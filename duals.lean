/- © 2021 Derik Kauffman. Licensed under the MIT license. -/

import tactic.induction
import tactic.linarith

/-! # Dual numbers
The [__dual numbers__](https://en.wikipedia.org/wiki/Dual_number)
are a number system consisting of pairs of numbers, `a + bε`, where `ε² = 0`.
I'll refer to `a` as the _real part_ and `b` as the _infinitesimal part_.
I'm using rational numbers for the coefficients `a` and `b`, since reals are
uncomputable in Lean.
-/
structure dual := (a b : ℚ)

namespace dual
instance : has_repr dual :=
	{repr := (λd : dual, to_string d.a ++ " + " ++ to_string d.b ++ "ε")}

def of_rat (q : ℚ) : dual := mk q 0

@[simp] lemma eq_components_eq (p q : dual) :
	p = q ↔ p.a = q.a ∧ p.b = q.b :=
begin
	induction' p,
	induction' q,
	simp,
end

-- We define basic operations on the duals, and register them to take advantage
-- of standard symbolic notation:
@[simp] def add (p q : dual) := mk (p.a + q.a) (p.b + q.b)
instance : has_add dual := ⟨add⟩

@[simp] lemma add_eq (p q : dual) : 
  p + q = { a := p.a + q.a, b := p.b + q.b } := by refl


@[simp] def neg (p : dual) := mk (-p.a) (-p.b)
instance : has_neg dual := ⟨neg⟩

@[simp] lemma neg_eq (p : dual) : 
  -p = { a := -p.a, b := -p.b } := by refl


-- The multiplication rule captures the fact that ε² = 0:
@[simp] def mul (p q : dual) := mk (p.a * q.a) (p.a * q.b + p.b * q.a)
instance : has_mul dual := ⟨mul⟩

@[simp] lemma mul_eq (p q : dual) : 
  p * q = { a := p.a * q.a, b := p.a * q.b + p.b * q.a } := by refl


@[simp] def zero : dual := mk 0 0
instance : has_zero dual := ⟨zero⟩

@[simp] def one : dual := mk 1 0
instance : has_one dual := ⟨one⟩


-- Here we prove that the dual numbers form a commutative ring:
instance dual : comm_ring dual :={
	add       := add,
  add_assoc := by simp [add_assoc],
	zero      := zero,
	zero_add  := by intro a; induction' a; simp,
	add_zero  := by intro a; induction' a; simp,
	neg       := neg,
	mul       := mul,
	add_left_neg  := by finish,
	add_comm      := by intros; simp [add_comm],
	mul_assoc     := by intros; simp [mul_assoc]; ring,
	one           := one,
	one_mul       := by intro a; induction' a; simp,
	mul_one       := by intro a; induction' a; simp,
	left_distrib  := by intros; simp [left_distrib]; ring,
	right_distrib := by intros; simp [right_distrib]; ring,
	mul_comm      := by intros; simp [mul_comm]; ring
}

-- For convenience, we define `ε` as the unit infinitesimal
def ε : dual := mk 0 1

-- This allows us to write dual numbers quite naturally:
#eval 3 + 4*ε  -- 3 + 4ε
#eval (1 + ε) * ε  -- 0 + 1ε

-- We can define a division on the ring as the inverse of multiplication:
def div (x y : dual) := mk (x.a / y.a) ((x.b * y.a - x.a * y.b)/(y.a^2))
instance : has_div dual := ⟨div⟩
-- Look familiar? This is just the quotient rule.

/- Technically 1/ε should be undefined, but our division rule gives it a value
of 0 (just like how we define 1/0 ≡ 0 for rationals) -/
#eval 1/ε  -- 0 + 0ε

-- However, there is no true inverse to ε (no dual number x such that x * ε = 1):
lemma no_inv_of_ε : ∀x : dual, x * ε ≠ 1 :=
begin
	intro x,
	induction' x,
	rw ε,

	calc (mk a b) * (mk 0 1) = mk 0 a : by simp
	... ≠ one : by finish,
end


/- We can use the dual numbers to implement a basic automatic differentiation
system! Given any function defined in terms of addition, subtraction,
multiplication, and division, we can find its derivative at a point x
by plugging in x + ε and taking the infinitesimal part of the result:
-/
def poly := λx : dual, x^8 + 4*x^5 - 2*x^3 + x - 3
def ratfunc := λx : dual, (x^3 - 2*x^2 - 4*x + 5) / (2*x + 3)

def derivative (f : dual → dual) (x : ℚ) := (f (mk x 1)).b
#eval derivative poly (-2)  -- -727
#eval derivative ratfunc 3  -- 95/81

end dual
