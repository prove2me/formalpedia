-- Prove2me | solution 1 for ShiBQP.polyBound_three_phase_compose
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T09:13:37.35923+00:00
-- url     : https://prove2.me/submissions/f39a3b32-d92e-47af-904c-d3c3a0fd5004

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

/-!
# The arithmetic half of `PolyTimeComputable` composition

This is the time-bound obligation that falls out of composing two `Turing.FinTM2`
machines `M₁` (computing `f`, in `p₁ (|a|)` steps) and `M₂` (computing `g`, in
`p₂ (|f a|)` steps) into a single machine for `g ∘ f`.

Why this shape.  In the composed machine the run splits into three phases:

* run `M₁` on `a`                                  -- `p₁.eval n` steps, `n = |a|`;
* move `f a` from `M₁`'s output stack to `M₂`'s
  input stack, via one scratch stack (two passes,
  because popping reverses)                        -- `2 * m + d` steps, `m = |f a|`;
* run `M₂` on `f a`                                -- `p₂.eval m` steps.

So the total is `p₁.eval n + (2 * m + d) + p₂.eval m`, where the *data-dependent*
quantity `m = |f a|` is not under our control.  The only handle on `m` is a
stack-growth bound for `M₁`: a single `Turing.TM2.Stmt` is a finite tree, so it
performs at most `c` pushes, where `c` is the maximum push-count over the
(finitely many) labels of `M₁`.  Hence

  `m ≤ n + c * p₁.eval n`,

i.e. `m` is bounded by a *polynomial in `n`*, namely `r := X + C c * p₁`, but only
by an inequality -- never an equation.  That forces exactly two ingredients:

* `Polynomial.comp`, to turn `p₂` evaluated at `r.eval n` into a polynomial in `n`
  (`Polynomial.eval_comp`, Mathlib/Algebra/Polynomial/Eval/Defs.lean:628);
* monotonicity of `Polynomial.eval` over `ℕ`, to pass from `p₂.eval m` to
  `p₂.eval (r.eval n)`.  Mathlib has **no** such lemma (searched
  `Mathlib/Algebra/Polynomial/`: no `eval_mono`, `eval_le_eval_of_le`,
  `Monotone (eval · p)`), so it is proved here as `shiTm2_eval_le_eval_of_le`.

Quantifying over `m` with the hypothesis `m ≤ n + c * p₁.eval n`, rather than
substituting a concrete `|f a|`, is what makes the statement usable: the machine
construction supplies that inequality and nothing more.
-/

/-- Evaluation of a polynomial with natural-number coefficients is monotone in the
argument.  (Absent from Mathlib; `Polynomial.eval_comp` is the only composition
lemma available, and it does not give this.) -/
private theorem shiTm2_eval_le_eval_of_le (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) :
    Polynomial.eval m p ≤ Polynomial.eval n p := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add hr hs
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul (Nat.le_refl a) (Nat.pow_le_pow_left h k)

/-- **The time bound for machine composition.**

Given polynomial running bounds `p₁` for the first machine and `p₂` for the second,
a stack-growth constant `c` for the first machine and a constant copy-phase overhead
`d`, the total cost of the composed machine is bounded by a single polynomial in the
length of the original input -- uniformly in the intermediate length `m`, subject only
to the bound `m ≤ n + c * p₁.eval n` that the first machine's runtime provides.

The witness is
`q = p₁ + (C 2 * r + C d) + p₂.comp r`  with  `r = X + C c * p₁`. -/
theorem solution (p₁ p₂ : Polynomial ℕ) (c d : ℕ) :
    ∃ q : Polynomial ℕ, ∀ n m : ℕ, m ≤ n + c * Polynomial.eval n p₁ →
      Polynomial.eval n p₁ + (2 * m + d) + Polynomial.eval m p₂ ≤ Polynomial.eval n q := by
  refine ⟨p₁ + (Polynomial.C 2 * (Polynomial.X + Polynomial.C c * p₁) + Polynomial.C d)
      + p₂.comp (Polynomial.X + Polynomial.C c * p₁), ?_⟩
  intro n m hm
  have h2 : 2 * m + d ≤ 2 * (n + c * Polynomial.eval n p₁) + d :=
    Nat.add_le_add (Nat.mul_le_mul (Nat.le_refl 2) hm) (Nat.le_refl d)
  have h3 : Polynomial.eval m p₂ ≤ Polynomial.eval (n + c * Polynomial.eval n p₁) p₂ :=
    shiTm2_eval_le_eval_of_le p₂ hm
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C,
    Polynomial.eval_X]
  exact Nat.add_le_add (Nat.add_le_add_left h2 _) h3
