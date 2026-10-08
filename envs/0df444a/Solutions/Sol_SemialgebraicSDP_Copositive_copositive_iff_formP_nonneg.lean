-- Prove2me | solution 1 for SemialgebraicSDP.Copositive.copositive_iff_formP_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:48:55.881985+00:00
-- url     : https://prove2.me/submissions/1eb9f3e6-a7ba-401c-897b-27a688859b9f

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_SemialgebraicSDP_Copositive_Forms

open SemialgebraicSDP.Copositive MvPolynomial

private theorem eval_form {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    eval z (formP M) = MurtyKabadi.Reduction.Q M (fun i => z i ^ 2) := by
  simp only [formP, eval_sum, eval_mul, eval_C, eval_pow, eval_X,
    MurtyKabadi.Reduction.Q, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    MurtyKabadi.Reduction.Copositive M ↔ ∀ z : Fin n → ℝ, 0 ≤ eval z (formP M) := by
  constructor
  · intro h z
    rw [eval_form]
    exact h _ (fun i => sq_nonneg (z i))
  · intro h x hx
    have hs : (fun i => (Real.sqrt (x i)) ^ 2) = x := by
      funext i
      exact Real.sq_sqrt (hx i)
    have hh := h (fun i => Real.sqrt (x i))
    rw [eval_form, hs] at hh
    exact hh

#print axioms solution
