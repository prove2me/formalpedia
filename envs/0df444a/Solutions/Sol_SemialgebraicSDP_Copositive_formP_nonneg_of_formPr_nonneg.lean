-- Prove2me | solution 1 for SemialgebraicSDP.Copositive.formP_nonneg_of_formPr_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:19:47.381564+00:00
-- url     : https://prove2.me/submissions/1bb7defe-dc86-422b-b486-343d32660e63

import Mathlib
import Definitions.Def_SemialgebraicSDP_Copositive_Forms

open SemialgebraicSDP.Copositive MvPolynomial

theorem SemialgebraicSDP.Copositive.formP_nonneg_of_formPr_nonneg {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (r : ℕ)
    (h : ∀ z : Fin n → ℝ, 0 ≤ eval z (formPr M r)) :
    ∀ z : Fin n → ℝ, 0 ≤ eval z (formP M) := by
  classical
  intro z
  by_cases hz : ∀ j, z j = 0
  · simp [formP, hz]
  · obtain ⟨j, hj⟩ := not_forall.mp hz
    have hs : 0 < ∑ k, z k ^ 2 :=
      Finset.sum_pos' (fun k _ => sq_nonneg (z k)) ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero hj⟩
    have hp := h z
    simp only [formPr, eval_mul, eval_pow, eval_sum, eval_X] at hp
    exact nonneg_of_mul_nonneg_right hp (pow_pos hs r)

theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (r : ℕ) (h : ∀ z : Fin n → ℝ, 0 ≤ eval z (formPr M r)) :
    ∀ z : Fin n → ℝ, 0 ≤ eval z (formP M) :=
  SemialgebraicSDP.Copositive.formP_nonneg_of_formPr_nonneg M hM r h

#print axioms solution
