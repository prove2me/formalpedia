-- Prove2me | solution 1 for SemialgebraicSDP.Copositive.formPr_sos_succ
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:19:45.589347+00:00
-- url     : https://prove2.me/submissions/fffd2680-5599-478a-9c09-1beb3f9cda51

import Mathlib
import Definitions.Def_SemialgebraicSDP_Copositive_Forms

open SemialgebraicSDP.Copositive MvPolynomial

theorem SemialgebraicSDP.Copositive.formPr_sos_succ {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (i : ℕ)
    (h : IsSumSq (formPr M i)) : IsSumSq (formPr M (i + 1)) := by
  classical
  have hs : IsSumSq (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) :=
    IsSumSq.sum_sq _ _
  have he : formPr M (i + 1) = (∑ j : Fin n, X j ^ 2) * formPr M i := by
    simp only [formPr, pow_succ]
    ring
  rw [he]
  exact hs.mul h

theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (i : ℕ)
    (h : IsSumSq (formPr M i)) : IsSumSq (formPr M (i + 1)) :=
  SemialgebraicSDP.Copositive.formPr_sos_succ M hM i h

#print axioms solution
