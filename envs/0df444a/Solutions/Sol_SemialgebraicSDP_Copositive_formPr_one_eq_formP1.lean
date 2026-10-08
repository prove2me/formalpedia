-- Prove2me | solution 1 for SemialgebraicSDP.Copositive.formPr_one_eq_formP1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:18:46.721286+00:00
-- url     : https://prove2.me/submissions/ce7be3cc-76e3-45fe-a6f2-c538f861c435

import Mathlib
import Definitions.Def_SemialgebraicSDP_Copositive_Forms

open SemialgebraicSDP.Copositive MvPolynomial

theorem SemialgebraicSDP.Copositive.formPr_one_eq_formP1 {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    formPr M 1 = formP1 M := by
  classical
  simp only [formPr, pow_one, formP, formP1]
  rw [mul_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    formPr M 1 = formP1 M :=
  SemialgebraicSDP.Copositive.formPr_one_eq_formP1 M hM

