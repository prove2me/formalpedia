-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P04.optical_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:08:11.272185+00:00
-- url     : https://prove2.me/submissions/d4baf33e-4809-47f2-8ca5-185b7716e07b

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P04
noncomputable section

open QAlgorithms.Papers.Independent.Support21.P04

theorem solution (S : Matrix.unitaryGroup (Fin 2) ℂ) :
    transitionMatrix S - (transitionMatrix S).conjTranspose =
      (-2 * (Real.pi : ℂ) * Complex.I) •
        (transitionMatrix S * (transitionMatrix S).conjTranspose) := by
  have hU : (S : Matrix (Fin 2) (Fin 2) ℂ) * (S : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp S.2
  set U : Matrix (Fin 2) (Fin 2) ℂ := (S : Matrix (Fin 2) (Fin 2) ℂ) with hUdef
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hc
  have hc0 : c ≠ 0 := by
    simp [hc, Real.pi_ne_zero, Complex.I_ne_zero]
  have hstar : star (c⁻¹) = -c⁻¹ := by
    rw [star_inv₀]
    have : star c = -c := by
      simp [hc, Complex.conj_ofReal]
    rw [this, inv_neg]
  unfold transitionMatrix
  rw [← hUdef, ← hc]
  rw [Matrix.conjTranspose_smul, hstar, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
  have e : (1 - U) * (1 - U.conjTranspose) = (1 - U) + (1 - U.conjTranspose) := by
    rw [sub_mul, mul_sub, mul_sub, hU]; simp; abel
  rw [e]
  have : -2 * (Real.pi : ℂ) * Complex.I * c⁻¹ * -c⁻¹ = c⁻¹ := by
    rw [show -2 * (Real.pi : ℂ) * Complex.I = -c by rw [hc]; ring]
    field_simp
  rw [this, neg_smul, sub_neg_eq_add, smul_add]
