-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Krd.CP.cay_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:51.8128+00:00
-- url     : https://prove2.me/submissions/cb9bda3a-8c9e-418f-b749-37220bc02527

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_CayleyTransform_DenseCP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.CP
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.SiegelWeilFormula.Krd.CP
theorem _root_.solution {J h : Matrix ι ι ℂ} (hh : hᴴ * J * h = J) (hu : IsUnit (1 + h).det) :
    ∃ Y : Matrix ι ι ℂ, Yᴴ * J + J * Y = 0 ∧ IsUnit (1 - Y).det ∧ (1 + Y) * (1 - Y)⁻¹ = h := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix ι ι ℂ, P = 1 + h := ⟨_, rfl⟩
  rw [← hP] at hu
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  obtain ⟨Y, hYd⟩ : ∃ Y : Matrix ι ι ℂ, Y = (h - 1) * P⁻¹ := ⟨_, rfl⟩
  have e1 : 1 - Y = (2 : ℂ) • P⁻¹ := by
    calc 1 - Y = P * P⁻¹ - (h - 1) * P⁻¹ := by rw [hPi, hYd]
      _ = (P - (h - 1)) * P⁻¹ := by rw [← Matrix.sub_mul]
      _ = ((2 : ℂ) • 1) * P⁻¹ := by rw [hP, two_smul]; congr 1; abel
      _ = (2 : ℂ) • P⁻¹ := by rw [Matrix.smul_mul, Matrix.one_mul]
  have e2 : 1 + Y = (2 : ℂ) • (h * P⁻¹) := by
    calc 1 + Y = P * P⁻¹ + (h - 1) * P⁻¹ := by rw [hPi, hYd]
      _ = (P + (h - 1)) * P⁻¹ := by rw [← Matrix.add_mul]
      _ = ((2 : ℂ) • h) * P⁻¹ := by rw [hP, two_smul]; congr 1; abel
      _ = (2 : ℂ) • (h * P⁻¹) := by rw [Matrix.smul_mul]
  have hdet : IsUnit (1 - Y).det := by
    rw [e1, Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 two_ne_zero)).mul ((Matrix.isUnit_nonsing_inv_det_iff).2 hu)
  refine ⟨Y, ?_, hdet, ?_⟩
  · have hPc : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPi, conjTranspose_one]
    have eY : Y * P = h - 1 := by rw [hYd, Matrix.mul_assoc, hiP, Matrix.mul_one]
    have eYh : Pᴴ * Yᴴ = (h - 1)ᴴ := by rw [← conjTranspose_mul, eY]
    have key : Pᴴ * (Yᴴ * J + J * Y) * P = 0 := by
      have e3 : Pᴴ * (Yᴴ * J + J * Y) * P = (Pᴴ * Yᴴ) * J * P + Pᴴ * J * (Y * P) := by noncomm_ring
      rw [e3, eYh, eY, hP, conjTranspose_sub, conjTranspose_add, conjTranspose_one]
      have e4 : (hᴴ - 1) * J * (1 + h) + (1 + hᴴ) * J * (h - 1) = (2 : ℂ) • (hᴴ * J * h - J) := by
        rw [two_smul]; noncomm_ring
      rw [e4, hh, sub_self, smul_zero]
    calc Yᴴ * J + J * Y = ((P⁻¹)ᴴ * Pᴴ) * (Yᴴ * J + J * Y) * (P * P⁻¹) := by
          rw [hPc, hPi, Matrix.one_mul, Matrix.mul_one]
      _ = (P⁻¹)ᴴ * (Pᴴ * (Yᴴ * J + J * Y) * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [key, Matrix.mul_zero, Matrix.zero_mul]
  · rw [e1, e2]
    have hinv : ((2 : ℂ) • P⁻¹)⁻¹ = (2 : ℂ)⁻¹ • P := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul, hPi]
    rw [hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul, Matrix.mul_assoc, hiP,
      Matrix.mul_one]
end PositivityTheory.SiegelWeilFormula.Krd.CP
