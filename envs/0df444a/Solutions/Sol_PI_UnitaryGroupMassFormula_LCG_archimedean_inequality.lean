-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.archimedean_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:04:47.325642+00:00
-- url     : https://prove2.me/submissions/229292b4-831f-41e0-85fd-1bebd128a2c6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_DetMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchIneq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_determinant_monotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution : ArchIneq := by
  intro n k A C D κ hκ hA hker
  have hGdet := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k D 1 1 zero_le_one (by intro w; simp)).1
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin k) (Fin k) ℂ, G = Dᴴ * D := ⟨_, rfl⟩
  rw [← hG] at hGdet ⊢
  have hGh : Gᴴ = G := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have him : G.det.im = 0 := by
    have hstar : star G.det = G.det := by rw [← Matrix.det_conjTranspose, hGh]
    have h1 := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at h1
    linarith
  by_cases hg : G.det = 0
  · rw [hg, Complex.zero_re, mul_zero]
    exact mul_nonneg (pow_nonneg hκ k) (sq_nonneg _)
  · have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hg
    obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin k) ℂ, X = D * G⁻¹ * Dᴴ * C := ⟨_, rfl⟩
    have hAP : A * (D * G⁻¹ * Dᴴ) = A := by
      apply Matrix.ext_of_mulVec_single
      intro j
      have h1 : Dᴴ *ᵥ ((Pi.single j 1 : Fin n → ℂ) - (D * G⁻¹ * Dᴴ) *ᵥ Pi.single j 1) = 0 := by
        have h3 : Dᴴ * (D * G⁻¹ * Dᴴ) = G * G⁻¹ * Dᴴ := by
          rw [hG]
          simp only [Matrix.mul_assoc]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, h3, Matrix.mul_nonsing_inv G hGu, Matrix.one_mul, sub_self]
      have h2 := hker _ h1
      rw [Matrix.mulVec_sub, sub_eq_zero] at h2
      rw [← Matrix.mulVec_mulVec, ← h2]
    have hAX : A * X = A * C := by
      rw [hX, ← Matrix.mul_assoc, hAP]
    have hdm := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k X A κ hκ hA).2
    rw [hAX] at hdm
    have hXh : Xᴴ = Cᴴ * D * G⁻¹ * Dᴴ := by
      rw [hX]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv,
        hGh, Matrix.mul_assoc]
    have hXX : Xᴴ * X = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by
      rw [hXh, hX]
      have hGG : G⁻¹ * (Dᴴ * D) = 1 := by
        rw [← hG]
        exact Matrix.nonsing_inv_mul G hGu
      calc Cᴴ * D * G⁻¹ * Dᴴ * (D * G⁻¹ * Dᴴ * C) = Cᴴ * D * (G⁻¹ * (Dᴴ * D)) * G⁻¹ * (Dᴴ * C) := by
            simp only [Matrix.mul_assoc]
        _ = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by rw [hGG, Matrix.mul_one]
    have hdetX : (Xᴴ * X).det = star (Dᴴ * C).det * (Dᴴ * C).det / G.det := by
      have hCD : Cᴴ * D = (Dᴴ * C)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hXX, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hCD,
        Matrix.det_conjTranspose]
      ring
    have h5 : (Xᴴ * X).det * G.det = star (Dᴴ * C).det * (Dᴴ * C).det := by
      rw [hdetX, div_mul_cancel₀ _ hg]
    have hval : (Xᴴ * X).det.re * G.det.re = ‖(Dᴴ * C).det‖ ^ 2 := by
      have h6 := congrArg Complex.re h5
      rw [Complex.mul_re, him, mul_zero, sub_zero] at h6
      rw [h6, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    calc (((A * C)ᴴ * (A * C)).det).re * G.det.re ≤ κ ^ k * (Xᴴ * X).det.re * G.det.re :=
          mul_le_mul_of_nonneg_right hdm hGdet
      _ = κ ^ k * ‖(Dᴴ * C).det‖ ^ 2 := by rw [mul_assoc, hval]
end PI.UnitaryGroupMassFormula.LCG
