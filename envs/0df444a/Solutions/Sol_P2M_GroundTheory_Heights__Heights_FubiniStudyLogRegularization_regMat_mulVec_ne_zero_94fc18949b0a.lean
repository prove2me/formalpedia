-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_regMat_mulVec_ne_zero_94fc18949b0a
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:05:05.591156+00:00
-- url     : https://prove2.me/submissions/53603cd5-7b78-404f-9e1b-d87a30c54352

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
variable {n : ℕ}
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {y : Fin n → ℂ}
    (hy : y ≠ 0) : regMat h u ε *ᵥ y ≠ 0 := by
  have key : ∀ (ε : ℝ), 0 ≤ ε → ∀ (u y : Fin n → ℂ), ∑ i, ‖(regMat h u ε *ᵥ y) i‖ ^ 2
      = ‖∑ j, u j * y j‖ ^ 2 + ε * ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 := by
    intro ε hε u y
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (regMat h u ε *ᵥ y) i.succ = ((√ε : ℝ) : ℂ) * ((h.matᵀ)⁻¹ *ᵥ y) i := by
      simp only [regMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hε]
  have hN2 : ∀ y : Fin n → ℂ, h.dualNorm y ^ 2 = ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 := fun y =>
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hpos : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < h.dualNorm y := by
    intro y hy
    apply Real.sqrt_pos.2
    have hu : IsUnit (h.matᵀ)⁻¹ := by
      rw [Matrix.isUnit_iff_isUnit_det]
      exact Matrix.isUnit_nonsing_inv_det _ (by rw [Matrix.det_transpose]; exact h.isUnit_det)
    have : (h.matᵀ)⁻¹ *ᵥ y ≠ 0 := by
      intro h0
      exact hy (Matrix.mulVec_injective_of_isUnit hu (by rw [h0, Matrix.mulVec_zero]))
    obtain ⟨i, hi⟩ := Function.ne_iff.1 this
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩
  have h0 : h.dualNorm 0 = 0 := by simp [HermNorm.dualNorm]
  intro hc
  have h1 := key ε hε.le u y
  rw [hc, ← hN2] at h1
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h1
  have := mul_pos hε (pow_pos (hpos y hy) 2)
  nlinarith [sq_nonneg ‖∑ j, u j * y j‖]



