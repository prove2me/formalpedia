-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_smul_28823a5d6dcc
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:05:06.850877+00:00
-- url     : https://prove2.me/submissions/5448aa39-fbbf-4230-ba89-fa10581627c5

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
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) {t : ℂ} (ht : t ≠ 0)
    (y : Fin n → ℂ) : fsLogReg h u ε (t • y) = fsLogReg h u ε y := by
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
  unfold GroundTheory.Heights₂.Heights.fsLogReg
  have hs : h.dualNorm (t • y) = ‖t‖ * h.dualNorm y := by
    unfold HermNorm.dualNorm
    rw [Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hu : ∑ j, u j * (t • y) j = t * ∑ j, u j * y j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by simp; ring
  rw [hs, hu, norm_mul]
  have ht' : ‖t‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ht)
  congr 2
  rw [mul_pow, mul_pow, show ‖t‖ ^ 2 * ‖∑ j, u j * y j‖ ^ 2 + ε * (‖t‖ ^ 2 * h.dualNorm y ^ 2)
      = ‖t‖ ^ 2 * (‖∑ j, u j * y j‖ ^ 2 + ε * h.dualNorm y ^ 2) by ring, mul_div_mul_left _ _ ht']



