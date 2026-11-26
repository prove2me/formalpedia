-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiffOn_fsLogReg_1721299e7b32
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:07:14.423406+00:00
-- url     : https://prove2.me/submissions/cb263bb8-947c-46b4-a279-4385e51e2d02

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
theorem _root_.solution (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fsLogReg h u ε) {x | x ≠ 0} := by
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
  have e : ∀ y, GroundTheory.Heights₂.Heights.fsLogReg h u ε y = Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2) / ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2) / 2 := by
    intro y; unfold GroundTheory.Heights₂.Heights.fsLogReg; rw [hN2]
  refine ContDiffOn.congr ?_ (fun y _ => e y)
  have c1 : ContDiff ℝ ∞ (fun y : Fin n → ℂ => ‖∑ j, u j * y j‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j))
  have c2 : ContDiff ℝ ∞ (fun y : Fin n → ℂ => ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2) := by
    refine ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp ?_
    unfold Matrix.mulVec dotProduct
    exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)
  have hne : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 := by
    intro y hy; rw [← hN2]; exact pow_pos (hpos y hy) 2
  refine ContDiffOn.div_const (ContDiffOn.log (ContDiffOn.div ((c1.add (contDiff_const.mul c2)).contDiffOn) c2.contDiffOn (fun y hy => (hne y hy).ne')) fun y hy => ?_) 2
  have hp := hne y hy
  exact (div_pos (by nlinarith [mul_pos hε hp, sq_nonneg ‖∑ j, u j * y j‖]) hp).ne'



