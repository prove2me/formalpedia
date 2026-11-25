-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_levi_log_dualNorm_nonneg_3e81938347b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:13.836085+00:00
-- url     : https://prove2.me/submissions/fa0bd2da-8573-4049-9cd1-40a9a132ef23

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogNormGradDensNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogNormGradDensNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogNormGradDensNonneg_log_fs_eq_std_2b91042fd6ef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_leviForm_log_fs_nonneg_4c974b17d733
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiffOn_log_dualNorm_a92d55d266bf
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LogNormGradDensNonneg
namespace GroundTheory.Heights₂.Heights.LogNormGradDensNonneg
theorem _root_.solution {n : ℕ} (h : HermNorm n) {x : Fin n → ℂ} (hx : x ≠ 0)
    (w : Fin n → ℂ) : 0 ≤ levi (fun x => Real.log (h.dualNorm x)) x w := by
  set T : (Fin n → ℂ) → Fin n → ℂ := fun x => (h.matᵀ)⁻¹ *ᵥ x with hT
  set F : (Fin n → ℂ) → ℝ := fun z => Real.log ((ReciprocityTheory.ChartRestriction.G.Geo.fsMetric (Fin n)).ρ z) with hF
  have hTx : T x ≠ 0 := by
    intro h0
    have : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact h.isUnit_det),
        Matrix.one_mulVec]
    exact hx (by rw [← this]; simp only [hT] at h0; rw [h0, Matrix.mulVec_zero])
  have hcomp : (fun x => Real.log (h.dualNorm x)) = F ∘ T := by
    funext z
    simp [hF, hT, ReciprocityTheory.ChartRestriction.G.Geo.fsMetric, HermNorm.dualNorm, EuclideanSpace.norm_eq]
  have hTa : AnalyticAt ℂ T x := by
    have := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h.matᵀ)⁻¹)).analyticAt x
    simp only [LinearMap.coe_toContinuousLinearMap'] at this
    convert this using 1
    funext z
    rw [Matrix.mulVecLin_apply]
  have hFc : ContDiffAt ℝ 2 F (T x) := by
    rw [hF, log_fs_eq_std]
    exact (((contDiffOn_log_dualNorm (HermNorm.std n)).contDiffAt
      (isOpen_compl_singleton.mem_nhds hTx)).of_le (WithTop.coe_le_coe.mpr le_top))
  rw [hcomp, levi_comp w hTa hFc]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hTx _
end GroundTheory.Heights₂.Heights.LogNormGradDensNonneg
