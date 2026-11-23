-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.tlK_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:42:44.482645+00:00
-- url     : https://prove2.me/submissions/e7b8fd7a-ee01-4707-b07d-58b54af670c9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tlFlr_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tlFlr_ge
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_eta_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (c : ℝ) : ContDiff ℝ ∞ (tlK c) := by
  have hf : ContDiff ℝ ∞ (fun t => tlFlr (19 / 20) (9 / 10) (c - t)) :=
    (tlFlr_contDiff _ _).comp (contDiff_const.sub contDiff_id)
  have hge : ∀ t, 9 / 10 ≤ tlFlr (19 / 20) (9 / 10) (c - t) := fun t => tlFlr_ge _ _ _ (by norm_num)
  have hl : ContDiff ℝ ∞ (fun t => Real.log (tlFlr (19 / 20) (9 / 10) (c - t))) :=
    hf.log fun t => by linarith [hge t]
  have hs : ContDiff ℝ ∞ (fun t => tlFlr (19 / 20) (9 / 10) (c - t) + Real.log (tlFlr (19 / 20) (9 / 10) (c - t))) :=
    hf.add hl
  exact (hs.log fun t => (tl_eta_pos _ (hge t)).ne').neg
end ReciprocityTheory.L2DbarEstimates.I
