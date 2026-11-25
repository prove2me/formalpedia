-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.macof_wd_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:11.084282+00:00
-- url     : https://prove2.me/submissions/5dc96b1e-f32c-439a-81a2-3dd6f57d07f4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_MacofFderivApplyContDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_macof_fderiv_apply_contDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) : ContDiffOn ℝ ∞ (wd n j g) U := by
  unfold wd
  exact ((macof_fderiv_apply_contDiffOn hU hg _).sub
    (contDiffOn_const.mul (macof_fderiv_apply_contDiffOn hU hg _))).div_const 2
end ReciprocityTheory.L2DbarEstimates.I
