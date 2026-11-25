-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.macof_wdb_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:16:15.784313+00:00
-- url     : https://prove2.me/submissions/060367fe-c925-4a7a-a895-7466be54540c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_MacofFderivApplyContDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_macof_fderiv_apply_contDiffOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


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
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) : ContDiffOn ℝ ∞ (wdb n j g) U := by
  unfold wdb
  exact ((macof_fderiv_apply_contDiffOn hU hg _).add
    (contDiffOn_const.mul (macof_fderiv_apply_contDiffOn hU hg _))).div_const 2
end ReciprocityTheory.L2DbarEstimates.I
