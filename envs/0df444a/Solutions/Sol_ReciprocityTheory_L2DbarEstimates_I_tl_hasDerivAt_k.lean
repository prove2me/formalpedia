-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.tl_hasDerivAt_k
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:25:36.207612+00:00
-- url     : https://prove2.me/submissions/f944bcf7-f97d-441f-8f9f-f97cc85f5a00

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_eta_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add


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
open Filter Topology
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (c t : ℝ) (hs : 9 / 10 ≤ c - t) :
    HasDerivAt (fun t => -Real.log ((c - t) + Real.log (c - t))) (tlKp c t) t := by
  have hs0 : c - t ≠ 0 := by intro h; linarith
  have he := tl_eta_pos _ hs
  have hu : HasDerivAt (fun y => c - y) (-1) t := by simpa using (hasDerivAt_id t).const_sub c
  have hl := hu.log hs0
  have h2 := (hu.add hl).log he.ne'
  refine h2.neg.congr_deriv ?_
  unfold tlKp
  simp only [Pi.add_apply, Pi.div_apply]
  field_simp
  ring
end ReciprocityTheory.L2DbarEstimates.I
