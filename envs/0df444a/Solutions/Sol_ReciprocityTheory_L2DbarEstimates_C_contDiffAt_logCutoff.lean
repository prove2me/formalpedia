-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.contDiffAt_logCutoff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:22.052748+00:00
-- url     : https://prove2.me/submissions/d4b20d08-5aec-420d-b996-5f5f8002004e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_extCh_contDiff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_logCutoff_eventuallyEq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n}
    (hF : ContDiffAt ℝ ∞ F z) : ContDiffAt ℝ ∞ (extCut F k) z := by
  by_cases h0 : F z = 0
  · exact contDiffAt_const.congr_of_eventuallyEq
      (logCutoff_eventuallyEq_zero hk hF.continuousAt h0)
  · have hin : ContDiffAt ℝ ∞ (fun w => -Real.log (‖F w‖ ^ 2) / k) z := by
      have h2 : ContDiffAt ℝ ∞ (fun w => ‖F w‖ ^ 2) z := hF.norm_sq ℝ
      have hne : ‖F z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 h0)
      exact ((h2.log hne).neg).div_const k
    have hcomp : ContDiffAt ℝ ∞ (fun w => extCh (-Real.log (‖F w‖ ^ 2) / k)) z :=
      extCh_contDiff.contDiffAt.comp z hin
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hF.continuousAt.eventually_ne h0] with w hw
    simp [extCut, hw]
end ReciprocityTheory.L2DbarEstimates.C
