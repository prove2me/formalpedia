-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.logCutoff_eventuallyEq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:10.355652+00:00
-- url     : https://prove2.me/submissions/352ccc89-3767-44a1-86b0-0528325f6f65

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_extCh_of_two_le

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
    (hFc : ContinuousAt F z) (hz : F z = 0) : extCut F k =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
  have hball : Metric.ball (0 : ℂ) (Real.exp (-k)) ∈ 𝓝 (F z) := by
    rw [hz]
    exact Metric.ball_mem_nhds _ (Real.exp_pos _)
  filter_upwards [hFc.preimage_mem_nhds hball] with w hw
  have hw' : ‖F w‖ < Real.exp (-k) := by simpa using hw
  unfold extCut
  split_ifs with h0
  · rfl
  · apply extCh_of_two_le
    have hpos : 0 < ‖F w‖ := norm_pos_iff.2 h0
    have hlog : Real.log ‖F w‖ < -k := by
      have := Real.log_lt_log hpos hw'
      rwa [Real.log_exp] at this
    rw [le_div_iff₀ hk, Real.log_pow]
    push_cast
    linarith
end ReciprocityTheory.L2DbarEstimates.C
