-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.cutP_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:48.860998+00:00
-- url     : https://prove2.me/submissions/5ab80bb3-ee05-4ec5-af57-6863d3918d76

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_cutL_nonneg

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
open scoped ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {k m : ℝ} (hk : 1 ≤ k) (hm : 0 ≤ m) :
    cutP (Real.exp (-2 * k)) m ≤ (m + 2) ^ 2 / 2 * k ^ 2 := by
  have hε : 0 < Real.exp (-2 * k) := Real.exp_pos _
  have hε1 : Real.exp (-2 * k) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hLe : cutL (Real.exp (-2 * k)) m = Real.log (m + Real.exp (-2 * k)) + 2 * k := by
    unfold cutL
    rw [Real.log_exp]
    ring
  have hlog : Real.log (m + Real.exp (-2 * k)) ≤ m + Real.exp (-2 * k) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hL0 := cutL_nonneg hε hm
  have hLup : cutL (Real.exp (-2 * k)) m ≤ (m + 2) * k := by
    rw [hLe]
    nlinarith
  unfold cutP
  nlinarith [mul_le_mul hLup hLup hL0 (by positivity : (0 : ℝ) ≤ (m + 2) * k)]
end ReciprocityTheory.L2DbarEstimates.C
