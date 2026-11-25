-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.tl_lw_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:41:31.445335+00:00
-- url     : https://prove2.me/submissions/39a6f7d5-7266-4a24-a11e-a998562e979e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_ev_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_ev_le_one

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
theorem _root_.solution {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (hr : 0 < r)
    (hε : 0 < ε) (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) (x : M) :
    lw n g ph r ε x ≤ Real.log (1 + ε ^ 2) := by
  unfold lw
  have h0 := tl_ev_nonneg n g ph r x
  have h1 := tl_ev_le_one n g ph r hr hbd x
  exact Real.log_le_log (by positivity) (by linarith)
end ReciprocityTheory.L2DbarEstimates.I
