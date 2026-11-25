-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.tl_twist_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:22.406934+00:00
-- url     : https://prove2.me/submissions/96a7b993-ef23-4846-b3ac-37f099604447

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tlFlr_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_lw_le

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
    (hε : 0 < ε) (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) :
    twist n g ph r ε = fun x => tlK (1 + Real.log (1 + ε ^ 2)) (lw n g ph r ε x) := by
  funext x
  have h := tl_lw_le n g ph r ε hr hε hbd x
  unfold twist eta xx tlK
  rw [tlFlr_eq _ _ _ (by norm_num) (by linarith)]
end ReciprocityTheory.L2DbarEstimates.I
