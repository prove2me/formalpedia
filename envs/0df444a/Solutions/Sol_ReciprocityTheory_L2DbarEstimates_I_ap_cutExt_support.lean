-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_cutExt_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:05.255339+00:00
-- url     : https://prove2.me/submissions/c9cee796-696b-4313-8673-fa85c6535ec0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_gt_eq_sum

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
open scoped ENNReal ContDiff Classical
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (χ : ℝ → ℝ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (x : M) (hx : x ∉ ⋃ p ∈ hS.toFinset, closure (W p)) :
    cutExt n z g ph r c W χ ε x = 0 := by
  simp only [cutExt, ap_gt_eq_sum n z g c W hS x]
  rw [Finset.sum_eq_zero, mul_zero]
  intro p hp
  have : x ∉ W p := fun h => hx (Set.mem_biUnion hp (subset_closure h))
  simp [this]
end ReciprocityTheory.L2DbarEstimates.I
