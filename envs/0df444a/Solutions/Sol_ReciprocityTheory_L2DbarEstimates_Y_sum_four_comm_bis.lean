-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.sum_four_comm_bis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:42:18.725166+00:00
-- url     : https://prove2.me/submissions/0133c454-fb5c-49e6-9823-46d4a77e2814

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (T : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ j, ∑ k, T a b j k = ∑ j, ∑ k, ∑ b, ∑ a, T a b j k := by
  calc ∑ a, ∑ b, ∑ j, ∑ k, T a b j k = ∑ a, ∑ j, ∑ k, ∑ b, T a b j k := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_; rw [Finset.sum_comm]
    _ = ∑ j, ∑ k, ∑ b, ∑ a, T a b j k := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => ?_; rw [Finset.sum_comm]
end ReciprocityTheory.L2DbarEstimates.Y
