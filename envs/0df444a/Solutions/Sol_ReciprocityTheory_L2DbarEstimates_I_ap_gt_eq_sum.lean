-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_gt_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:49.358097+00:00
-- url     : https://prove2.me/submissions/42adc84b-8341-46c5-83ac-5dd95b4620ce

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (c : M → ℂ) (W : M → Set M) (hS : (zeroSet n g).Finite) (y : M) :
    gt n z g c W y = ∑ p ∈ hS.toFinset, (W p).indicator (fun y => c p * jac n z g y) y := by
  unfold gt
  exact finsum_mem_eq_finite_toFinset_sum _ hS
end ReciprocityTheory.L2DbarEstimates.I
