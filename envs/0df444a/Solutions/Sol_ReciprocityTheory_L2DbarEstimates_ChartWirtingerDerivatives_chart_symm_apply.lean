-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.chart_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:29.396898+00:00
-- url     : https://prove2.me/submissions/b3f18632-b0ff-44ec-8bdd-7e0b8a8d9161

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M) (hx : x ∈ e.source) :
    e.symm (z x) = x := by
  rw [he hx]
  exact e.left_inv hx
end ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
