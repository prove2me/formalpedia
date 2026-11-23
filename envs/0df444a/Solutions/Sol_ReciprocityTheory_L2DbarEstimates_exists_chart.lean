-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:39.459117+00:00
-- url     : https://prove2.me/submissions/812946b1-de94-474f-9a7f-ee16ccbcb49b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (x : M) :
    ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := by
  obtain ⟨e, hx, he⟩ := hz x
  exact ⟨e, fun y _ => congrFun he y, hx⟩
end ReciprocityTheory.L2DbarEstimates
