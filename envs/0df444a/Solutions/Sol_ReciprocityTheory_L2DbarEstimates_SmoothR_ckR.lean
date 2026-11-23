-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.SmoothR.ckR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:22.494895+00:00
-- url     : https://prove2.me/submissions/bc96ed61-0025-411f-afaf-c6682dcff563

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
namespace SmoothR
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℝ)
    (hf : SmoothR n z f) : CkR n z k f := by
  intro e he
  exact contDiffOn_infty.1 (hf e he) k
end SmoothR
end ReciprocityTheory.L2DbarEstimates
