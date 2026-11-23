-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Smooth.ck
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:30.092059+00:00
-- url     : https://prove2.me/submissions/b9cae0f2-9118-4cae-8ef0-40d373637c6e

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
namespace Smooth
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℂ)
    (hf : Smooth n z f) : Ck n z k f := by
  intro e he
  exact contDiffOn_infty.1 (hf e he) k
end Smooth
end ReciprocityTheory.L2DbarEstimates
