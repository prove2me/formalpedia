-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Smooth.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:45.036521+00:00
-- url     : https://prove2.me/submissions/797539ea-7ce7-4f4b-b844-03d615527132

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
namespace Smooth
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Smooth n z f) (hg : Smooth n z g) :
    Smooth n z (fun x => f x * g x) := by
  exact fun e he => (hf e he).mul (hg e he)
end Smooth
end ReciprocityTheory.L2DbarEstimates
