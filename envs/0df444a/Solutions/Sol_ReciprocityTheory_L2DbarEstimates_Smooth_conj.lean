-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Smooth.conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:03.49143+00:00
-- url     : https://prove2.me/submissions/0b68f5fe-b45b-47c9-93d3-c6cac80deca9

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Smooth n z f) :
    Smooth n z (fun x => (starRingEnd ℂ) (f x)) := by
  intro e he
  have h1 := Complex.conjCLE.contDiff.comp_contDiffOn (hf e he)
  refine h1.congr (fun w _ => ?_)
  simp
end Smooth
end ReciprocityTheory.L2DbarEstimates
