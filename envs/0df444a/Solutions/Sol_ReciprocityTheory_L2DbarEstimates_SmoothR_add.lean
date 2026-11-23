-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.SmoothR.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:28.606932+00:00
-- url     : https://prove2.me/submissions/1850e5af-cca2-4a33-ac47-39383956f898

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add

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
namespace SmoothR
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℝ) (hf : SmoothR n z f) (hg : SmoothR n z g) :
    SmoothR n z (fun x => f x + g x) := by
  have h1 := Smooth.add n z _ _ hf hg
  unfold SmoothR
  simpa using h1
end SmoothR
end ReciprocityTheory.L2DbarEstimates
