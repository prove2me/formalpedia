-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.injOn_source_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:25.563825+00:00
-- url     : https://prove2.me/submissions/032a7521-ea07-443f-ba22-8b5e93d1ea0b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M]
omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) (z : M → V n) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) : InjOn z e.source := by
  intro a ha b hb hab
  exact e.injOn ha hb (by rw [← he ha, ← he hb]; exact hab)
end ReciprocityTheory.L2DbarEstimates
