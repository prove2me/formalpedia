-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.measurableSet_image_of_isLocalHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:06.339788+00:00
-- url     : https://prove2.me/submissions/6f26779b-e7a7-4952-a43c-d35f7c5793dc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_measurableSet_image_of_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart_cover

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
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (A : Set M) (hA : MeasurableSet A) : MeasurableSet (z '' A) := by
  obtain ⟨T, hTo, hTU, hTc⟩ := exists_chart_cover n z hz
  have h1 : A = ⋃ i, A ∩ T i := by rw [← Set.inter_iUnion, hTU, Set.inter_univ]
  rw [h1, Set.image_iUnion]
  refine MeasurableSet.iUnion (fun i => ?_)
  rcases hTc i with h | ⟨e, he, hTe⟩
  · simp [h]
  · exact measurableSet_image_of_chart n z e he _ (hA.inter (hTo i).measurableSet)
      (Set.inter_subset_right.trans hTe)
end ReciprocityTheory.L2DbarEstimates
