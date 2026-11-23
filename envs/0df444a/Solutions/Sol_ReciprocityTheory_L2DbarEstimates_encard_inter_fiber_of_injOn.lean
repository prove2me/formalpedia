-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.encard_inter_fiber_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:39.15566+00:00
-- url     : https://prove2.me/submissions/944da239-1d9c-4c7f-9e8c-4f89d985942e

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
theorem _root_.solution (n : ℕ) (z : M → V n) (S : Set M) (hS : InjOn z S) (y : V n) :
    (((S ∩ z ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) = (z '' S).indicator 1 y := by
  by_cases hy : y ∈ z '' S
  · obtain ⟨a, ha, rfl⟩ := hy
    have h1 : S ∩ z ⁻¹' {z a} = {a} := by
      ext b
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hb, hba⟩; exact hS hb ha hba
      · rintro rfl; exact ⟨ha, rfl⟩
    rw [h1, Set.encard_singleton]
    simp [Set.indicator_apply, Set.mem_image_of_mem z ha]
  · have h1 : S ∩ z ⁻¹' {y} = ∅ := by
      ext b
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro hb hby
      exact hy ⟨b, hb, hby⟩
    rw [h1, Set.encard_empty]
    simp [Set.indicator_apply, hy]
end ReciprocityTheory.L2DbarEstimates
