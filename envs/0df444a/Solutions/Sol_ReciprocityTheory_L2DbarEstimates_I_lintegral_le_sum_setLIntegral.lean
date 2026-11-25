-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.lintegral_le_sum_setLIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:34.925317+00:00
-- url     : https://prove2.me/submissions/b306e39f-1054-4f41-839c-6f734322d396

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (U : ι → Set α) (hU : ∀ i ∈ s, MeasurableSet (U i)) (f : α → ℝ≥0∞) (h : ι → α → ℝ≥0∞)
    (hsupp : ∀ x, f x ≠ 0 → ∃ i ∈ s, x ∈ U i) (hle : ∀ i ∈ s, ∀ x ∈ U i, f x ≤ h i x) :
    ∫⁻ x, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in U i, h i x ∂μ := by
  have hsub : Function.support f ⊆ ⋃ i : s, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hsupp x hx
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  rw [← setLIntegral_eq_of_support_subset hsub]
  calc ∫⁻ x in ⋃ i : s, U i, f x ∂μ ≤ ∑' i : s, ∫⁻ x in U i, f x ∂μ := lintegral_iUnion_le _ _
    _ = ∑ i ∈ s, ∫⁻ x in U i, f x ∂μ := Finset.tsum_subtype s (fun i => ∫⁻ x in U i, f x ∂μ)
    _ ≤ ∑ i ∈ s, ∫⁻ x in U i, h i x ∂μ :=
        Finset.sum_le_sum fun i hi => setLIntegral_mono' (hU i hi) (hle i hi)
end ReciprocityTheory.L2DbarEstimates.I
