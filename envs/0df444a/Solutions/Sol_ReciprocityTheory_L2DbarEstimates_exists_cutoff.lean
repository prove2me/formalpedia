-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.exists_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:43.125199+00:00
-- url     : https://prove2.me/submissions/1a9e47c3-76e5-4baa-833c-49851e215423

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_smoothR_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart_partition

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
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (K U : Set M) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : M → ℝ, SmoothR n z η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ ∀ x ∈ K, η x = 1 := by
  obtain ⟨N, e, χ, he, hs, hc, hts, h0, h1, hK1⟩ := exists_chart_partition n z hz K U hK hU hKU
  have hS : tsupport (fun x => ∑ i, χ i x) ⊆ ⋃ i, tsupport (χ i) := by
    refine closure_minimal ?_ (isClosed_iUnion_of_finite fun i => isClosed_tsupport _)
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact Set.mem_iUnion.2 ⟨i, subset_tsupport _ hi⟩
  refine ⟨fun x => ∑ i, χ i x, smoothR_sum n z Finset.univ χ (fun i _ => hs i),
    (isCompact_iUnion fun i => hc i).of_isClosed_subset (isClosed_tsupport _) hS,
    hS.trans (Set.iUnion_subset fun i => (hts i).trans Set.inter_subset_right),
    fun x => ⟨Finset.sum_nonneg (fun i _ => h0 i x), h1 x⟩, hK1⟩
end ReciprocityTheory.L2DbarEstimates
