-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.vol_isFiniteMeasureOnCompacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:34.832832+00:00
-- url     : https://prove2.me/submissions/8d7aae2b-68ca-4f3d-9b3a-4d09f52f15f4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart_cover
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_injOn_source_of_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_image
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous


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
theorem _root_.solution {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) :
    IsFiniteMeasureOnCompacts (vol n z) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨T, hTo, hTU, hTc⟩ := exists_chart_cover n z hz
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover T hTo (by rw [hTU]; exact Set.subset_univ K)
  have hzK : volume (z '' K) < ⊤ := (hK.image hz.continuous).measure_lt_top
  calc vol n z K ≤ vol n z (⋃ i ∈ s, K ∩ T i) := by
        refine measure_mono (fun x hx => ?_)
        have h1 := hs hx
        simp only [Set.mem_iUnion] at h1 ⊢
        obtain ⟨i, hi, hxi⟩ := h1
        exact ⟨i, hi, hx, hxi⟩
    _ ≤ ∑ i ∈ s, vol n z (K ∩ T i) := measure_biUnion_finset_le s _
    _ < ⊤ := by
        refine ENNReal.sum_lt_top.2 (fun i _ => ?_)
        rcases hTc i with h | ⟨e, he, hTe⟩
        · simp [h]
        · rw [vol_image n z hz e.source e.open_source (injOn_source_of_chart n z e he) _
            (hK.isClosed.measurableSet.inter (hTo i).measurableSet)
            (Set.inter_subset_right.trans hTe)]
          exact lt_of_le_of_lt (measure_mono (Set.image_mono Set.inter_subset_left)) hzK
end ReciprocityTheory.L2DbarEstimates
