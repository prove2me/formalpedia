-- Prove2me | solution 1 for ThreeSum.SourceBandPairData.Data.transfer_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:14:44.846688+00:00
-- url     : https://prove2.me/submissions/d5f27e21-0f0e-494c-88eb-256a13bcf573

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Theorems.Thm_ThreeSum_SourceBandPairData_ordered
import Definitions.Def_WeightedCache3SUM_Alias_f1b01b4676766ea6
import Theorems.Thm_ThreeSum_SourceBandLayout_data_le_hist


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairData
open Light BandPartition
namespace ThreeSum.SourceBandPairData
namespace Data
theorem _root_.solution {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m : ℕ} {shift : ℤ}
    (H : Data μ fL fR base NL NR g p m shift) (hm : 0 < m)
    (K : ∀ a, leftBase base ≤ a → ν a=μ a) : Data ν fL fR base NL NR g p m shift := by
  have ho := ordered base NL NR g m
  refine ⟨?_,?_,?_⟩
  · intro i hi
    apply (H.left i hi).transfer hm
    · intro q _
      exact K _ (by omega)
    · intro a ha _
      have hb := SourceBandLayout.data_le_hist (leftBase base) NL g m i
      unfold SourceBandLayout.data at hb
      exact K _ (by omega)
  · intro i hi
    apply (H.right i hi).transfer hm
    · intro q _
      exact K _ (by omega)
    · intro a ha _
      have hb := SourceBandLayout.data_le_hist (rightBase base NL g m) NR g m i
      unfold SourceBandLayout.data at hb
      exact K _ (by omega)
  · intro r hr
    exact (K _ (by omega)).trans (H.zero r hr)
end Data
end ThreeSum.SourceBandPairData
