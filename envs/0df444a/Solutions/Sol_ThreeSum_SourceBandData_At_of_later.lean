-- Prove2me | solution 1 for ThreeSum.SourceBandData.At.of_later
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:10:29.614405+00:00
-- url     : https://prove2.me/submissions/6a2882ed-15e6-4577-80bf-dd2fadbe89c2

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_WeightedCache3SUM_Alias_f1b01b4676766ea6
import Theorems.Thm_ThreeSum_SourceBandLayout_data_le_hist
import Theorems.Thm_ThreeSum_SourceBandLayout_flat_end_le_later
import Theorems.Thm_ThreeSum_SourceBandLayout_header_end


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandData
open Light BandPartition SourceBandLayout
namespace ThreeSum.SourceBandData
namespace At
theorem _root_.solution {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i k : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i)
    (K : KeptBut μ ν (hist base n g m k) (base+6*k) 6)
    (hm : 0 < m) (hik : i < k) (hk : k < size n g) :
    At ν f base n g p m shift i := by
  have he := header_end (m := m) (base := base) hk
  have hb := data_le_hist base n g m i
  have hf := flat_end_le_later (base := base) (n := n) (g := g) (m := m) hik
  unfold data at hb
  apply H.transfer hm
  · intro q hq
    exact K _ ⟨by omega,Or.inl (by omega)⟩
  · intro x hx hxe
    exact K _ ⟨by omega,Or.inr (by omega)⟩
end At
end ThreeSum.SourceBandData
