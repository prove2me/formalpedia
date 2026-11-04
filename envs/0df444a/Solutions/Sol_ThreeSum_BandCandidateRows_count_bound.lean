-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:28:36.212111+00:00
-- url     : https://prove2.me/submissions/a88cb0c3-68c0-4381-919c-7ef0f3cd07e0

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Theorems.Thm_ThreeSum_BandCandidateRows_records_length
import Theorems.Thm_ThreeSum_LightBandEnumeration_count_mono


set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
namespace ThreeSum.BandCandidateRows
theorem _root_.solution {A B C : Family} {m : ℕ}
    (hA : A.size ≤ m) (hB : B.size ≤ m) (hC : C.size ≤ m) :
    (records A B C).length ≤ 3*m^2 := by
  rw [records_length]
  have hh := LightBandEnumeration.count_mono hA hB hC
  calc
    _ ≤ LightBandEnumeration.count m m m := hh
    _ = 3*m^2 := by unfold LightBandEnumeration.count; ring
end ThreeSum.BandCandidateRows
