-- Prove2me | solution 1 for ThreeSum.LightEncodedColorFiniteSources.free_le_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:33:30.472801+00:00
-- url     : https://prove2.me/submissions/2171d698-41f6-417e-adc4-5fb6f01807cb

import Definitions.Def_Submission_ThreeSum_EncodedColorSourcesCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteRetention
import Definitions.Def_Submission_ThreeSum_LightEncodedColorFiniteSources
import Theorems.Thm_ThreeSum_EncodedColorCoverData_header_end
import Theorems.Thm_ThreeSum_EncodedColorWantedData_header_le_nextFree
import Theorems.Thm_ThreeSum_SourceBandLayout_header_end


set_option autoImplicit false
open ThreeSum ThreeSum.LightEncodedColorFiniteSources
open Light Scales TrimScales BandScales
namespace ThreeSum.LightEncodedColorFiniteSources
theorem _root_.solution (free n p M : ℕ) [NeZero M] (xs : List ℤ) : free ≤ base free n p M xs := by
  have h := EncodedColorWantedData.header_le_nextFree
    (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length)
    M (LightGuardedWanted.left p xs)
    (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
    (3*xs.length) (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ)
  have hk := EncodedColorCoverData.header_end free (microHalf (inputBits n)) (blockCount (inputBits n))
  change _ ≤ base free n p M xs at h
  unfold LightGuardedWanted.wantedFree at h
  omega
end ThreeSum.LightEncodedColorFiniteSources
