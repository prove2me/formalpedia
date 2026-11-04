-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedData.header_le_nextFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:28:05.041972+00:00
-- url     : https://prove2.me/submissions/994485b3-be1f-4438-977b-8bdc3aa019d1

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedData
import Theorems.Thm_Light_Ends_next


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedData
open Light WantedResidueKeys
namespace ThreeSum.EncodedColorWantedData
theorem _root_.solution (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) :
    out+4 ≤ nextFree out M left right NL NR shift := by
  unfold nextFree LightWantedSetup.pairBase LightSourceBucketSetup.next LightWantedSetup.bucketBase
    LightWantedSetup.rightCodes LightWantedSetup.leftCodes
  omega
end ThreeSum.EncodedColorWantedData
