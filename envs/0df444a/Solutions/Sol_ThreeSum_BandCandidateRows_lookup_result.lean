-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.lookup_result
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:01.470458+00:00
-- url     : https://prove2.me/submissions/07f6df10-0d2e-4b01-a735-61f34819c2d1

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Theorems.Thm_ThreeSum_BandEnumeration_Family_lookup_complete
import Definitions.Def_WeightedCache3SUM_Alias_183fd7d896c180f9
import Theorems.Thm_ThreeSum_LightBandEnumeration_lookup_complete
import Theorems.Thm_ThreeSum_LightBandEnumeration_lookup_sound


set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
namespace ThreeSum.BandCandidateRows
theorem _root_.solution (A : Family) (x : ℤ) (i : A.Index) (hi : A.lookup x=some i) :
    LightBandLookup.result A.lower A.upper A.size x=i.val+1 :=
  LightBandEnumeration.lookup_complete A i.isLt (A.lookup_sound x i hi).1 (A.lookup_sound x i hi).2
end ThreeSum.BandCandidateRows
