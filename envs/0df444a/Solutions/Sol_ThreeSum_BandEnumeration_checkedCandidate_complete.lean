-- Prove2me | solution 1 for ThreeSum.BandEnumeration.checkedCandidate_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:53:11.963253+00:00
-- url     : https://prove2.me/submissions/ee8da611-a690-46c6-977b-87b2671b338a

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_463ae85b9bcdc14e

set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family
namespace ThreeSum.BandEnumeration
theorem _root_.solution (A B C : Family) (t : Triple A B C)
    (ht : relevant A B C t) : checkedCandidate A B C (owner A B C t) = some t := by
  simp [checkedCandidate, candidate_owner A B C t ht, ht]
end ThreeSum.BandEnumeration
