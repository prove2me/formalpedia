-- Prove2me | solution 1 for ThreeSum.BandEnumeration.enumerate_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:18.051203+00:00
-- url     : https://prove2.me/submissions/50b64626-40ea-4647-8902-644eee48dd79

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Theorems.Thm_ThreeSum_BandEnumeration_owners_length

set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family
namespace ThreeSum.BandEnumeration
theorem _root_.solution (A B C : Family) :
    (enumerate A B C).length ≤ B.size * C.size + A.size * (B.size + C.size) := by
  rw [← owners_length A B C]
  exact List.length_filterMap_le _ _
end ThreeSum.BandEnumeration
