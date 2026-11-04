-- Prove2me | solution 1 for ThreeSum.BandEnumeration.owners_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:12:55.204108+00:00
-- url     : https://prove2.me/submissions/f80f2d17-a6d6-4988-ad0e-044a8086c4e3

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family
namespace ThreeSum.BandEnumeration
theorem _root_.solution (A B C : Family) :
    (owners A B C).length = B.size * C.size + A.size * (B.size + C.size) := by
  simp [owners, List.length_product]
end ThreeSum.BandEnumeration
