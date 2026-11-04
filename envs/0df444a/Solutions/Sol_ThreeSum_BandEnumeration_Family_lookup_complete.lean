-- Prove2me | solution 1 for ThreeSum.BandEnumeration.Family.lookup_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:11:14.621938+00:00
-- url     : https://prove2.me/submissions/fa335ebe-cbd8-4b25-94e3-6bc309bc2a89

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_b4f931c7e067a8b6


set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open ThreeSum.BandEnumeration.Family
namespace ThreeSum.BandEnumeration.Family
theorem _root_.solution (A : Family) (x : ℤ) (i : A.Index)
    (hl : A.lo i ≤ x) (hh : x ≤ A.hi i) : A.lookup x = some i := by
  have hlc := BinarySearch.locate_complete A.lower A.upper A.size x
    A.sorted A.separated i.isLt hl hh
  simp [lookup, hlc]
end ThreeSum.BandEnumeration.Family
