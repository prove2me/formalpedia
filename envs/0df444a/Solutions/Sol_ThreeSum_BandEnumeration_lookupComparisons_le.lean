-- Prove2me | solution 1 for ThreeSum.BandEnumeration.lookupComparisons_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:23.835042+00:00
-- url     : https://prove2.me/submissions/3bf3bf5c-17cb-4455-9794-94a07b003e51

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Theorems.Thm_ThreeSum_BinarySearch_comparisons_le


set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family
namespace ThreeSum.BandEnumeration
theorem _root_.solution (A B C : Family) (o : Owner A B C) :
    lookupComparisons A B C o ≤
      Nat.log 2 A.size + Nat.log 2 B.size + Nat.log 2 C.size + 1 := by
  rcases o with ⟨j, k⟩ | ⟨i, j | k⟩
  · exact (BinarySearch.comparisons_le _ _ _ _ _).trans (by omega)
  · exact (BinarySearch.comparisons_le _ _ _ _ _).trans (by omega)
  · exact (BinarySearch.comparisons_le _ _ _ _ _).trans (by omega)
end ThreeSum.BandEnumeration
