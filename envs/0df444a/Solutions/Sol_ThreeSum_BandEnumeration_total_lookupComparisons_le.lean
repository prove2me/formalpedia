-- Prove2me | solution 1 for ThreeSum.BandEnumeration.total_lookupComparisons_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:47.773935+00:00
-- url     : https://prove2.me/submissions/555f1aa5-3f6b-415a-a674-93e117077cc0

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Theorems.Thm_ThreeSum_BandEnumeration_owners_length
import Theorems.Thm_ThreeSum_BandEnumeration_lookupComparisons_le

set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family
namespace ThreeSum.BandEnumeration
theorem _root_.solution (A B C : Family) :
    ((owners A B C).map (lookupComparisons A B C)).sum ≤
      (B.size * C.size + A.size * (B.size + C.size)) *
        (Nat.log 2 A.size + Nat.log 2 B.size + Nat.log 2 C.size + 1) := by
  let budget := Nat.log 2 A.size + Nat.log 2 B.size + Nat.log 2 C.size + 1
  have hlist : ∀ os : List (Owner A B C),
      (os.map (lookupComparisons A B C)).sum ≤ os.length * budget := by
    intro os
    induction os with
    | nil => simp
    | cons o os ih =>
        have ho := lookupComparisons_le A B C o
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add ho ih |>.trans (by omega)
  simpa only [owners_length, budget] using hlist (owners A B C)
end ThreeSum.BandEnumeration
