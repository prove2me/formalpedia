-- Prove2me | solution 1 for ThreeSum.BandEnumeration.Family.lookup_sound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:40.133211+00:00
-- url     : https://prove2.me/submissions/d2de0747-77ca-4310-a3e6-cb4221580bb8

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_f0b9790e2f96cf93


set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open ThreeSum.BandEnumeration.Family
namespace ThreeSum.BandEnumeration.Family
theorem _root_.solution (A : Family) (x : ℤ) (i : A.Index)
    (h : A.lookup x = some i) : A.lo i ≤ x ∧ x ≤ A.hi i := by
  unfold lookup at h
  cases he : BinarySearch.locate A.lower A.upper A.size x with
  | none => simp [he] at h
  | some j =>
      simp only [he] at h
      dsimp only [Bind.bind, Option.bind] at h
      split at h
      · have hij : (⟨j, ‹j < A.size›⟩ : A.Index) = i := Option.some.inj h
        subst i
        exact (BinarySearch.locate_sound A.lower A.upper A.size x A.sorted he).2
      · cases h
end ThreeSum.BandEnumeration.Family
