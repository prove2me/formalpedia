-- Prove2me | solution 1 for ThreeSum.BandEnumeration.candidate_owner_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:41.354611+00:00
-- url     : https://prove2.me/submissions/185e60e8-fe48-4745-91dc-fef88a22ea66

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Theorems.Thm_ThreeSum_BandEnumeration_Family_lookup_complete

set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family
namespace ThreeSum.BandEnumeration
theorem _root_.solution (A B C : Family) (t : Triple A B C)
    (ht : relevant A B C t) : candidate A B C (owner A B C t) = some t := by
  rcases t with ⟨i, j, k⟩
  change A.lo i ≤ C.hi k - B.lo j ∧ C.lo k - B.hi j ≤ A.hi i at ht
  unfold owner Bands.tripleOwner
  dsimp only
  by_cases hfirst : A.lo i < C.lo k - B.hi j
  · rw [if_pos hfirst]
    simp only [candidate]
    rw [lookup_complete A _ i (by omega) ht.2]
    rfl
  · rw [if_neg hfirst]
    unfold Bands.overlapOwner
    dsimp only
    by_cases hsecond : A.lo i + B.lo j ≤ C.lo k
    · rw [if_pos hsecond]
      simp only [candidate]
      rw [lookup_complete B _ j (by omega) (by omega)]
      rfl
    · rw [if_neg hsecond]
      simp only [candidate]
      rw [lookup_complete C _ k (by omega) (by omega)]
      rfl
end ThreeSum.BandEnumeration
