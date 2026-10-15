-- Prove2me | solution 1 for ThreeSum.BandEnumeration.candidate_owner
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:37:26.302954+00:00
-- url     : https://prove2.me/submissions/7094cfc7-5120-4263-bea7-376a22c8ab8e

import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_BinarySearch_locate_complete


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BandEnumeration.Family
end ThreeSum.BandEnumeration.Family

section


/-!
# Enumeration of sorted-band triples through their quadratic owner set

Each owner is inverted with one binary interval lookup.  A final constant-size
test checks relevance and ownership.  No cubic list of triples is formed.
-/

namespace ThreeSum.BandEnumeration









namespace Family










theorem lookup_complete (A : Family) (x : ℤ) (i : A.Index)
    (hl : A.lo i ≤ x) (hh : x ≤ A.hi i) : A.lookup x = some i := by
  have hlc := BinarySearch.locate_complete A.lower A.upper A.size x
    A.sorted A.separated i.isLt hl hh
  simp [lookup, hlc]















end Family

open Family



















theorem candidate_owner_sourceProof (A B C : Family) (t : Triple A B C)
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

end


theorem solution : ∀ (A B C : ThreeSum.BandEnumeration.Family) (t : ThreeSum.BandEnumeration.Triple A B C),
  ThreeSum.BandEnumeration.relevant A B C t →
    @Eq.{1} (Option.{0} (ThreeSum.BandEnumeration.Triple A B C))
      (ThreeSum.BandEnumeration.candidate A B C (ThreeSum.BandEnumeration.owner A B C t))
      (@Option.some.{0} (ThreeSum.BandEnumeration.Triple A B C) t) := by
  exact @ThreeSum.BandEnumeration.candidate_owner_sourceProof

#print axioms solution
