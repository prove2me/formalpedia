-- Prove2me | solution 1 for ThreeSum.BandEnumeration.Family.lookup_sound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:37:36.954703+00:00
-- url     : https://prove2.me/submissions/41520142-dbc5-4c54-be34-48814ec5379e

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
import Theorems.Thm_ThreeSum_BinarySearch_locate_sound


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
















theorem lookup_sound_sourceProof (A : Family) (x : ℤ) (i : A.Index)
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

end Family

open Family

































































































































































end ThreeSum.BandEnumeration

end


theorem solution : ∀ (A : ThreeSum.BandEnumeration.Family) (x : Int) (i : A.Index),
  @Eq.{1} (Option.{0} A.Index) (A.lookup x) (@Option.some.{0} A.Index i) →
    And (@LE.le.{0} Int Int.instLEInt (A.lo i) x) (@LE.le.{0} Int Int.instLEInt x (A.hi i)) := by
  exact @ThreeSum.BandEnumeration.Family.lookup_sound_sourceProof

#print axioms solution
