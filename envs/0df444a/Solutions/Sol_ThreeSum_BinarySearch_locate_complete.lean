-- Prove2me | solution 1 for ThreeSum.BinarySearch.locate_complete
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:09:22.225284+00:00
-- url     : https://prove2.me/submissions/f9ec7ad6-104c-4b8f-90de-e7eeb5a54faf

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log
import Theorems.Thm_ThreeSum_BinarySearch_upperSearch_correct


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Executable binary search with a comparison budget

`upperSearch` finds the first array entry strictly above a query.  Its fuel is
logarithmic, and the proof accounts for the actual branches taken.  Array
accesses here are explicit function calls; a machine realization must still
implement those calls by bounded-address loads.
-/

namespace ThreeSum.BinarySearch













































































theorem upperBound_correct (f : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → f i ≤ f j) :
    Partition f x n (upperBound f n x) := by
  apply upperSearch_correct f x n (Nat.log 2 n + 1) 0 n hsorted (by omega) (by omega)
  · simpa only [Nat.sub_zero] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  · intro i hi; omega
  · intro i hi hin; omega






























theorem locate_complete_sourceProof (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    (hseparated : ∀ i j, i < j → j < n → hi i < lo j)
    {i : ℕ} (hin : i < n) (hil : lo i ≤ x) (hih : x ≤ hi i) :
    locate lo hi n x = some i := by
  have hp := upperBound_correct lo n x hsorted
  rcases hp with ⟨hkn, hpre, hpost⟩
  have hik : i < upperBound lo n x := by
    by_contra hh
    have hh' := hpost i (by omega) hin
    omega
  have heq : upperBound lo n x = i + 1 := by
    by_contra hh
    have hnext : i + 1 < upperBound lo n x := by omega
    have hnl := hpre (i + 1) hnext
    have hnh := hseparated i (i + 1) (by omega) (by omega)
    omega
  simp [locate, heq, hih]

end ThreeSum.BinarySearch

end


theorem solution : ∀ (lo hi : Nat → Int) (n : Nat) (x : Int),
  (∀ (i j : Nat),
      @LE.le.{0} Nat instLENat i j → @LT.lt.{0} Nat instLTNat j n → @LE.le.{0} Int Int.instLEInt (lo i) (lo j)) →
    (∀ (i j : Nat),
        @LT.lt.{0} Nat instLTNat i j → @LT.lt.{0} Nat instLTNat j n → @LT.lt.{0} Int Int.instLTInt (hi i) (lo j)) →
      ∀ {i : Nat},
        @LT.lt.{0} Nat instLTNat i n →
          @LE.le.{0} Int Int.instLEInt (lo i) x →
            @LE.le.{0} Int Int.instLEInt x (hi i) →
              @Eq.{1} (Option.{0} Nat) (ThreeSum.BinarySearch.locate lo hi n x) (@Option.some.{0} Nat i) := by
  exact @ThreeSum.BinarySearch.locate_complete_sourceProof

#print axioms solution
