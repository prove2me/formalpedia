-- Prove2me | solution 1 for ThreeSum.BinarySearch.locate_sound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:09:49.188431+00:00
-- url     : https://prove2.me/submissions/f45add0a-804c-4def-ae13-40c116d2311e

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












theorem locate_sound_sourceProof (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    {i : ℕ} (h : locate lo hi n x = some i) :
    i < n ∧ lo i ≤ x ∧ x ≤ hi i := by
  have hp := upperBound_correct lo n x hsorted
  rcases hp with ⟨hkn, hpre, hpost⟩
  unfold locate at h
  dsimp only at h
  split at h
  · rename_i hk
    split at h
    · rename_i hxh
      have heq : upperBound lo n x - 1 = i := Option.some.inj h
      subst i
      exact ⟨by omega, hpre _ (by omega), hxh⟩
    · cases h
  · cases h




















end ThreeSum.BinarySearch

end


theorem solution : ∀ (lo hi : Nat → Int) (n : Nat) (x : Int),
  (∀ (i j : Nat),
      @LE.le.{0} Nat instLENat i j → @LT.lt.{0} Nat instLTNat j n → @LE.le.{0} Int Int.instLEInt (lo i) (lo j)) →
    ∀ {i : Nat},
      @Eq.{1} (Option.{0} Nat) (ThreeSum.BinarySearch.locate lo hi n x) (@Option.some.{0} Nat i) →
        And (@LT.lt.{0} Nat instLTNat i n)
          (And (@LE.le.{0} Int Int.instLEInt (lo i) x) (@LE.le.{0} Int Int.instLEInt x (hi i))) := by
  exact @ThreeSum.BinarySearch.locate_sound_sourceProof

#print axioms solution
