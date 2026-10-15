-- Prove2me | solution 1 for ThreeSum.BinarySearch.upperSearch_correct
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:39:49.786613+00:00
-- url     : https://prove2.me/submissions/2335ae36-b4a4-43dc-86d6-d675d4cd5af7

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section
attribute [local instance 2000] instPowNat


/-!
# Executable binary search with a comparison budget

`upperSearch` finds the first array entry strictly above a query.  Its fuel is
logarithmic, and the proof accounts for the actual branches taken.  Array
accesses here are explicit function calls; a machine realization must still
implement those calls by bounded-address loads.
-/

namespace ThreeSum.BinarySearch




































theorem upperSearch_correct_sourceProof (f : ℕ → ℤ) (x : ℤ) (n fuel lo hi : ℕ)
    (hsorted : ∀ i j, i ≤ j → j < n → f i ≤ f j)
    (hlo : lo ≤ hi) (hhi : hi ≤ n) (hwidth : hi - lo < 2 ^ fuel)
    (hlower : ∀ i < lo, f i ≤ x)
    (hupper : ∀ i, hi ≤ i → i < n → x < f i) :
    Partition f x n (upperSearch f x fuel lo hi) := by
  induction fuel generalizing lo hi with
  | zero =>
      have heq : lo = hi := by simp only [Nat.pow_zero] at hwidth; omega
      simpa only [Partition, upperSearch, heq] using And.intro hhi (And.intro (heq ▸ hlower) hupper)
  | succ fuel ih =>
      rw [upperSearch]
      split
      · rename_i hlt
        dsimp only
        let mid := (lo + hi) / 2
        have hmidlo : lo ≤ mid := by dsimp [mid]; omega
        have hmidhi : mid < hi := by dsimp [mid]; omega
        have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow] at hwidth
        by_cases htest : f mid ≤ x
        · rw [if_pos htest]
          apply ih (mid + 1) hi (by omega) hhi
          · dsimp [mid] at *; omega
          · intro i hi'
            exact le_trans (hsorted i mid (by omega) (by omega)) htest
          · exact hupper
        · rw [if_neg htest]
          apply ih lo mid hmidlo (by omega)
          · dsimp [mid] at *; omega
          · exact hlower
          · intro i hmi hin
            exact lt_of_lt_of_le (by omega : x < f mid) (hsorted mid i hmi hin)
      · rename_i hstop
        have heq : lo = hi := by omega
        simpa only [Partition, heq] using And.intro hhi (And.intro (heq ▸ hlower) hupper)




























































end ThreeSum.BinarySearch

end


theorem solution : ∀ (f : Nat → Int) (x : Int) (n fuel lo hi : Nat)
  (hsorted :
    ∀ (i j : Nat),
      @LE.le.{0} Nat instLENat i j → @LT.lt.{0} Nat instLTNat j n → @LE.le.{0} Int Int.instLEInt (f i) (f j))
  (hlo : @LE.le.{0} Nat instLENat lo hi) (hhi : @LE.le.{0} Nat instLENat hi n)
  (hwidth :
    @LT.lt.{0} Nat instLTNat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) hi lo)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) fuel))
  (hlower : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i lo → @LE.le.{0} Int Int.instLEInt (f i) x)
  (hupper :
    ∀ (i : Nat), @LE.le.{0} Nat instLENat hi i → @LT.lt.{0} Nat instLTNat i n → @LT.lt.{0} Int Int.instLTInt x (f i)),
  ThreeSum.BinarySearch.Partition f x n (ThreeSum.BinarySearch.upperSearch f x fuel lo hi) := by
  exact @ThreeSum.BinarySearch.upperSearch_correct_sourceProof

#print axioms solution
