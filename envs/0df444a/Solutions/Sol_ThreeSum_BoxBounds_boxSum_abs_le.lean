-- Prove2me | solution 1 for ThreeSum.BoxBounds.boxSum_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:41:37.100932+00:00
-- url     : https://prove2.me/submissions/f8a9b678-fce7-48b0-b036-18a3c29c5140

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-! # Derived integer bounds for signed sparse-box sums -/

namespace ThreeSum.BoxBounds

open Finset ThreeSum.SubsetAddress

theorem boxSum_abs_le_sourceProof {L cut U : ℕ} (flags free : Finset (Fin L))
    (weight : Finset (Fin L) → ℤ) (hflags : flags.card ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ U) :
    |SparseBoxes.boxSum flags free weight| ≤ ((2^L*U : ℕ) : ℤ) := by
  have hwidth := (subsetMask_isMask flags).le_width
  have hpow := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) hwidth
  have hmul := Nat.mul_le_mul_right U hpow
  unfold SparseBoxes.boxSum
  calc
    _ ≤ ∑ leaf ∈ flags.powerset, |if flags \ free ⊆ leaf then weight leaf else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _leaf ∈ flags.powerset, (U : ℤ) := by
      apply Finset.sum_le_sum
      intro leaf hl
      have hcard := (Finset.card_le_card (Finset.mem_powerset.mp hl)).trans hflags
      split
      · exact hweight leaf hcard
      · simp
    _ = ((2^flags.card*U : ℕ) : ℤ) := by simp
    _ ≤ _ := by exact_mod_cast hmul

end ThreeSum.BoxBounds

end


theorem solution : ∀ {L cut U : Nat} (flags free : Finset.{0} (Fin L)) (weight : Finset.{0} (Fin L) → Int),
  @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) flags) cut →
    (∀ (S : Finset.{0} (Fin L)),
        @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin L) S) cut →
          @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (weight S))
            (@Nat.cast.{0} Int instNatCastInt U)) →
      @LE.le.{0} Int Int.instLEInt
        (@abs.{0} Int instLatticeInt Int.instAddGroup
          (@ThreeSum.SparseBoxes.boxSum.{0} (Fin L) (@Fin.instLinearOrder L) flags free weight))
        (@Nat.cast.{0} Int instNatCastInt
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
            U)) := by
  exact @ThreeSum.BoxBounds.boxSum_abs_le_sourceProof

#print axioms solution
