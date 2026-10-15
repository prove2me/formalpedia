-- Prove2me | solution 1 for ThreeSum.Radix.representations_card_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:58:27.670658+00:00
-- url     : https://prove2.me/submissions/0c3c8460-d169-4472-a1c4-2b29babeb35f

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Exact radix composition of finite local covers

The recursion enumerates only representations of one supplied target pair.
The coverage and multiplicity proofs quantify over arbitrary integer targets;
no enumeration of the square of the global modulus is used in the definition.
-/

namespace ThreeSum.Radix

open Finset
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]













































































/-- Multiplicity compounds once per local choice; there is no extra carry
factor in the global bound. -/
theorem representations_card_le_sourceProof (p : ℤ) (left right : Ω → ℤ) (B : ℕ)
    (hcap : ∀ a b, (localFiber p left right a b).card ≤ B)
    (j : ℕ) (a b : ℤ) : (representations p left right j a b).card ≤ B ^ j := by
  induction j generalizing a b with
  | zero => simp [representations]
  | succ j ih =>
    calc
      (representations p left right (j + 1) a b).card ≤
          ∑ ω ∈ localFiber p left right a b,
            ((representations p left right j ((a - left ω) / p)
              ((b - right ω) / p)).image (List.cons ω)).card := card_biUnion_le
      _ ≤ ∑ _ω ∈ localFiber p left right a b, B ^ j := by
        apply sum_le_sum
        intro ω _
        exact card_image_le.trans (ih _ _)
      _ = (localFiber p left right a b).card * B ^ j := by simp
      _ ≤ B * B ^ j := Nat.mul_le_mul_right _ (hcap a b)
      _ = B ^ (j + 1) := by ring













end ThreeSum.Radix

end

universe u_1

theorem solution : ∀ {Ω : Type u_1} [inst : Fintype.{u_1} Ω] [inst_1 : DecidableEq.{u_1 + 1} Ω] (p : Int) (left right : Ω → Int) (B : Nat),
  (∀ (a b : Int),
      @LE.le.{0} Nat instLENat (@Finset.card.{u_1} Ω (@ThreeSum.Radix.localFiber.{u_1} Ω inst p left right a b)) B) →
    ∀ (j : Nat) (a b : Int),
      @LE.le.{0} Nat instLENat
        (@Finset.card.{u_1} (List.{u_1} Ω) (@ThreeSum.Radix.representations.{u_1} Ω inst inst_1 p left right j a b))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) B j) := by
  exact @ThreeSum.Radix.representations_card_le_sourceProof

#print axioms solution
