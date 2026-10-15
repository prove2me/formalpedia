-- Prove2me | solution 1 for ThreeSum.Radix.mem_representations
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:23:54.47995+00:00
-- url     : https://prove2.me/submissions/44822b78-8b76-4d67-91de-0d823c7efc6f

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Radix_radix_divisibility


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










































/-- The recursive family contains exactly all positional representations,
including their distinct schedules and local edge choices. -/
theorem mem_representations_sourceProof (p : ℤ) (hp : p ≠ 0) (left right : Ω → ℤ)
    (j : ℕ) (a b : ℤ) (xs : List Ω) :
    xs ∈ representations p left right j a b ↔
      xs.length = j ∧ p ^ j ∣ a - positionalHash p left xs ∧
        p ^ j ∣ b - positionalHash p right xs := by
  induction j generalizing a b xs with
  | zero =>
    cases xs <;> simp [representations, positionalHash]
  | succ j ih =>
    cases xs with
    | nil => simp [representations, positionalHash]
    | cons ω xs =>
      have hm : ω :: xs ∈ representations p left right (j + 1) a b ↔
          ω ∈ localFiber p left right a b ∧
            xs ∈ representations p left right j ((a - left ω) / p) ((b - right ω) / p) := by
        simp [representations]
      rw [hm, ih]
      simp only [localFiber, mem_filter, mem_univ, true_and, List.length_cons,
        Nat.add_right_cancel_iff, positionalHash, radix_divisibility p _ _ _ hp]
      tauto














































end ThreeSum.Radix

end

universe u_1

theorem solution : ∀ {Ω : Type u_1} [inst : Fintype.{u_1} Ω] [inst_1 : DecidableEq.{u_1 + 1} Ω] (p : Int),
  @Ne.{1} Int p (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
    ∀ (left right : Ω → Int) (j : Nat) (a b : Int) (xs : List.{u_1} Ω),
      Iff
        (@Membership.mem.{u_1, u_1} (List.{u_1} Ω) (Finset.{u_1} (List.{u_1} Ω))
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (List.{u_1} Ω)) (List.{u_1} Ω)
            (@Finset.instSetLike.{u_1} (List.{u_1} Ω)))
          (@ThreeSum.Radix.representations.{u_1} Ω inst inst_1 p left right j a b) xs)
        (And (@Eq.{1} Nat (@List.length.{u_1} Ω xs) j)
          (And
            (@Dvd.dvd.{0} Int Int.instDvd
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) p j)
              (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) a
                (@ThreeSum.Radix.positionalHash.{u_1} Ω p left xs)))
            (@Dvd.dvd.{0} Int Int.instDvd
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) p j)
              (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) b
                (@ThreeSum.Radix.positionalHash.{u_1} Ω p right xs))))) := by
  exact @ThreeSum.Radix.mem_representations_sourceProof

#print axioms solution
