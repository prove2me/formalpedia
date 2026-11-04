-- Prove2me | solution 1 for ThreeSum.Radix.representations_card_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:30.826396+00:00
-- url     : https://prove2.me/submissions/0bcbf273-5e70-41f2-b0f3-380b2ca32662

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Radix

set_option autoImplicit false
open ThreeSum ThreeSum.Radix
open Finset
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
namespace ThreeSum.Radix
theorem _root_.solution (p : ℤ) (left right : Ω → ℤ) (B : ℕ)
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
