-- Prove2me | solution 1 for ThreeSum.Radix.mem_representations_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:59.999126+00:00
-- url     : https://prove2.me/submissions/5663d28a-9f97-4881-bc53-6eac37c13fb6

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_WeightedCache3SUM_Alias_7c515d7a0181c20c

set_option autoImplicit false
open ThreeSum ThreeSum.Radix
open Finset
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
namespace ThreeSum.Radix
theorem _root_.solution (p : ℤ) (hp : p ≠ 0) (left right : Ω → ℤ)
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
