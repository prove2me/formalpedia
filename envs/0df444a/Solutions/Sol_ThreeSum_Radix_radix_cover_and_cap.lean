-- Prove2me | solution 1 for ThreeSum.Radix.radix_cover_and_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:39.538667+00:00
-- url     : https://prove2.me/submissions/5f3593d8-d3c0-498f-afe3-7411fbe99c50

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_WeightedCache3SUM_Alias_322f8176f0ec5cb8
import Theorems.Thm_ThreeSum_Radix_representations_nonempty
import Definitions.Def_WeightedCache3SUM_Alias_8a1bc378764c1bfd

set_option autoImplicit false
open ThreeSum ThreeSum.Radix
open Finset
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
namespace ThreeSum.Radix
theorem _root_.solution (p : ℤ) (hp : p ≠ 0) (left right : Ω → ℤ) (B : ℕ)
    (hcover : ∀ a b, (localFiber p left right a b).Nonempty)
    (hcap : ∀ a b, (localFiber p left right a b).card ≤ B)
    (j : ℕ) (a b : ℤ) :
    (∃ xs, xs.length = j ∧ p ^ j ∣ a - positionalHash p left xs ∧
      p ^ j ∣ b - positionalHash p right xs) ∧
    (representations p left right j a b).card ≤ B ^ j := by
  obtain ⟨xs, hxs⟩ := representations_nonempty p left right hcover j a b
  exact ⟨⟨xs, (mem_representations p hp left right j a b xs).mp hxs⟩,
    representations_card_le p left right B hcap j a b⟩
end ThreeSum.Radix
