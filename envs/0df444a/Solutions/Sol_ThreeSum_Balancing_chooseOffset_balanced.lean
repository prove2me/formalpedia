-- Prove2me | solution 1 for ThreeSum.Balancing.chooseOffset_balanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:01.643081+00:00
-- url     : https://prove2.me/submissions/92fa92f5-0316-4839-aff7-437498646d2b

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_Balancing
import Theorems.Thm_ThreeSum_Balancing_exists_balanced_offset
import Theorems.Thm_ThreeSum_Balancing_chooseOffset_le

set_option autoImplicit false
open ThreeSum ThreeSum.Balancing
open Finset
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G]
namespace ThreeSum.Balancing
theorem _root_.solution [Inhabited G] (keys : List G) (hall : ∀ d, d ∈ keys)
    (F H : G → ℕ) :
    Fintype.card G * correlation F H (chooseOffset keys F H) ≤
      (∑ k, F k) * (∑ k, H k) := by
  obtain ⟨d, hd⟩ := exists_balanced_offset F H
  exact (Nat.mul_le_mul_left _ (chooseOffset_le keys F H (hall d))).trans hd
end ThreeSum.Balancing
