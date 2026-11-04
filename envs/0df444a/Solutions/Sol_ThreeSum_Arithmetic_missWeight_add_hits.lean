-- Prove2me | solution 1 for ThreeSum.Arithmetic.missWeight_add_hits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:14:00.149789+00:00
-- url     : https://prove2.me/submissions/3d5ff5cf-6e42-4f5b-8571-8c89a439dff7

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic

set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators
namespace ThreeSum.Arithmetic
theorem _root_.solution (L : Finset ℤ) (x : ℤ) :
    missWeight L x + (∑ l ∈ L, dividesIndicator l x) = L.card := by
  unfold missWeight
  rw [← Finset.sum_add_distrib]
  calc
    (∑ l ∈ L, ((if l ∣ x then 0 else 1) + dividesIndicator l x)) =
        ∑ _l ∈ L, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases h : l ∣ x <;> simp [dividesIndicator, h]
    _ = L.card := by simp
end ThreeSum.Arithmetic
