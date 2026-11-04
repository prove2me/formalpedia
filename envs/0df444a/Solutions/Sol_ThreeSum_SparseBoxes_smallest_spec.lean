-- Prove2me | solution 1 for ThreeSum.SparseBoxes.smallest_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:10.481202+00:00
-- url     : https://prove2.me/submissions/028b04dc-eb3f-4090-9d93-585656710c6c

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Theorems.Thm_ThreeSum_SparseBoxes_largest_spec

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (t : ℕ) (flags : Finset α) (h : t ≤ flags.card) :
    smallest t flags ⊆ flags ∧ (smallest t flags).card = t ∧
      IsInitial flags (smallest t flags) := by
  have hs := @largest_spec (OrderDual α) _ t flags h
  refine ⟨hs.1, hs.2.1, hs.1, ?_⟩
  intro a ha b hb hba
  by_contra hbn
  have hab : a < b := hs.2.2 a ha b hb hbn
  exact (lt_asymm hba) hab
end ThreeSum.SparseBoxes
