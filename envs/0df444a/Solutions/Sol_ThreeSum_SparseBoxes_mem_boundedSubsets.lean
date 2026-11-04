-- Prove2me | solution 1 for ThreeSum.SparseBoxes.mem_boundedSubsets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:16.435939+00:00
-- url     : https://prove2.me/submissions/bc4aca51-6d2d-41e2-8bb9-d154e8198598

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

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (ambient s : Finset α) (cut : ℕ) :
    s ∈ boundedSubsets ambient cut ↔ s ⊆ ambient ∧ s.card ≤ cut := by
  simp only [boundedSubsets, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨j, hj, hs, hc⟩
    exact ⟨hs, by omega⟩
  · rintro ⟨hs, hc⟩
    exact ⟨s.card, by omega, hs, rfl⟩
end ThreeSum.SparseBoxes
