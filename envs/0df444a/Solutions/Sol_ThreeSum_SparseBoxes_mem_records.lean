-- Prove2me | solution 1 for ThreeSum.SparseBoxes.mem_records
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:52.222694+00:00
-- url     : https://prove2.me/submissions/83e26076-ed8a-46d5-ab27-b27947aa3dd7

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
import Theorems.Thm_ThreeSum_SparseBoxes_boundedSubsets_eq_filter

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (ambient flags : Finset α) (cut e : ℕ) :
    (⟨flags, e⟩ : Sigma (fun _ : Finset α => ℕ)) ∈ records ambient cut ↔
      flags ⊆ ambient ∧ flags.card ≤ cut ∧ e ≤ flags.card := by
  simp [records, boundedSubsets_eq_filter, Finset.mem_powerset, Nat.lt_succ_iff, and_assoc]
end ThreeSum.SparseBoxes
