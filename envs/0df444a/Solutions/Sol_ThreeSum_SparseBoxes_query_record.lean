-- Prove2me | solution 1 for ThreeSum.SparseBoxes.query_record
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:50.471324+00:00
-- url     : https://prove2.me/submissions/dda2c0b7-983d-496d-aeb7-986aeb52d9de

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
import Theorems.Thm_ThreeSum_SparseBoxes_IsInitial_eq_smallest
import Theorems.Thm_ThreeSum_SparseBoxes_queryFree_initial
import Theorems.Thm_ThreeSum_SparseBoxes_mem_records

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (ambient q u : Finset α) (t : ℕ)
    (hqa : q ⊆ ambient) (hu : u ∈ q.powersetCard t) :
    (⟨q \ u, (queryFree q u).card⟩ : Sigma (fun _ : Finset α => ℕ)) ∈
      records ambient (q.card - t) ∧
    queryFree q u = smallest (queryFree q u).card (q \ u) := by
  obtain ⟨huq, huc⟩ := Finset.mem_powersetCard.mp hu
  have hi := queryFree_initial q u
  refine ⟨(mem_records ambient (q \ u) (q.card - t) _).mpr
    ⟨Finset.sdiff_subset.trans hqa, ?_, Finset.card_le_card hi.1⟩, hi.eq_smallest⟩
  rw [Finset.card_sdiff_of_subset huq, huc]
end ThreeSum.SparseBoxes
