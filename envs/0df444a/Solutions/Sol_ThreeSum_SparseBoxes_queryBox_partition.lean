-- Prove2me | solution 1 for ThreeSum.SparseBoxes.queryBox_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:01.759205+00:00
-- url     : https://prove2.me/submissions/7dd1b5fb-9988-46b3-8cc9-a81931d6e0c9

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
import Theorems.Thm_ThreeSum_SparseBoxes_IsLargest_unique
import Theorems.Thm_ThreeSum_SparseBoxes_queryBox_iff_isLargest

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (q leaf : Finset α) (t : ℕ) (hlq : leaf ⊆ q)
    (ht : t ≤ (q \ leaf).card) :
    ∃! u, u ∈ q.powersetCard t ∧ QueryBox q u leaf := by
  let u := largest t (q \ leaf)
  have hs := largest_spec t (q \ leaf) ht
  have huq : u ⊆ q := hs.1.trans Finset.sdiff_subset
  refine ⟨u, ⟨Finset.mem_powersetCard.mpr ⟨huq, hs.2.1⟩, ?_⟩, ?_⟩
  · exact (queryBox_iff_isLargest q u leaf t huq hs.2.1 hlq).mpr hs
  · intro v hv
    obtain ⟨hvq, hvc⟩ := Finset.mem_powersetCard.mp hv.1
    exact IsLargest.unique
      ((queryBox_iff_isLargest q v leaf t hvq hvc hlq).mp hv.2) hs
end ThreeSum.SparseBoxes
