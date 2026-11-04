-- Prove2me | solution 1 for ThreeSum.SparseBoxes.queryBox_iff_isLargest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:33.662323+00:00
-- url     : https://prove2.me/submissions/5853991a-6b27-4b9a-acd1-d4db24c03c53

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
import Theorems.Thm_ThreeSum_SparseBoxes_queryBox_iff_separator

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (q u leaf : Finset α) (t : ℕ)
    (huq : u ⊆ q) (huc : u.card = t) (hlq : leaf ⊆ q) :
    QueryBox q u leaf ↔ IsLargest t (q \ leaf) u := by
  rw [queryBox_iff_separator q u leaf huq]
  simp only [IsLargest, huc, true_and, and_true]
  exact and_iff_right hlq
end ThreeSum.SparseBoxes
