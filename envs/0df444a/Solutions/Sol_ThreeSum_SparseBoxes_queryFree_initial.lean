-- Prove2me | solution 1 for ThreeSum.SparseBoxes.queryFree_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:12.819539+00:00
-- url     : https://prove2.me/submissions/7cc03baf-b384-4f5d-97d1-597f5ce4452d

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
theorem _root_.solution (q u : Finset α) :
    IsInitial (q \ u) (queryFree q u) := by
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro a ha b hb hba
  refine Finset.mem_filter.mpr ⟨hb, ?_⟩
  intro x hx
  exact hba.trans ((Finset.mem_filter.mp ha).2 x hx)
end ThreeSum.SparseBoxes
