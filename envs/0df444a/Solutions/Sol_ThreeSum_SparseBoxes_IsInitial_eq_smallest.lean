-- Prove2me | solution 1 for ThreeSum.SparseBoxes.IsInitial.eq_smallest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:50.698166+00:00
-- url     : https://prove2.me/submissions/7b657b8c-d3b2-476a-91a3-592626152eac

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
import Theorems.Thm_ThreeSum_SparseBoxes_IsLargest_unique
import Theorems.Thm_ThreeSum_SparseBoxes_smallest_spec
import Theorems.Thm_ThreeSum_SparseBoxes_IsInitial_unique

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
namespace IsInitial
theorem _root_.solution {flags free : Finset α}
    (h : IsInitial flags free) : free = smallest free.card flags := by
  have hs := smallest_spec free.card flags (Finset.card_le_card h.1)
  exact h.unique hs.2.2 hs.2.1.symm
end IsInitial
end ThreeSum.SparseBoxes
