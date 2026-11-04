-- Prove2me | solution 1 for ThreeSum.SparseBoxes.IsInitial.erase_max_excluded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:15.207286+00:00
-- url     : https://prove2.me/submissions/c610b7b1-cb16-428f-9c04-6a73b9cfdeee

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
namespace IsInitial
theorem _root_.solution {flags free : Finset α}
    (h : IsInitial flags free) (hn : free.Nonempty) :
    IsInitial (flags.erase (free.max' hn)) (free.erase (free.max' hn)) := by
  let a := free.max' hn
  refine ⟨Finset.erase_subset_erase a h.1, ?_⟩
  intro x hx y hy hyx
  exact Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hy).1,
      h.2 x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hyx⟩
end IsInitial
end ThreeSum.SparseBoxes
