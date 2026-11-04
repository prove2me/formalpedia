-- Prove2me | solution 1 for ThreeSum.SparseBoxes.IsInitial.erase_max_included
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:14.005137+00:00
-- url     : https://prove2.me/submissions/11b8b7f2-aa11-44eb-a77e-fda325f6a652

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
    IsInitial flags (free.erase (free.max' hn)) := by
  let a := free.max' hn
  refine ⟨(Finset.erase_subset a free).trans h.1, ?_⟩
  intro x hx y hy hyx
  have hxf := Finset.mem_of_mem_erase hx
  have hyf := h.2 x hxf y hy hyx
  have hya : y ≠ a := by
    intro he
    subst y
    have hxa : x ≤ a := Finset.le_max' free x hxf
    exact (not_lt_of_ge hxa) hyx
  exact Finset.mem_erase.mpr ⟨hya, hyf⟩
end IsInitial
end ThreeSum.SparseBoxes
