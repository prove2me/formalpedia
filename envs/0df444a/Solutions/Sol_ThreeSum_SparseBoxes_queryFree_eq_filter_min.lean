-- Prove2me | solution 1 for ThreeSum.SparseBoxes.queryFree_eq_filter_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:32.563595+00:00
-- url     : https://prove2.me/submissions/db87c41a-5c35-4acf-8186-81be2825d0e8

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
theorem _root_.solution (q u : Finset α) (hu : u.Nonempty) :
    queryFree q u = (q \ u).filter (fun x => x < u.min' hu) := by
  ext x
  simp only [queryFree, Finset.mem_filter]
  constructor
  · rintro ⟨hx, ho⟩
    exact ⟨hx, ho _ (Finset.min'_mem u hu)⟩
  · rintro ⟨hx, ho⟩
    refine ⟨hx, ?_⟩
    intro y hy
    exact ho.trans_le (Finset.min'_le u y hy)
end ThreeSum.SparseBoxes
