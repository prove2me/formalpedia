-- Prove2me | solution 1 for ThreeSum.SparseBoxes.boundedSubsets_eq_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:31.588715+00:00
-- url     : https://prove2.me/submissions/98223efa-3355-4c62-9218-4d534b3910f6

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
import Theorems.Thm_ThreeSum_SparseBoxes_mem_boundedSubsets

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (ambient : Finset α) (cut : ℕ) :
    boundedSubsets ambient cut = ambient.powerset.filter (fun s => s.card ≤ cut) := by
  ext s
  simp only [mem_boundedSubsets, Finset.mem_filter, Finset.mem_powerset]
end ThreeSum.SparseBoxes
