-- Prove2me | solution 1 for ThreeSum.Subset.partialZeta_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:14.724605+00:00
-- url     : https://prove2.me/submissions/b9d6e28d-77c7-41ef-9f33-5226655219ba

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Subset

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution (f : Finset α → ℤ) (u : Finset α) :
    partialZeta u f u = zeta f u := by
  simp [partialZeta, zeta]
end ThreeSum.Subset
