-- Prove2me | solution 1 for ThreeSum.Subset.mobius_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:09.131485+00:00
-- url     : https://prove2.me/submissions/3a999a37-2fd5-42e5-9457-df71104f644e

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
theorem _root_.solution (f g : Finset α → ℤ) (q : Finset α) :
    mobius (fun s => f s + g s) q = mobius f q + mobius g q := by
  simp only [mobius, mul_add, Finset.sum_add_distrib]
end ThreeSum.Subset
