-- Prove2me | solution 1 for ThreeSum.Subset.zeta_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:17:06.992692+00:00
-- url     : https://prove2.me/submissions/12c651ad-b838-4cea-9972-fe394fb4076b

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
theorem _root_.solution (f : Finset α → ℤ) {q : Finset α} {a : α}
    (ha : a ∉ q) :
    zeta f (insert a q) = zeta f q + zeta (fun s => f (insert a s)) q := by
  exact Finset.sum_powerset_insert ha f
end ThreeSum.Subset
