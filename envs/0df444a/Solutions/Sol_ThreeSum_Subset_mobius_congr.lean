-- Prove2me | solution 1 for ThreeSum.Subset.mobius_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:17:08.133319+00:00
-- url     : https://prove2.me/submissions/6c8f7251-c79d-4eb1-a658-4e9cf59c1a2c

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
theorem _root_.solution (q : Finset α) {f g : Finset α → ℤ}
    (h : ∀ s ⊆ q, f s = g s) : mobius f q = mobius g q := by
  apply Finset.sum_congr rfl
  intro s hs
  rw [h s (Finset.mem_powerset.mp hs)]
end ThreeSum.Subset
