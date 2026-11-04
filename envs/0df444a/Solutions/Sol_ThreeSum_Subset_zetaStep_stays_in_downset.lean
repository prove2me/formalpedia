-- Prove2me | solution 1 for ThreeSum.Subset.zetaStep_stays_in_downset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:18.967825+00:00
-- url     : https://prove2.me/submissions/44675317-7bf8-46af-95bd-a017786f3a76

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
theorem _root_.solution
    (u : Finset α) (a : α) (mu : ℕ) (h : u.card ≤ mu) :
    (u.erase a).card ≤ mu := by
  exact (Finset.card_le_card (Finset.erase_subset a u)).trans h
end ThreeSum.Subset
