-- Prove2me | solution 1 for ThreeSum.Subset.forced_prefix_stays_in_downset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:17.871119+00:00
-- url     : https://prove2.me/submissions/343d990c-9b2c-4d9f-8d15-f1719d27740c

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
    (s₀ t : Finset α) (mu : ℕ) (h : s₀.card + t.card ≤ mu) :
    (s₀ ∪ t).card ≤ mu := by
  exact (Finset.card_union_le s₀ t).trans h
end ThreeSum.Subset
