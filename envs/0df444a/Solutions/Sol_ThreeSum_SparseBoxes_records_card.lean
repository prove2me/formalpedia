-- Prove2me | solution 1 for ThreeSum.SparseBoxes.records_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:41:04.437101+00:00
-- url     : https://prove2.me/submissions/0f302399-1f77-4d71-9ec0-ca5cc8ca3f2c

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
import Theorems.Thm_ThreeSum_SparseBoxes_boundedSubsets_eq_filter

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
theorem _root_.solution (ambient : Finset α) (cut : ℕ) :
    (records ambient cut).card =
      ∑ flags ∈ ambient.powerset with flags.card ≤ cut, (flags.card + 1) := by
  simp only [records, boundedSubsets_eq_filter, Finset.card_sigma, Finset.card_range]
end ThreeSum.SparseBoxes
