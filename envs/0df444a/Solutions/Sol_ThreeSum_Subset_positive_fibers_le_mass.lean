-- Prove2me | solution 1 for ThreeSum.Subset.positive_fibers_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:23.127616+00:00
-- url     : https://prove2.me/submissions/0e3e3663-12b9-4ec8-ac7c-1eaf27ce5a4b

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
import Theorems.Thm_ThreeSum_Subset_fiberMass_conservation

set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (labels : Finset γ) (label : β → γ) (weight : β → ℕ)
    (hlabels : ∀ p ∈ domain, label p ∈ labels) :
    (labels.filter (fun value => 0 < fiberMass domain label weight value)).card ≤
      ∑ p ∈ domain, weight p := by
  rw [← fiberMass_conservation domain labels label weight hlabels]
  calc
    _ = ∑ value ∈ labels, if 0 < fiberMass domain label weight value then 1 else 0 := by
      simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro value hvalue
      split_ifs with h
      · omega
      · exact Nat.zero_le _
end ThreeSum.Subset
