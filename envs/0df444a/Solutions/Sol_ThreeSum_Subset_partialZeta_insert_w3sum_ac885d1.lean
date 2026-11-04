-- Prove2me | solution 1 for ThreeSum.Subset.partialZeta_insert_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:15.773221+00:00
-- url     : https://prove2.me/submissions/0d16b294-701a-4503-a4c4-d2d372cec607

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
theorem _root_.solution (f : Finset α → ℤ) (u processed : Finset α)
    (a : α) (ha : a ∉ processed) :
    partialZeta (insert a processed) f u =
      zetaStep a (partialZeta processed f) u := by
  by_cases hau : a ∈ u
  · have hi : u ∩ insert a processed = insert a (u ∩ processed) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      aesop
    have he : u.erase a ∩ processed = u ∩ processed := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase]
      aesop
    have hd : u.erase a \ processed = u \ insert a processed := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      aesop
    have hterm (x : Finset α) :
        (u \ insert a processed) ∪ insert a x = (u \ processed) ∪ x := by
      ext b
      by_cases hba : b = a
      · subst b
        simp [hau, ha]
      · simp [hba]
    have hai : a ∉ u ∩ processed := by simp [ha]
    rw [partialZeta, hi, Finset.sum_powerset_insert hai]
    simp only [zetaStep, hau, ite_true]
    have hfirst :
        (∑ x ∈ (u ∩ processed).powerset, f ((u \ insert a processed) ∪ x)) =
        partialZeta processed f (u.erase a) := by
      simp only [partialZeta, he, hd]
    have hsecond :
        (∑ x ∈ (u ∩ processed).powerset,
          f ((u \ insert a processed) ∪ insert a x)) =
        partialZeta processed f u := by
      simp only [partialZeta, hterm]
    rw [hfirst, hsecond, add_comm]
  · have hi : u ∩ insert a processed = u ∩ processed := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      aesop
    have hd : u \ insert a processed = u \ processed := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    simp only [partialZeta, hi, hd, zetaStep, hau, ite_false]
end ThreeSum.Subset
