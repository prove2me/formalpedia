-- Prove2me | solution 1 for ThreeSum.Subset.partialZeta_insert
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:42:10.019488+00:00
-- url     : https://prove2.me/submissions/17b4c63f-0f77-4d51-8d12-1933ff0f9d7d

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Exact subset identities used by the proposed 3SUM algorithm

This module proves the algebraic identities, rather than taking the claimed
algorithm or its running time as an assumption.  `zeta` is the ordinary finite
subset sum; `mobius` is its signed inverse.  The fixed-cardinality specialization
is the identity used by the repeated histogram construction.
-/

namespace ThreeSum.Subset

open scoped BigOperators

variable {α : Type*} [DecidableEq α]































































































































































































































































/-! ## Stored partial zeta stages -/


















/-- The exact update invariant for the ordinary coordinatewise zeta DP. -/
theorem partialZeta_insert_sourceProof (f : Finset α → ℤ) (u processed : Finset α)
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






























































































































/-! ## Prefix reporting mass -/




























































end ThreeSum.Subset

end

universe u_1

theorem solution : ∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (f : Finset.{u_1} α → Int) (u processed : Finset.{u_1} α),
  ∀ a ∉ processed,
    @Eq.{1} Int
      (@ThreeSum.Subset.partialZeta.{u_1} α inst
        (@Insert.insert.{u_1, u_1} α (Finset.{u_1} α) (@Finset.instInsert.{u_1} α inst) a processed) f u)
      (@ThreeSum.Subset.zetaStep.{u_1} α inst a (@ThreeSum.Subset.partialZeta.{u_1} α inst processed f) u) := by
  exact @ThreeSum.Subset.partialZeta_insert_sourceProof

#print axioms solution
