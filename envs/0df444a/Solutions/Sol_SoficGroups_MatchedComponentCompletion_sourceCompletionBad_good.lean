-- Prove2me | solution 1 for SoficGroups.MatchedComponentCompletion.sourceCompletionBad_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/4d1cc4da-c64b-4078-91a0-dbab175ba9a2

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentCompletion
open scoped BigOperators
namespace SoficGroups.MatchedComponentCompletion
theorem _root_.solution
    {V ι J : Type*} [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V)
    (x : V) (hx : x ∈ Z)
    (hgood : x ∉ sourceCompletionBad σ p F Z) :
    (∀ i, σ i x ∈ Z) ∧
    (∀ j ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
      p j x ∈ Z) ∧
    (∀ i, ∀ j ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
      p j (σ i x) = σ i (p j x)) ∧
    (∀ i, ∀ j ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
      p j (σ i x) ∈ Z) ∧
    (∀ j ∈ F, ∀ k ∈ F,
      p (j * k) x = p j (p k x)) ∧
    (∀ j ∈ F, ∀ k ∈ F, j ≠ k → p j x ≠ p k x) := by
  classical
  simp [sourceCompletionBad, hx] at hgood
  aesop
end SoficGroups.MatchedComponentCompletion
