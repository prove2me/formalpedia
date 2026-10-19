-- Prove2me | solution 1 for SoficGroups.KunActualRootedModelBridge.sourceRootedIndicatorMarkovModel_isGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/184c1f78-7549-42d2-aeee-7ac95c0049e9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosen_symmetric_wordEvaluation_one
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosen_symmetric_wordEvaluation_generator

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualRootedModelBridge
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators
universe u
namespace SoficGroups.KunActualRootedModelBridge
theorem _root_.solution
    {G : Type} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (n : ℕ) (T : Finset (Fin (A.model n).size)) :
    (sourceRootedIndicatorMarkovModel
      A S hsymmetric hgenerates n T).IsGenerated
        (fun i : ↥S => (i : G))
        (symmetricGeneratorWord S hsymmetric hgenerates) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    change sourceFiniteIndicator T x = 0 ∨
      sourceFiniteIndicator T x = 1
    by_cases hx : x ∈ T
    · right
      unfold sourceFiniteIndicator
      split
      · rfl
      · rename_i hnot
        exact (hnot hx).elim
    · left
      unfold sourceFiniteIndicator
      split
      · rename_i hmem
        exact (hx hmem).elim
      · rfl
  · intro g
    rfl
  · exact chosen_symmetric_wordEvaluation_one
      A S hsymmetric hgenerates n
  · intro i
    exact chosen_symmetric_wordEvaluation_generator
      A S hsymmetric hgenerates n i
end SoficGroups.KunActualRootedModelBridge
