-- Prove2me | solution 1 for SoficGroups.KunActualRootedModelBridge.sourceRootedIndicatorMarkovModel_isRootedAtRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/d3cf9572-aef6-4d25-8827-fdb47844d8b7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_symmetricGeneratorWord_prod
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenCayleyRadiusBad_rooted

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
    (S : Finset G) (hone : 1 ∈ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (n r : ℕ) (T : Finset (Fin (A.model n).size))
    (hgood : Disjoint T
      (chosenCayleyRadiusBad A S
        (symmetricGeneratorWord S hsymmetric hgenerates) n r)) :
    (sourceRootedIndicatorMarkovModel
      A S hsymmetric hgenerates n T).IsRootedAtRadius
        (symmetricGeneratorWord S hsymmetric hgenerates) r := by
  refine ⟨?_⟩
  intro a g hword x hx
  have hxreal : sourceFiniteIndicator T x ≠ 0 := by
    intro hzero
    apply hx
    change (sourceFiniteIndicator T x : ℂ) = 0
    exact_mod_cast hzero
  have hxT : x ∈ T := by
    by_contra hnot
    apply hxreal
    unfold sourceFiniteIndicator
    split
    · rename_i hmem
      exact (hnot hmem).elim
    · rfl
  have hxgood := Finset.disjoint_left.mp hgood hxT
  exact chosenCayleyRadiusBad_rooted
    A S hone (symmetricGeneratorWord S hsymmetric hgenerates)
    (symmetricGeneratorWord_prod S hsymmetric hgenerates)
    n r a g hword hxgood
end SoficGroups.KunActualRootedModelBridge
