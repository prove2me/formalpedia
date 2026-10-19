-- Prove2me | solution 1 for SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_sparse_cut_at_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/a83741be-3cfe-440f-9a0b-bc447489f89c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualRootedModelBridge_sourceRootedIndicatorMarkovModel_isGenerated
import Theorems.Thm_SoficGroups_KunActualRootedModelBridge_sourceRootedIndicatorMarkovModel_isRootedAtRadius
import Theorems.Thm_SoficGroups_KunRootedWordPower_exists_rooted_word_radius_sparse_cut_of_boundary

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSourceUnconditionalFullDecomposition
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunActualRootedModelBridge
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
namespace SoficGroups.KunSourceUnconditionalFullDecomposition
theorem _root_.solution
    {G : Type} [Group G] [DecidableEq G]
    (P : SoficGroups.KazhdanPair.{0, 0} G)
    (S : Finset G) (hone : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (γ α : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hsmall :
      216 * γ <
        (S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) :
    ∃ r : ℕ,
      ∀ (A : SoficGroups.SoficApproximation G) (n : ℕ)
        (T : Finset (Fin (A.model n).size)),
      Disjoint T
        (chosenCayleyRadiusBad A S
          (symmetricGeneratorWord S hsymmetric hgenerates) n r) →
      (SoficGroups.boundary
        (fun i : ↥S => (A.model n).action (i : G)) T : ℝ) <
          γ * (T.card : ℝ) →
      ∃ U : Finset (Fin (A.model n).size),
        3 * (U ∆ T).card < T.card ∧
          (SoficGroups.boundary
            (fun i : ↥S => (A.model n).action (i : G)) U : ℝ) ≤
              α * (U.card : ℝ) := by
  classical
  obtain ⟨k, r, hr⟩ :=
    exists_rooted_word_radius_sparse_cut_of_boundary
      P S hone hcover hsymmetric
      (symmetricGeneratorWord S hsymmetric hgenerates)
      γ α hγ hα hsmall
  refine ⟨r, ?_⟩
  intro A n T hgood hboundary
  have hvertexInstance :
      (instDecidableEqFin (A.model n).size :
        DecidableEq (Fin (A.model n).size)) =
          Classical.decEq (Fin (A.model n).size) :=
    Subsingleton.elim _ _
  letI : DecidableEq (Fin (A.model n).size) :=
    Classical.decEq (Fin (A.model n).size)
  rw [hvertexInstance] at hboundary ⊢
  have hT : T.Nonempty := by
    by_contra hnot
    have hempty : T = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnot
    subst T
    simp [SoficGroups.boundary] at hboundary
  let X :=
    sourceRootedIndicatorMarkovModel
      A S hsymmetric hgenerates n T
  have hgenerated :
      X.IsGenerated (fun i : ↥S => (i : G))
        (symmetricGeneratorWord S hsymmetric hgenerates) :=
    sourceRootedIndicatorMarkovModel_isGenerated
      A S hsymmetric hgenerates n T
  have hrooted :
      X.IsRootedAtRadius
        (symmetricGeneratorWord S hsymmetric hgenerates) r :=
    sourceRootedIndicatorMarkovModel_isRootedAtRadius
      A S hone hsymmetric hgenerates n r T hgood
  have hboundary' :
      (SoficGroups.boundary X.generator T : ℝ) <
        γ * (T.card : ℝ) := by
    change
      (SoficGroups.boundary
        (fun i : ↥S => (A.model n).action (i : G)) T : ℝ) <
          γ * (T.card : ℝ)
    exact hboundary
  obtain ⟨U, _hmarkov, _hreference, hclose, hcut⟩ :=
    hr X hgenerated hrooted T hT
      (by
        intro x
        dsimp only [X, sourceRootedIndicatorMarkovModel,
          sourceFiniteIndicator]
        split
        next hleft =>
          split
          next => rfl
          next hright =>
            exfalso
            apply hright
            exact Finset.mem_def.mpr (Finset.mem_def.mp hleft)
        next hleft =>
          split
          next hright =>
            exfalso
            apply hleft
            exact Finset.mem_def.mpr (Finset.mem_def.mp hright)
          next => rfl)
      hboundary'
  exact ⟨U, hclose, hcut⟩
end SoficGroups.KunSourceUnconditionalFullDecomposition
