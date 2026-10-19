-- Prove2me | solution 1 for SoficGroups.KunCompletedProductDiagonalSparseCut.exists_completed_goodPermutationGraph_sparse_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/ddca8578-c57e-46bd-8e1e-62ce4c1df6ee

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_exists_rooted_word_radius_sparse_cut_of_boundary
import Theorems.Thm_SoficGroups_KunCompletedProductDiagonalSparseCut_completedGoodPermutationGraphRootedModel_isGenerated
import Theorems.Thm_SoficGroups_KunCompletedProductDiagonalSparseCut_completedGoodPermutationGraphRootedModel_isRootedAtRadius

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedProductDiagonalSparseCut
open SoficGroups.KunDiagonalGoodRootGraphLoss
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
universe u
namespace SoficGroups.KunCompletedProductDiagonalSparseCut
theorem _root_.solution
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (γ α : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hγsmall :
      216 * γ <
        (S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) :
    ∃ r : ℕ,
      ∀ (V : Type u) [Fintype V] [DecidableEq V]
        (σ : ↥S → Equiv.Perm V) (φ : G → Equiv.Perm V),
      (∀ g : G, φ g = ((w g).map σ).prod) →
      φ 1 = 1 →
      (∀ i : ↥S, φ (i : G) = σ i) →
      ∀ (p : Equiv.Perm V) (B : Finset V),
      (∀ a g : G,
        (w a).length + (w g).length + (w (a * g)).length ≤ r →
          ∀ x : V, x ∉ B →
            φ (a * g) x = (φ a * φ g) x) →
      let T := goodPermutationGraph p B
      T.Nonempty →
      (SoficGroups.boundary
        (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) <
          γ * (T.card : ℝ) →
      ∃ U : Finset (V × V),
        (((U ∆ T).card : ℝ)) ≤
          72 * (SoficGroups.boundary
            (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) /
              ((S.card : ℝ) *
                (1 - kazhdanMarkovContractionFactor P S) ^ 2) ∧
        3 * (U ∆ T).card < T.card ∧
        (SoficGroups.boundary
          (fun i : ↥S => (σ i).prodCongr (σ i)) U : ℝ) ≤
            α * (U.card : ℝ) := by
  classical
  obtain ⟨k, r, hr⟩ :=
    exists_rooted_word_radius_sparse_cut_of_boundary
      P S honeS hcover hsymmetric w γ α hγ hα hγsmall
  refine ⟨r, ?_⟩
  intro V _ _ σ φ hword hone hgenerator p B hroot
  have hproductInstance :
      (instDecidableEqProd : DecidableEq (V × V)) =
        Classical.decEq (V × V) :=
    Subsingleton.elim _ _
  letI : DecidableEq (V × V) := Classical.decEq (V × V)
  dsimp only
  intro hT hboundary
  rw [hproductInstance] at hboundary ⊢
  let X : RootedIndicatorMarkovModel G ↥S :=
    completedGoodPermutationGraphRootedModel σ φ p B
  let T : Finset X.carrier := goodPermutationGraph p B
  have hgenerated : X.IsGenerated (fun i : ↥S => (i : G)) w :=
    completedGoodPermutationGraphRootedModel_isGenerated
      (fun i : ↥S => (i : G)) w σ φ
        hword hone hgenerator p B
  have hrooted : X.IsRootedAtRadius w r :=
    completedGoodPermutationGraphRootedModel_isRootedAtRadius
      w σ φ p B r hroot
  have hindicator : ∀ z : X.carrier,
      X.indicator z = if z ∈ T then (1 : ℝ) else 0 := by
    intro z
    by_cases hz : z ∈ goodPermutationGraph p B
    · have hzT : z ∈ T := hz
      rw [if_pos hzT]
      change
        completedGoodPermutationGraphIndicator
          (goodPermutationGraph p B) z = 1
      exact if_pos hz
    · have hzT : z ∉ T := hz
      rw [if_neg hzT]
      change
        completedGoodPermutationGraphIndicator
          (goodPermutationGraph p B) z = 0
      exact if_neg hz
  have hT' : T.Nonempty := hT
  have hboundary' :
      (SoficGroups.boundary X.generator T : ℝ) <
        γ * (T.card : ℝ) := by
    change
      (SoficGroups.boundary
        (fun i : ↥S => (σ i).prodCongr (σ i))
        (goodPermutationGraph p B) : ℝ) <
          γ * ((goodPermutationGraph p B).card : ℝ)
    exact hboundary
  obtain ⟨U, _hmarkov, hdistance, hclose, hcut⟩ :=
    hr X hgenerated hrooted T hT' hindicator hboundary'
  refine ⟨U, ?_, ?_, ?_⟩
  · exact hdistance
  · exact hclose
  · exact hcut
end SoficGroups.KunCompletedProductDiagonalSparseCut
