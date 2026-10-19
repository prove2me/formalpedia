-- Prove2me | solution 1 for SoficGroups.KunActualCanonicalSelectedFiniteModelComposition.nonempty_expandingCentralizerFiniteModel_of_canonical_selected_additive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/b4c57769-5d38-4df1-8d2b-dfba0f83fb6b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CompletedSourceFinalGeneratorTransfer_twiceCompleted_sourceGenerator_normalizedHamming_tendsto_zero
import Theorems.Thm_SoficGroups_KunActualCanonicalSelectedPruning_exists_actual_uniformly_expanding_pruned_selected_components
import Theorems.Thm_SoficGroups_KunActualCanonicalPrunedSourceBadDensity_pruned_sourceCompletionBad_density_tendsto_zero_of_canonical_matched
import Theorems.Thm_SoficGroups_KunActualTwicePrunedFirstFactorRootBad_twiceCompleted_firstFactor_mul_normalizedHamming_tendsto_zero_of_canonical_matched
import Theorems.Thm_SoficGroups_KunActualSelectedPrunedSourceFiniteModelBridge_nonempty_expandingCentralizerFiniteModel_of_actual_selected_pruned_source

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualCanonicalSelectedFiniteModelComposition
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
namespace SoficGroups.KunActualCanonicalSelectedFiniteModelComposition
theorem _root_.solution
    {K J : Type} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (P : SoficGroups.KazhdanPair.{0, 0} K)
    (S : Finset K) (hone : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (ν : ℕ → ℕ)
    (Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    (C : (n : ℕ) → Finset (Fin (A.model (ν n)).size))
    (hC : ∀ n, C n ∈ (Q n).parts)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (hmatched : Tendsto
      (fun n =>
        (((C n ∩ SoficGroups.matchedRadiusBad
          (Q n) (sourceProductRadiusLabels S F (r n))
          ((A.model (ν n)).action)
          (canonicalProductRadiusBad
            A S hsymmetric hgenerates F (ν n) (r n))).card : ℝ) /
            (C n).card))
      atTop (𝓝 0))
    (hlarge : Tendsto (fun n => (C n).card) atTop atTop)
    (γ : ℝ) (hγ : 0 < γ)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (hadd : ∀ n,
      ∀ E : Finset {x : Fin (A.model (ν n)).size // x ∈ C n},
        γ * min (E.card : ℝ)
            ((Fintype.card
              {x : Fin (A.model (ν n)).size // x ∈ C n} : ℝ) -
              E.card) -
          a n * Fintype.card
            {x : Fin (A.model (ν n)).size // x ∈ C n} ≤
          (SoficGroups.boundary
            (fun i : ↥S =>
              completedRestriction
                ((A.model (ν n)).action ((i : K), (1 : J)))
                (C n)) E : ℝ)) :
    Nonempty (SoficGroups.ExpandingCentralizerFiniteModel J F) := by
  classical
  obtain ⟨N, D, τ, hZ, hdeleted, hZlarge, hagrees, hexp⟩ :=
    SoficGroups.KunActualCanonicalSelectedPruning.exists_actual_uniformly_expanding_pruned_selected_components
      A S ν Q C hC hlarge γ hγ a ha hadd
  let ν' : ℕ → ℕ := fun n => ν (n + N)
  let Q' : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν' n)).size)) :=
    fun n => Q (n + N)
  let C' : (n : ℕ) → Finset (Fin (A.model (ν' n)).size) :=
    fun n => C (n + N)
  let r' : ℕ → ℕ := fun n => r (n + N)
  have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
    tendsto_add_atTop_nat N
  have hC' (n : ℕ) : C' n ∈ (Q' n).parts := hC (n + N)
  have hr' : Tendsto r' atTop atTop := by
    exact hr.comp hshift
  have hmatched' : Tendsto
      (fun n =>
        (((C' n ∩ SoficGroups.matchedRadiusBad
          (Q' n) (sourceProductRadiusLabels S F (r' n))
          ((A.model (ν' n)).action)
          (canonicalProductRadiusBad
            A S hsymmetric hgenerates F (ν' n) (r' n))).card : ℝ) /
            (C' n).card))
      atTop (𝓝 0) := by
    exact hmatched.comp hshift
  let W : ℕ → Type :=
    fun n => {x : Fin (A.model (ν' n)).size // x ∈ C' n}
  let Z : (n : ℕ) → Finset (W n) :=
    fun n => Finset.univ \ D n
  let σ : (n : ℕ) → ↥S → Equiv.Perm (W n) :=
    fun n i => completedRestriction
      ((A.model (ν' n)).action ((i : K), (1 : J))) (C' n)
  let p : (n : ℕ) → J → Equiv.Perm (W n) :=
    fun n j => completedRestriction
      ((A.model (ν' n)).action ((1 : K), j)) (C' n)
  let ρ : (n : ℕ) → K →
      Equiv.Perm {x : W n // x ∈ Z n} :=
    fun n g => completedRestriction
      (completedRestriction
        ((A.model (ν' n)).action (g, (1 : J))) (C' n))
      (Z n)
  have hσone (n : ℕ) (i : ↥S) (hi : (i : K) = 1) :
      σ n i = 1 := by
    dsimp [σ]
    rw [hi]
    change completedRestriction
      ((A.model (ν' n)).action (1 : K × J)) (C' n) = 1
    rw [(A.model (ν' n)).map_one, completedRestriction_one]
  have hp (n : ℕ) : p n 1 = 1 := by
    dsimp [p]
    change completedRestriction
      ((A.model (ν' n)).action (1 : K × J)) (C' n) = 1
    rw [(A.model (ν' n)).map_one, completedRestriction_one]
  have hρone (n : ℕ) : ρ n 1 = 1 := by
    dsimp [ρ]
    change completedRestriction
      (completedRestriction
        ((A.model (ν' n)).action (1 : K × J)) (C' n))
      (Z n) = 1
    rw [(A.model (ν' n)).map_one,
      completedRestriction_one, completedRestriction_one]
  have hρmul (b g : K) :
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (ρ n (b * g)) (ρ n b * ρ n g))
        atTop (𝓝 0) := by
    exact SoficGroups.KunActualTwicePrunedFirstFactorRootBad.twiceCompleted_firstFactor_mul_normalizedHamming_tendsto_zero_of_canonical_matched
      A S hone hsymmetric hgenerates F ν' Q' C' hC'
      r' hr' hmatched' D hZ hdeleted b g
  have hagrees' : ∀ n (i : ↥S)
      (x : {y : W n // y ∈ Z n}),
        completedRestriction
            ((A.model (ν' n)).action ((i : K), (1 : J)))
            (C' n) x.val ∈ Z n →
          (τ n i x).val =
            completedRestriction
              ((A.model (ν' n)).action ((i : K), (1 : J)))
              (C' n) x.val := by
    intro n i x hx
    exact hagrees n i x.val x.property hx
  have hρgenerator (i : ↥S) :
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (τ n i) (ρ n (i : K)))
        atTop (𝓝 0) := by
    exact SoficGroups.CompletedSourceFinalGeneratorTransfer.twiceCompleted_sourceGenerator_normalizedHamming_tendsto_zero
      (fun n => Fin (A.model (ν' n)).size)
      (fun n (j : ↥S) =>
        (A.model (ν' n)).action ((j : K), (1 : J)))
      (fun n (g : K) =>
        (A.model (ν' n)).action (g, (1 : J)))
      (fun j : ↥S => (j : K)) C' D τ
      (fun _ _ => rfl) hagrees' hZ hdeleted i
  have hsource : Tendsto
      (fun n =>
        ((sourceCompletionBad (σ n) (p n) F (Z n)).card : ℝ) /
          (Z n).card)
      atTop (𝓝 0) := by
    exact SoficGroups.KunActualCanonicalPrunedSourceBadDensity.pruned_sourceCompletionBad_density_tendsto_zero_of_canonical_matched
      A S hsymmetric hgenerates F ν' Q' C' hC'
      r' hmatched' D hZ hdeleted
  have hhalf : 0 < γ / 2 := by positivity
  exact SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge.nonempty_expandingCentralizerFiniteModel_of_actual_selected_pruned_source
    P S hone hcover hsymmetric hgenerates F W σ hσone
    p hp Z hZ hZlarge τ hagrees ρ hρone hρmul hρgenerator
    (γ / 2) hhalf hexp hsource
end SoficGroups.KunActualCanonicalSelectedFiniteModelComposition
