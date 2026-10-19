-- Prove2me | solution 1 for SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge.nonempty_expandingCentralizerFiniteModel_of_actual_selected_pruned_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/eb910127-fb02-47e0-b52e-fae60c3b91b4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdanMarkovContractionFactor_lt_one
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenWordEvaluation_multiplicative_tendsto
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_symmetricGeneratorWord_prod
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_symmetricGeneratorWord_generator
import Theorems.Thm_SoficGroups_MatchedComponentCompletion_card_subtype_sourceCompletionBad
import Theorems.Thm_SoficGroups_KunUniformCompletedRootRadiusImprovement_exists_uniform_radius_hasAlmostCentralizerImprovement
import Theorems.Thm_SoficGroups_CompletedChosenWordLocalRoot_chosenWordEvaluation_multiplicative_tendsto
import Theorems.Thm_SoficGroups_CompletedPrescribedSpectralRadiusSchedule_fixedRadiusRootBad_rooted
import Theorems.Thm_SoficGroups_CompletedPrescribedSpectralRadiusSchedule_fixedRadiusRootBad_density_tendsto_zero
import Theorems.Thm_SoficGroups_CompletedSelectedCentralizerPairwiseSource_eventually_completed_sourceCentralizer_table_of_bad_density
import Theorems.Thm_SoficGroups_KunActualSelectedCentralizerFiniteModel_nonempty_expandingCentralizerFiniteModel_of_selected_completed_sequence
import Theorems.Thm_SoficGroups_KunCombinedPrescribedRootSourceTolerance_exists_prescribed_radius_union_source_completed_tolerance
import Theorems.Thm_SoficGroups_KunActualSelectedPrunedSourceFiniteModelBridge_completed_generator_one_of_internal_agreement

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.KunActualSoficRootRadius
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge
theorem _root_.solution
    {G J : Type} [Group G] [Group J]
    [DecidableEq G]
    (P : SoficGroups.KazhdanPair.{0, 0} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (F : Finset J)
    (W : ℕ → Type)
    [∀ n, Fintype (W n)] [∀ n, DecidableEq (W n)]
    (σ : (n : ℕ) → ↥S → Equiv.Perm (W n))
    (hσone : ∀ n (i : ↥S), (i : G) = 1 → σ n i = 1)
    (p : (n : ℕ) → J → Equiv.Perm (W n))
    (hp : ∀ n, p n 1 = 1)
    (Z : (n : ℕ) → Finset (W n))
    (hZ : ∀ n, (Z n).Nonempty)
    (hlarge : Tendsto (fun n => (Z n).card) atTop atTop)
    (τ : (n : ℕ) → ↥S →
      Equiv.Perm {x : W n // x ∈ Z n})
    (hτ : ∀ n i (x : W n) (hx : x ∈ Z n)
      (_hi : σ n i x ∈ Z n),
        ((τ n i ⟨x, hx⟩ :
          {x : W n // x ∈ Z n}) : W n) = σ n i x)
    (ρ : (n : ℕ) → G →
      Equiv.Perm {x : W n // x ∈ Z n})
    (hρone : ∀ n, ρ n 1 = 1)
    (hρmul : ∀ a g : G,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (ρ n (a * g)) (ρ n a * ρ n g))
        atTop (𝓝 0))
    (hρgenerator : ∀ i : ↥S,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (τ n i) (ρ n (i : G)))
        atTop (𝓝 0))
    (ell : ℝ) (hell : 0 < ell)
    (hexp : ∀ n, ∀ E : Finset {x : W n // x ∈ Z n},
      ell * min (E.card : ℝ)
        ((Fintype.card {x : W n // x ∈ Z n} : ℝ) - E.card) ≤
          (SoficGroups.boundary (τ n) E : ℝ))
    (hbad : Tendsto
      (fun n =>
        ((SoficGroups.MatchedComponentCompletion.sourceCompletionBad
          (σ n) (p n) F (Z n)).card : ℝ) / (Z n).card)
      atTop (𝓝 0)) :
    Nonempty (SoficGroups.ExpandingCentralizerFiniteModel J F) := by
  classical
  let V : ℕ → Type := fun n => {x : W n // x ∈ Z n}
  letI (n : ℕ) : Nonempty (V n) :=
    ⟨⟨(hZ n).choose, (hZ n).choose_spec⟩⟩
  let w : G → List ↥S :=
    SoficGroups.KunActualSoficRootRadius.symmetricGeneratorWord
      S hsymmetric hgenerates
  have hw (g : G) :
      ((w g).map fun i : ↥S => (i : G)).prod = g := by
    exact SoficGroups.KunActualSoficRootRadius.symmetricGeneratorWord_prod
      S hsymmetric hgenerates g
  let φ : (n : ℕ) → G → Equiv.Perm (V n) :=
    fun n g => ((w g).map (τ n)).prod
  have hφone (n : ℕ) : φ n 1 = 1 := by
    simp [φ, w,
      SoficGroups.KunActualSoficRootRadius.symmetricGeneratorWord_one]
  have hφgenerator (n : ℕ) (i : ↥S) :
      φ n (i : G) = τ n i := by
    by_cases hi : (i : G) = 1
    · have hτone : τ n i = 1 :=
        completed_generator_one_of_internal_agreement
          S (σ n) (Z n) (τ n) (hτ n) (hσone n) i hi
      simp [φ, w, hi, hτone,
        SoficGroups.KunActualSoficRootRadius.symmetricGeneratorWord_one]
    · simp [φ, w,
        SoficGroups.KunActualSoficRootRadius.symmetricGeneratorWord_generator
          S hsymmetric hgenerates i hi]
  have hφmul (a g : G) :
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (φ n (a * g)) (φ n a * φ n g))
        atTop (𝓝 0) := by
    simpa [φ,
      SoficGroups.CompletedChosenWordLocalRoot.chosenWordEvaluation] using
      SoficGroups.CompletedChosenWordLocalRoot.chosenWordEvaluation_multiplicative_tendsto
          V ρ hρone hρmul
          (fun i : ↥S => (i : G)) w hw τ hρgenerator a g
  let root : (n : ℕ) → ℕ → Finset (V n) :=
    fun n k =>
      SoficGroups.CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad
        (φ n) S k
  have hroot (k : ℕ) :
      Tendsto
        (fun n => ((root n k).card : ℝ) / Fintype.card (V n))
        atTop (𝓝 0) := by
    exact SoficGroups.CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_density_tendsto_zero
      V φ S hφmul k
  let source : (n : ℕ) → Finset (V n) :=
    fun n => SoficGroups.MatchedComponentCompletion.subtypeBad
      (Z n)
      (SoficGroups.MatchedComponentCompletion.sourceCompletionBad
        (σ n) (p n) F (Z n))
  have hsource :
      Tendsto
        (fun n => ((source n).card : ℝ) / Fintype.card (V n))
        atTop (𝓝 0) := by
    simpa [source, V,
      SoficGroups.MatchedComponentCompletion.card_subtype_sourceCompletionBad,
      Fintype.card_coe] using hbad
  have hVpositive (n : ℕ) : 0 < Fintype.card (V n) := by
    simpa [V, Fintype.card_coe] using (hZ n).card_pos
  have hVlarge :
      Tendsto (fun n => Fintype.card (V n)) atTop atTop := by
    simpa [V, Fintype.card_coe] using hlarge
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδpositive (j : ℕ) : 0 < δ j := by
    dsimp [δ]
    positivity
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let d : ℕ := S.card
  have hd : 0 < d := by
    dsimp [d]
    exact Finset.card_pos.mpr ⟨1, honeS⟩
  let q : ℝ :=
    SoficGroups.KunThomInvariantOrthogonal.kazhdanMarkovContractionFactor P S
  have hq : q < 1 := by
    exact SoficGroups.KunThomInvariantOrthogonal.kazhdanMarkovContractionFactor_lt_one
      P S ⟨1, honeS⟩
  let α : ℕ → ℝ :=
    fun j => ell * δ j / (2 * (ell + 8 * (d : ℝ)))
  have hα (j : ℕ) : 0 < α j := by
    dsimp [α]
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  let spectral (j : ℕ) :=
    SoficGroups.KunUniformCompletedRootRadiusImprovement.exists_uniform_radius_hasAlmostCentralizerImprovement
        P S honeS hcover hsymmetric w ell (α j) hell (hα j)
  let radius : ℕ → ℕ := fun j => (spectral j).choose
  have hspectral (j : ℕ) := (spectral j).choose_spec
  let R : ℕ → ℕ := fun j => max j (radius j)
  have hR (j : ℕ) : j ≤ R j := le_max_left _ _
  obtain ⟨m, rootError, t, hm, hRm, hδm, hrelative,
      hrootError, hrootlower, hrootlimit, htdef, htpositive,
      htroot, htsource, htrooterror, htlimit, htarget,
      hsmall, hslow⟩ :=
    SoficGroups.KunCombinedPrescribedRootSourceTolerance.exists_prescribed_radius_union_source_completed_tolerance
        V hVpositive hVlarge root source hroot hsource
        δ hδpositive hδ R hR d hd ell q hell hq
  let pZ : (n : ℕ) → J → Equiv.Perm (V n) :=
    fun n j => SoficGroups.MatchedComponentCompletion.completedRestriction
      (p n j) (Z n)
  have hpZ (n : ℕ) : pZ n 1 = 1 := by
    dsimp [pZ]
    rw [hp n,
      SoficGroups.MatchedComponentCompletion.completedRestriction_one]
  have hsourcebudget (n : ℕ) :
      2 * Fintype.card (↥S) *
        (SoficGroups.MatchedComponentCompletion.sourceCompletionBad
          (σ n) (p n) F (Z n)).card ≤ t n := by
    have hbudget := htsource n
    change
      2 * S.card *
        (SoficGroups.MatchedComponentCompletion.subtypeBad
          (Z n)
          (SoficGroups.MatchedComponentCompletion.sourceCompletionBad
            (σ n) (p n) F (Z n))).card ≤ t n at hbudget
    rw [SoficGroups.MatchedComponentCompletion.card_subtype_sourceCompletionBad]
      at hbudget
    simpa only [Fintype.card_coe] using hbudget
  have htable :=
    SoficGroups.CompletedSelectedCentralizerPairwiseSource.eventually_completed_sourceCentralizer_table_of_bad_density
        W σ p F Z hZ hbad τ hτ t hsourcebudget
  have hdefect : ∀ᶠ n in atTop,
      ∀ j ∈ SoficGroups.CompressionCriterion.productTrackedTable F,
        SoficGroups.permutationCommutationDefect
          (τ n) (pZ n j) ≤ t n := by
    filter_upwards [htable] with n hn
    simpa [pZ] using hn.2.2
  have hmulJ : ∀ᶠ n in atTop,
      ∀ a ∈ F, ∀ b ∈ F,
        5 * SoficGroups.permutationDistance
          (pZ n (a * b)) (pZ n a * pZ n b) ≤
            Fintype.card (V n) := by
    filter_upwards [htable] with n hn
    simpa [pZ, V] using hn.1
  have hsepJ : ∀ᶠ n in atTop,
      ∀ a ∈ F, ∀ b ∈ F, a ≠ b →
        Fintype.card (V n) <
          5 * SoficGroups.permutationDistance (pZ n a) (pZ n b) := by
    filter_upwards [htable] with n hn
    simpa [pZ, V] using hn.2.1
  have himprove : ∀ᶠ n in atTop,
      SoficGroups.HasAlmostCentralizerImprovement (τ n) (t n) := by
    filter_upwards [hslow] with n hn
    apply hspectral (m n) (V n) (τ n) (φ n) (t n)
      (root n (R (m n)) ∪ source n)
    · intro g
      rfl
    · exact hφone n
    · exact hφgenerator n
    · exact hexp n
    · simpa [d, q] using hn
    · right
      refine ⟨by exact_mod_cast htpositive n, ?_, ?_, ?_⟩
      · simpa [α] using htarget n
      · have hbudget :
            2 * d * (root n (R (m n)) ∪ source n).card ≤ t n := by
          rw [htdef n]
          omega
        exact_mod_cast hbudget
      · intro a g hlength x hx
        have hxroot : x ∉ root n (R (m n)) := by
          intro hxroot
          exact hx (Finset.mem_union_left _ hxroot)
        have hradius : radius (m n) ≤ R (m n) := by
          exact le_max_right _ _
        exact
          SoficGroups.CompletedPrescribedSpectralRadiusSchedule.fixedRadiusRootBad_rooted
            S honeS w hw (φ n) (R (m n)) a g
            (hlength.trans hradius) x hxroot
  exact SoficGroups.KunActualSelectedCentralizerFiniteModel.nonempty_expandingCentralizerFiniteModel_of_selected_completed_sequence
      F V (↥S) τ pZ hpZ t ell hell hdefect
      (Filter.Eventually.of_forall hexp)
      hsmall himprove hmulJ hsepJ
end SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge
