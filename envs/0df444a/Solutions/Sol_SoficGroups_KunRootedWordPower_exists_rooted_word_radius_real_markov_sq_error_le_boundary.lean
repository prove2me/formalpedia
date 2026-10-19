-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.exists_rooted_word_radius_real_markov_sq_error_le_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/e3a4548b-981f-40c8-834e-ba49f8395339

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdanMarkovContractionFactor_lt_one
import Theorems.Thm_SoficGroups_KunRootedWordPower_exists_rooted_word_radius_geometric_markov_displacement
import Theorems.Thm_SoficGroups_KunRootedWordPower_rooted_markov_real_iterate_sq_error
import Theorems.Thm_SoficGroups_KunRootedWordPower_rooted_indicator_defect_sq_le_boundary

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise symmDiff
universe u
attribute [local instance] SoficGroups.KunRootedWordPower.rootedSparseModelDecidableEq
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (k : ℕ) :
    ∃ r : ℕ, ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      ∀ T : Finset X.carrier,
        (∀ x : X.carrier,
          X.indicator x = if x ∈ T then (1 : ℝ) else 0) →
        (∑ x : X.carrier,
          ((((SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov
              X.generator)^[k])
            (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) x -
              if x ∈ T then (1 : ℝ) else 0) ^ 2) ≤
          8 * (SoficGroups.boundary X.generator T : ℝ) /
            ((S.card : ℝ) *
              (1 - kazhdanMarkovContractionFactor P S) ^ 2) := by
  letI : Nonempty (↥S) := ⟨⟨1, honeS⟩⟩
  let q := kazhdanMarkovContractionFactor P S
  have hgap : 0 < 1 - q :=
    sub_pos.mpr
      (kazhdanMarkovContractionFactor_lt_one P S ⟨1, honeS⟩)
  have hdegree : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, honeS⟩
  obtain ⟨r, hr⟩ :=
    exists_rooted_word_radius_geometric_markov_displacement
      P S honeS hcover hsymmetric w k
  refine ⟨r, ?_⟩
  intro X hgenerated hroot T hindicator
  let χ : X.carrier → ℝ :=
    SoficGroups.KunFinitePermutationMarkovMass.realIndicator T
  have hχ : X.indicator = χ := by
    funext x
    simpa [χ,
      SoficGroups.KunFinitePermutationMarkovMass.realIndicator]
      using hindicator x
  have hgeo := hr X hgenerated hroot
  rw [hχ] at hgeo
  have hjensen :
      ‖permutationMarkov X.generator (indicatorVector χ) -
        indicatorVector χ‖ ^ 2 ≤
        2 * (SoficGroups.boundary X.generator T : ℝ) /
          (S.card : ℝ) := by
    simpa [χ, Fintype.card_coe] using
      rooted_indicator_defect_sq_le_boundary X.generator T
  have hcoef : 0 ≤ 2 / (1 - q) :=
    div_nonneg (by norm_num) hgap.le
  have hsquare :
      ‖((permutationMarkov X.generator)^[k])
          (indicatorVector χ) - indicatorVector χ‖ ^ 2 ≤
        (2 / (1 - q)) ^ 2 *
          ‖permutationMarkov X.generator (indicatorVector χ) -
            indicatorVector χ‖ ^ 2 := by
    calc
      ‖((permutationMarkov X.generator)^[k])
          (indicatorVector χ) - indicatorVector χ‖ ^ 2 ≤
        ((2 / (1 - q)) *
          ‖permutationMarkov X.generator (indicatorVector χ) -
            indicatorVector χ‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg hcoef (norm_nonneg _))).mpr hgeo
      _ = (2 / (1 - q)) ^ 2 *
          ‖permutationMarkov X.generator (indicatorVector χ) -
            indicatorVector χ‖ ^ 2 := by
        rw [mul_pow]
  rw [← rooted_markov_real_iterate_sq_error X.generator T k]
  change
    ‖((permutationMarkov X.generator)^[k])
        (indicatorVector χ) - indicatorVector χ‖ ^ 2 ≤
      8 * (SoficGroups.boundary X.generator T : ℝ) /
        ((S.card : ℝ) * (1 - q) ^ 2)
  calc
    ‖((permutationMarkov X.generator)^[k])
        (indicatorVector χ) - indicatorVector χ‖ ^ 2 ≤
      (2 / (1 - q)) ^ 2 *
        ‖permutationMarkov X.generator (indicatorVector χ) -
          indicatorVector χ‖ ^ 2 := hsquare
    _ ≤ (2 / (1 - q)) ^ 2 *
        (2 * (SoficGroups.boundary X.generator T : ℝ) /
          (S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hjensen (sq_nonneg _)
    _ = 8 * (SoficGroups.boundary X.generator T : ℝ) /
        ((S.card : ℝ) * (1 - q) ^ 2) := by
      field_simp
      ring
end SoficGroups.KunRootedWordPower
