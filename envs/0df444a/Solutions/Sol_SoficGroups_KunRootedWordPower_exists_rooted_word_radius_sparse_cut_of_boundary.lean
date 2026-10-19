-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.exists_rooted_word_radius_sparse_cut_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/70cf3308-3858-4e28-bf7c-02b814da1d76

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdanMarkovContractionFactor_lt_one
import Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_kazhdanMarkovContractionFactor_nonneg
import Theorems.Thm_SoficGroups_KunRootedWordPower_exists_rooted_word_radius_markov_iterate_contraction
import Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_sum_realPermutationMarkov_iterate_indicator
import Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_realPermutationMarkov_iterate_indicator_mem_unitInterval
import Theorems.Thm_SoficGroups_KunRootedWordPower_RootedIndicatorMarkovModel_IsRootedAtRadius_mono
import Theorems.Thm_SoficGroups_KunRootedWordPower_rooted_indicator_defect_sq_le_boundary
import Theorems.Thm_SoficGroups_KunSharpThresholdCut_exists_upperLevel_boundary_and_symmDiff_le
import Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_highSupport_variation_le_of_realMarkov_residual
import Theorems.Thm_SoficGroups_KunRootedWordPower_exists_rooted_word_radius_real_markov_sq_error_le_boundary
import Theorems.Thm_SoficGroups_KunRootedWordPower_rooted_real_markov_iterate_residual_sqrt_eq

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
    (γ α : ℝ) (_hγ : 0 < γ) (hα : 0 < α)
    (hγsmall :
      216 * γ <
        (S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) :
    ∃ (k r : ℕ), ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      ∀ T : Finset X.carrier,
        T.Nonempty →
        (∀ x : X.carrier,
          X.indicator x = if x ∈ T then (1 : ℝ) else 0) →
        (SoficGroups.boundary X.generator T : ℝ) <
          γ * (T.card : ℝ) →
        ∃ U : Finset X.carrier,
          (((U ∆ T).card : ℝ)) ≤
            9 * (∑ x : X.carrier,
              ((((SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov
                X.generator)^[k])
                  (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) x -
                if x ∈ T then (1 : ℝ) else 0) ^ 2) ∧
          (((U ∆ T).card : ℝ)) ≤
            72 * (SoficGroups.boundary X.generator T : ℝ) /
              ((S.card : ℝ) *
                (1 - kazhdanMarkovContractionFactor P S) ^ 2) ∧
          3 * (U ∆ T).card < T.card ∧
          (SoficGroups.boundary X.generator U : ℝ) ≤
            α * (U.card : ℝ) := by
  classical
  letI : Nonempty (↥S) := ⟨⟨1, honeS⟩⟩
  let q := kazhdanMarkovContractionFactor P S
  have hqzero : 0 ≤ q :=
    kazhdanMarkovContractionFactor_nonneg P S
  have hqone : q < 1 :=
    kazhdanMarkovContractionFactor_lt_one P S ⟨1, honeS⟩
  have hgap : 0 < 1 - q := sub_pos.mpr hqone
  have hdegree : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, honeS⟩
  let η : ℝ := 4 * α ^ 2 / (486 * (S.card : ℝ) ^ 2)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hη hqone
  let ε : ℝ := (η - q ^ k) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨rnear, hnear⟩ :=
    exists_rooted_word_radius_real_markov_sq_error_le_boundary
      P S honeS hcover hsymmetric w k
  obtain ⟨rfinal, hfinal⟩ :=
    exists_rooted_word_radius_markov_iterate_contraction
      P S honeS hcover hsymmetric w k ε hε
  refine ⟨k, max rnear rfinal, ?_⟩
  intro X hgenerated hroot T hT hindicator hboundary
  have hrootnear := hroot.mono (le_max_left rnear rfinal)
  have hrootfinal := hroot.mono (le_max_right rnear rfinal)
  let χ : X.carrier → ℝ :=
    SoficGroups.KunFinitePermutationMarkovMass.realIndicator T
  let f : X.carrier → ℝ :=
    ((SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov
      X.generator)^[k]) χ
  let b : ℝ :=
    ‖permutationMarkov X.generator (indicatorVector χ) -
      indicatorVector χ‖
  have hχ : X.indicator = χ := by
    funext x
    simpa [χ,
      SoficGroups.KunFinitePermutationMarkovMass.realIndicator]
      using hindicator x
  have hD :
      (∑ x : X.carrier,
        (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2) ≤
        8 * (SoficGroups.boundary X.generator T : ℝ) /
          ((S.card : ℝ) * (1 - q) ^ 2) := by
    simpa [f, χ, q] using
      hnear X hgenerated hrootnear T hindicator
  have hstep := hfinal X hgenerated hrootfinal
  rw [hχ] at hstep
  have hresidual :
      Real.sqrt
        (∑ x : X.carrier,
          (SoficGroups.KunActualFinalRestrictedVariation.realMarkov
            X.generator f x - f x) ^ 2) ≤ η * b := by
    calc
      Real.sqrt
          (∑ x : X.carrier,
            (SoficGroups.KunActualFinalRestrictedVariation.realMarkov
              X.generator f x - f x) ^ 2) =
          ‖((permutationMarkov X.generator)^[k + 1])
              (indicatorVector χ) -
            ((permutationMarkov X.generator)^[k])
              (indicatorVector χ)‖ := by
            simpa [f, χ] using
              rooted_real_markov_iterate_residual_sqrt_eq
                X.generator T k
      _ ≤ (q ^ k + ε) * b := hstep
      _ ≤ η * b := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp [ε]
        linarith
  have hfzero : ∀ x : X.carrier, 0 ≤ f x := by
    intro x
    exact (SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_iterate_indicator_mem_unitInterval
      X.generator T k x).1
  have hfone : ∀ x : X.carrier, f x ≤ 1 := by
    intro x
    exact (SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov_iterate_indicator_mem_unitInterval
      X.generator T k x).2
  have hmass : (∑ x : X.carrier, f x) = (T.card : ℝ) :=
    SoficGroups.KunFinitePermutationMarkovMass.sum_realPermutationMarkov_iterate_indicator
      X.generator T k
  have hjensen :
      b ^ 2 ≤
        2 * (SoficGroups.boundary X.generator T : ℝ) /
          (S.card : ℝ) := by
    simpa [b, χ, Fintype.card_coe] using
      rooted_indicator_defect_sq_le_boundary X.generator T
  have hgaple : 1 - q ≤ 1 := by linarith
  have hgapzero : 0 ≤ 1 - q := hgap.le
  have hgap_sq_le_one : (1 - q) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (1 - q)]
  have hgamma_degree : 2 * γ ≤ (S.card : ℝ) := by
    have hsmalldegree :
        (S.card : ℝ) * (1 - q) ^ 2 ≤ (S.card : ℝ) := by
      nlinarith [mul_nonneg hdegree.le
        (sub_nonneg.mpr hgap_sq_le_one)]
    change 216 * γ < (S.card : ℝ) * (1 - q) ^ 2
      at hγsmall
    nlinarith only [hγsmall, hsmalldegree, _hγ]
  have hbase : b ^ 2 ≤ (T.card : ℝ) := by
    refine hjensen.trans ?_
    apply (div_le_iff₀ hdegree).2
    have hscaled :=
      mul_le_mul_of_nonneg_right hgamma_degree
        (Nat.cast_nonneg T.card)
    have hboundary' :=
      mul_le_mul_of_nonneg_left hboundary.le
        (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hscaled, hboundary']
  have hsmall :
      486 * (Fintype.card (↥S) : ℝ) ^ 2 * η ≤
        4 * α ^ 2 := by
    dsimp [η]
    rw [Fintype.card_coe]
    field_simp
    exact le_rfl
  have hvariation :=
    SoficGroups.KunActualFinalRestrictedVariation.highSupport_variation_le_of_realMarkov_residual
      X.generator T f α η b hfzero hfone hmass
        hα.le hη.le hbase hresidual hsmall
  obtain ⟨t, _ht, hcut, hdistance⟩ :=
    SoficGroups.KunSharpThresholdCut.exists_upperLevel_boundary_and_symmDiff_le
      X.generator T f
  let U : Finset X.carrier :=
    SoficGroups.KunSharpThresholdCut.upperLevel f t
  have hquant :
      (((U ∆ T).card : ℝ)) ≤
        72 * (SoficGroups.boundary X.generator T : ℝ) /
          ((S.card : ℝ) * (1 - q) ^ 2) := by
    calc
      (((U ∆ T).card : ℝ)) ≤
          9 * ∑ x : X.carrier,
            (f x - if x ∈ T then (1 : ℝ) else 0) ^ 2 :=
        hdistance
      _ ≤ 9 *
          (8 * (SoficGroups.boundary X.generator T : ℝ) /
            ((S.card : ℝ) * (1 - q) ^ 2)) :=
        mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = 72 * (SoficGroups.boundary X.generator T : ℝ) /
          ((S.card : ℝ) * (1 - q) ^ 2) := by ring
  have hTpos : 0 < (T.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hdenom :
      0 < (S.card : ℝ) * (1 - q) ^ 2 :=
    mul_pos hdegree (sq_pos_of_pos hgap)
  have hscaled :
      216 * (SoficGroups.boundary X.generator T : ℝ) <
        ((S.card : ℝ) * (1 - q) ^ 2) * (T.card : ℝ) := by
    calc
      216 * (SoficGroups.boundary X.generator T : ℝ) <
        216 * (γ * (T.card : ℝ)) :=
        mul_lt_mul_of_pos_left hboundary (by norm_num)
      _ = (216 * γ) * (T.card : ℝ) := by ring
      _ < ((S.card : ℝ) * (1 - q) ^ 2) * (T.card : ℝ) :=
        mul_lt_mul_of_pos_right hγsmall hTpos
  have hclose_real :
      (3 : ℝ) * (((U ∆ T).card : ℝ)) < (T.card : ℝ) := by
    calc
      (3 : ℝ) * (((U ∆ T).card : ℝ)) ≤
          216 * (SoficGroups.boundary X.generator T : ℝ) /
            ((S.card : ℝ) * (1 - q) ^ 2) := by
        calc
          (3 : ℝ) * (((U ∆ T).card : ℝ)) ≤
            3 * (72 * (SoficGroups.boundary X.generator T : ℝ) /
              ((S.card : ℝ) * (1 - q) ^ 2)) :=
            mul_le_mul_of_nonneg_left hquant (by norm_num)
          _ = 216 * (SoficGroups.boundary X.generator T : ℝ) /
              ((S.card : ℝ) * (1 - q) ^ 2) := by ring
      _ < (T.card : ℝ) :=
        (div_lt_iff₀ hdenom).2 (by nlinarith only [hscaled])
  have hclose : 3 * (U ∆ T).card < T.card := by
    exact_mod_cast hclose_real
  have hsub : T ⊆ U ∪ (U ∆ T) := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Finset.mem_union.mpr (Or.inl hxU)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_symmDiff.mpr (Or.inr ⟨hx, hxU⟩)))
  have hcard : T.card ≤ U.card + (U ∆ T).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le U (U ∆ T))
  have hcardreal :
      (T.card : ℝ) ≤ (U.card : ℝ) + (((U ∆ T).card : ℝ)) := by
    exact_mod_cast hcard
  have hlarge :
      2 * (T.card : ℝ) ≤ 3 * (U.card : ℝ) := by
    linarith only [hcardreal, hclose_real]
  have hscaledlarge :=
    mul_le_mul_of_nonneg_left hlarge hα.le
  have hboundaryU :
      (SoficGroups.boundary X.generator U : ℝ) ≤
        α * (U.card : ℝ) := by
    change
      (SoficGroups.boundary X.generator
        (SoficGroups.KunSharpThresholdCut.upperLevel f t) : ℝ) ≤ _
    nlinarith only [hcut, hvariation, hscaledlarge]
  exact ⟨U, by simpa [f, χ] using hdistance,
    by simpa [q] using hquant, hclose, hboundaryU⟩
end SoficGroups.KunRootedWordPower
