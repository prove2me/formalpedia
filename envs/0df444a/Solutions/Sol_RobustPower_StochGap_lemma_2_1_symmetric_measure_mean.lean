-- Prove2me | solution 1 for RobustPower.StochGap.lemma_2_1_symmetric_measure_mean
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T02:11:40.838778+00:00
-- url     : https://prove2.me/submissions/3907d3f3-e45b-4e88-ae40-ad056f7e71a7

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets
import Definitions.Def_RobustPower_StochGap_SymmetricMeasure

set_option autoImplicit false

open MeasureTheory

namespace RobustPower.StochGap.P2da9a127

lemma refl_invol {n : ℕ} (u₀ : Fin n → ℝ) (x : Fin n → ℝ) :
    (2 : ℝ) • u₀ - ((2 : ℝ) • u₀ - x) = x := sub_sub_cancel _ _

lemma refl_le {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (S : Set (Fin n → ℝ)) (u₀ : Fin n → ℝ)
    (hμ : IsSymmetricMeasure μ S u₀) (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    μ A ≤ μ ((fun x => (2 : ℝ) • u₀ - x) '' A) := by
  obtain ⟨-, hc, hsym⟩ := hμ
  obtain ⟨N, hNsup, hNm, hN0⟩ := exists_measurable_superset_of_null hc
  have hsub : A ∩ Nᶜ ⊆ S := by
    intro x hx
    by_contra h
    exact hx.2 (hNsup h)
  have h1 : μ A = μ (A ∩ Nᶜ) := by
    rw [← measure_inter_add_sdiff A hNm, Set.sdiff_eq]
    have : μ (A ∩ N) = 0 := measure_mono_null Set.inter_subset_right hN0
    rw [this, zero_add]
  rw [h1, hsym _ hsub (hA.inter hNm.compl)]
  exact measure_mono (Set.image_mono Set.inter_subset_left)

lemma map_eq {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (S : Set (Fin n → ℝ)) (u₀ : Fin n → ℝ)
    (hμ : IsSymmetricMeasure μ S u₀) :
    Measure.map (fun x => (2 : ℝ) • u₀ - x) μ = μ := by
  have hmeas : Measurable (fun x : Fin n → ℝ => (2 : ℝ) • u₀ - x) :=
    (continuous_const.sub continuous_id).measurable
  have himg : ∀ B : Set (Fin n → ℝ),
      (fun x => (2 : ℝ) • u₀ - x) ⁻¹' B = (fun x => (2 : ℝ) • u₀ - x) '' B := by
    intro B
    exact (congrFun (Set.image_eq_preimage_of_inverse (refl_invol u₀) (refl_invol u₀)) B).symm
  ext A hA
  rw [Measure.map_apply hmeas hA, himg]
  apply le_antisymm
  · have hA' : MeasurableSet ((fun x => (2 : ℝ) • u₀ - x) '' A) := by
      rw [← himg]; exact hmeas hA
    have := refl_le μ S u₀ hμ _ hA'
    rwa [Set.image_image, show (fun x => (2 : ℝ) • u₀ - ((2 : ℝ) • u₀ - x)) = id from
      funext (refl_invol u₀), Set.image_id] at this
  · exact refl_le μ S u₀ hμ A hA

end RobustPower.StochGap.P2da9a127

open MeasureTheory RobustPower.StochGap in
theorem solution {n : ℕ} (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (S : Set (Fin n → ℝ)) (u₀ : Fin n → ℝ)
    (hμ : IsSymmetricMeasure μ S u₀) (hint : Integrable (fun x : Fin n → ℝ => x) μ) :
    ∫ x, x ∂μ = u₀ := by
  have hmeas : Measurable (fun x : Fin n → ℝ => (2 : ℝ) • u₀ - x) :=
    (continuous_const.sub continuous_id).measurable
  have hmap := RobustPower.StochGap.P2da9a127.map_eq μ S u₀ hμ
  have h1 : ∫ x, x ∂μ = ∫ x, ((2 : ℝ) • u₀ - x) ∂μ := by
    conv_lhs => rw [← hmap]
    exact integral_map hmeas.aemeasurable aestronglyMeasurable_id
  rw [integral_sub (integrable_const _) hint, integral_const, probReal_univ, one_smul] at h1
  have h2 : (2 : ℝ) • ∫ x, x ∂μ = (2 : ℝ) • u₀ := by
    rw [two_smul]
    exact eq_sub_iff_add_eq.mp h1
  exact smul_right_injective _ two_ne_zero h2
