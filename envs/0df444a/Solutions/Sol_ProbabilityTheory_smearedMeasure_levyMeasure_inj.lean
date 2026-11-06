-- Prove2me | solution 1 for ProbabilityTheory.smearedMeasure_levyMeasure_inj
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:51:54.711211+00:00
-- url     : https://prove2.me/submissions/7004df61-5d30-4dfc-9dbc-a494afe9accf

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_zero_singleton
import Theorems.Thm_ProbabilityTheory_measurable_one_sub_sinc
import Theorems.Thm_ProbabilityTheory_one_sub_sinc_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The sinc-weighted Levy measure has no atom at zero. -/
private lemma chat13_density_singleton_zero {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    (ν.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x)) {(0 : ℝ)} = 0 := by
  rw [withDensity_apply _ (measurableSet_singleton 0),
    setLIntegral_measure_zero _ _ hν.zero_singleton]

/-- Restricting off zero removes the Gaussian atom and preserves the jump density. -/
private lemma chat13_restrict_compl (σ_sq : ℝ≥0) {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    (smearedMeasure σ_sq ν).restrict {(0 : ℝ)}ᶜ
      = ν.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x) := by
  classical
  rw [smearedMeasure, Measure.restrict_add, Measure.restrict_smul, restrict_dirac,
    if_neg (by simp), smul_zero, zero_add]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff, show {a : ℝ | a ∉ {(0 : ℝ)}ᶜ} = {(0 : ℝ)} from by ext a; simp]
  exact chat13_density_singleton_zero hν

/-- Dividing out the positive sinc density recovers the Levy measure. -/
private lemma chat13_untilt {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    (ν.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x)).withDensity
      (fun x => (ENNReal.ofReal (1 - Real.sinc x))⁻¹) = ν := by
  have hne0 : ∀ᵐ x ∂ν, x ≠ 0 := by
    rw [ae_iff]; simpa using hν.zero_singleton
  refine withDensity_inv_same measurable_one_sub_sinc ?_ ?_
  · filter_upwards [hne0] with x hx
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact one_sub_sinc_pos hx
  · filter_upwards with x using ENNReal.ofReal_ne_top

/-- The jump measure can be recovered uniquely from the smeared measure. -/
theorem solution :
    ∀ {ν₁ ν₂ : Measure ℝ}, IsLevyMeasure ν₁ → IsLevyMeasure ν₂ →
      ∀ {σ₁ σ₂ : ℝ≥0}, smearedMeasure σ₁ ν₁ = smearedMeasure σ₂ ν₂ → ν₁ = ν₂ := by
  intro ν₁ ν₂ hν₁ hν₂ σ₁ σ₂ h
  have hr : (ν₁.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x))
      = ν₂.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x) := by
    have hpt : (smearedMeasure σ₁ ν₁).restrict {(0 : ℝ)}ᶜ
        = (smearedMeasure σ₂ ν₂).restrict {(0 : ℝ)}ᶜ := by rw [h]
    rwa [chat13_restrict_compl σ₁ hν₁, chat13_restrict_compl σ₂ hν₂] at hpt
  calc ν₁ = (ν₁.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x)).withDensity
              (fun x => (ENNReal.ofReal (1 - Real.sinc x))⁻¹) :=
        (chat13_untilt hν₁).symm
    _ = (ν₂.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x)).withDensity
              (fun x => (ENNReal.ofReal (1 - Real.sinc x))⁻¹) := by rw [hr]
    _ = ν₂ := chat13_untilt hν₂
