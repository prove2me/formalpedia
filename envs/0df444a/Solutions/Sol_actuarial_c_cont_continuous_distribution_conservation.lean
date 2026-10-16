-- Prove2me | solution 1 for actuarial_c_cont_continuous_distribution_conservation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T13:04:51.791973+00:00
-- url     : https://prove2.me/submissions/bd74584f-f125-47ed-a959-c85d6c304a16

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_c_cont_exposure
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_maturityPV
import Definitions.Def_actuarial_c_cont_continuousAnnuityPV
import Definitions.Def_actuarial_c_cont_deathEPV
import Definitions.Def_actuarial_c_cont_maturityEPV
import Definitions.Def_actuarial_c_cont_continuousAnnuityEPV
import Theorems.Thm_actuarial_c_cont_continuous_path_conservation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ActuarialAssurances.Continuous
open MeasureTheory
private theorem maturityPV_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n delta : ℝ) : Integrable (maturityPV n delta) μ := by
  classical
  have hf : maturityPV n delta = (Set.Ici n).indicator (fun _ : ℝ => Real.exp (-delta * n)) := by
    funext t
    by_cases ht : n ≤ t
    · simp [maturityPV, Set.indicator, Set.mem_Ici, ht]
    · simp [maturityPV, Set.indicator, Set.mem_Ici, ht]
  rw [hf]
  exact (integrable_const _).indicator measurableSet_Ici
private theorem exposure_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℝ) (hn : 0 ≤ n) : Integrable (exposure n) μ := by
  have hmeas : Measurable (exposure n) := by
    unfold exposure
    fun_prop
  have hbound : ∀ t : ℝ, ‖exposure n t‖ ≤ n := by
    intro t
    have hnon : 0 ≤ exposure n t := by
      unfold exposure
      exact le_min hn (le_max_left _ _)
    have hupper : exposure n t ≤ n := by
      unfold exposure
      exact min_le_left _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact hupper
  apply Integrable.of_bound hmeas.aestronglyMeasurable n
  filter_upwards [] with t
  exact hbound t
/-- Immediate death benefit at a finite maturity is integrable under a probability law. -/
private theorem deathPV_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (n delta : ℝ) (hn : 0 ≤ n) : Integrable (deathPV n delta) μ := by
  have hmeas : Measurable (deathPV n delta) := by
    have hf : deathPV n delta =
        (Set.Ico (0 : ℝ) n).indicator
          (fun t : ℝ => Real.exp (-delta * t)) := by
      funext t
      by_cases ht : 0 ≤ t ∧ t < n
      · simp [deathPV, Set.indicator, Set.mem_Ico, ht]
      · simp [deathPV, Set.indicator, Set.mem_Ico, ht]
    rw [hf]
    have hexp : Measurable (fun t : ℝ => Real.exp (-delta * t)) := by
      fun_prop
    exact hexp.indicator measurableSet_Ico
  have hbound : ∀ t : ℝ, ‖deathPV n delta t‖ ≤ Real.exp (|delta| * n) := by
    intro t
    by_cases ht : 0 ≤ t ∧ t < n
    · have hx : -delta * t ≤ |delta| * n := by
        calc
          -delta * t ≤ |(-delta) * t| := le_abs_self _
          _ = |delta| * t := by rw [abs_mul, abs_neg, abs_of_nonneg ht.1]
          _ ≤ |delta| * n :=
            mul_le_mul_of_nonneg_left ht.2.le (abs_nonneg _)
      rw [deathPV, if_pos ht, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact (Real.exp_le_exp).mpr hx
    · rw [deathPV, if_neg ht, norm_zero]
      exact le_of_lt (Real.exp_pos _)
  apply Integrable.of_bound hmeas.aestronglyMeasurable (Real.exp (|delta| * n))
  filter_upwards [] with t
  exact hbound t
/-- The discount exponential of bounded exposure is globally integrable. -/
private theorem exposure_exp_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (n delta : ℝ) (hn : 0 ≤ n) : Integrable (fun t => Real.exp (-delta * exposure n t)) μ := by
  have hmeas : Measurable (fun t : ℝ => Real.exp (-delta * exposure n t)) := by
    unfold exposure
    fun_prop
  have hbound : ∀ t : ℝ, ‖Real.exp (-delta * exposure n t)‖ ≤ Real.exp (|delta| * n) := by
    intro t
    have h0 : 0 ≤ exposure n t := by
      unfold exposure
      exact le_min hn (le_max_left _ _)
    have hn' : exposure n t ≤ n := by
      unfold exposure
      exact min_le_left _ _
    have hx : -delta * exposure n t ≤ |delta| * n := by
      calc
        -delta * exposure n t ≤ |(-delta) * exposure n t| := le_abs_self _
        _ = |delta| * exposure n t := by
          rw [abs_mul, abs_neg, abs_of_nonneg h0]
        _ ≤ |delta| * n :=
          mul_le_mul_of_nonneg_left hn' (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_exp).mpr hx
  apply Integrable.of_bound hmeas.aestronglyMeasurable (Real.exp (|delta| * n))
  filter_upwards [] with t
  exact hbound t
/-- Integrability of the entire continuously paid unit annuity. -/
private theorem continuousAnnuityPV_integrable (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (n delta : ℝ) (hn : 0 ≤ n) :
    Integrable (continuousAnnuityPV n delta) μ := by
  by_cases hd : delta = 0
  · have heq : continuousAnnuityPV n delta = exposure n := by
      funext t
      simp [continuousAnnuityPV, hd]
    rw [heq]
    exact exposure_integrable μ n hn
  · have he := exposure_exp_integrable μ n delta hn
    have hdif : Integrable (fun t : ℝ =>
      1 - Real.exp (-delta * exposure n t)) μ :=
      (integrable_const (1 : ℝ)).sub he
    have hdiv := hdif.div_const delta
    have heq : continuousAnnuityPV n delta =
        (fun t => (1 - Real.exp (-delta * exposure n t)) / delta) := by
      funext t
      simp [continuousAnnuityPV, hd]
    rw [heq]
    exact hdiv
theorem solution (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (n delta : ℝ) (hn : 0 ≤ n)
    (hsupport : μ {t : ℝ | 0 ≤ t} = 1) :
    deathEPV μ n delta + maturityEPV μ n delta +
      delta * continuousAnnuityEPV μ n delta = 1 := by
  have haesupport : ∀ᵐ t ∂μ, 0 ≤ t := by
    rw [ae_iff_prob_eq_one (by fun_prop)]
    exact hsupport
  have hD := deathPV_integrable μ n delta hn
  have hM := maturityPV_integrable μ n delta
  have hA := continuousAnnuityPV_integrable μ n delta hn
  calc
    deathEPV μ n delta + maturityEPV μ n delta +
      delta * continuousAnnuityEPV μ n delta =
      ∫ t, deathPV n delta t + maturityPV n delta t +
        delta * continuousAnnuityPV n delta t ∂μ := by
          simp only [deathEPV, maturityEPV, continuousAnnuityEPV]
          rw [← integral_add hD hM]
          rw [← integral_const_mul]
          exact (integral_add (hD.add hM) (hA.const_mul delta)).symm
    _ = ∫ t, (1 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [haesupport] with t ht
      exact actuarial_c_cont_continuous_path_conservation n delta t hn ht
    _ = 1 := by simp
