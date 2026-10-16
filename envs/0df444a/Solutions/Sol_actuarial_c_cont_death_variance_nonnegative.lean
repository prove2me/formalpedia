-- Prove2me | solution 1 for actuarial_c_cont_death_variance_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T17:17:42.298709+00:00
-- url     : https://prove2.me/submissions/521a1861-9d00-4e1d-92b4-3a8a2328e07e

import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_c_cont_deathPV
import Definitions.Def_actuarial_c_cont_deathEPV
import Definitions.Def_actuarial_c_cont_deathSecondEPV
import Definitions.Def_actuarial_c_cont_deathVariance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ActuarialAssurances.Continuous
open MeasureTheory
theorem solution (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (n delta : ℝ)
    (hn : 0 ≤ n) (hsupport : μ {t : ℝ | 0 ≤ t} = 1) :
    0 ≤ deathVariance μ n delta := by
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
  have hbound : ∀ t : ℝ,
      ‖deathPV n delta t‖ ≤ Real.exp (|delta| * n) := by
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
  let X : ℝ → ℝ := deathPV n delta
  let C : ℝ := Real.exp (|delta| * n)
  have hC : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hX : Integrable X μ :=
    Integrable.of_bound hmeas.aestronglyMeasurable C (by
      filter_upwards [] with t
      exact hbound t)
  have hXsq : Integrable (fun t => (X t)^2) μ :=
    Integrable.of_bound (hmeas.pow_const 2).aestronglyMeasurable (C^2) (by
      filter_upwards [] with t
      have hx : ‖X t‖ ≤ C := hbound t
      have hs : ‖X t‖ ^ 2 ≤ C^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hx)
          (add_nonneg hC (norm_nonneg (X t)))]
      simpa only [norm_pow] using hs)
  let c : ℝ := ∫ t, X t ∂μ
  have hnonneg : 0 ≤ ∫ t, (X t - c)^2 ∂μ := by
    apply integral_nonneg
    intro t
    exact sq_nonneg _
  have hcenter :
      (∫ t, (X t - c)^2 ∂μ) =
      (∫ t, (X t)^2 ∂μ) - c^2 := by
    have hcm : Integrable (fun t => (2*c)*X t) μ :=
      hX.const_mul (2*c)
    calc
      (∫ t, (X t - c)^2 ∂μ) =
        ∫ t, ((X t)^2 - (2*c)*X t + c^2) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with t
          ring
      _ = (∫ t, (X t)^2 ∂μ) - c^2 := by
          have hadd : (∫ t, ((X t)^2 - (2*c)*X t + c^2) ∂μ) =
              (∫ t, ((X t)^2 - (2*c)*X t) ∂μ) +
              (∫ t, c^2 ∂μ) := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              (integral_add (hXsq.sub hcm) (integrable_const (c^2)))
          rw [hadd, integral_sub hXsq hcm]
          rw [integral_const_mul]
          simp only [integral_const]
          have hmass : μ.real Set.univ = 1 := by simp
          rw [hmass]
          dsimp [c]
          ring
  unfold deathVariance deathSecondEPV deathEPV
  change 0 ≤ (∫ t, (X t)^2 ∂μ) - c^2
  calc
    0 ≤ ∫ t, (X t - c)^2 ∂μ := hnonneg
    _ = (∫ t, (X t)^2 ∂μ) - c^2 := hcenter
