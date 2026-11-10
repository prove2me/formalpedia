-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat27_smeared_exponent_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:19:04.857465+00:00
-- url     : https://prove2.me/submissions/fe9ebf48-67aa-4985-afa1-e07cc756023d

import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26b_intInt_exponent_jump
import Theorems.Thm_ProbabilityTheory_continuous_integral_levyCompensatedIntegrand
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26_charFun_smearedMeasure_public
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Real

private lemma chat26_linear (ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, (ξ + u) = 2 * ξ := by
  rw [intervalIntegral.integral_comp_add_left (fun v => v) ξ, integral_id]
  ring

private lemma chat26_quadratic (ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, (ξ + u) ^ 2 = 2 * ξ ^ 2 + 2 / 3 := by
  rw [intervalIntegral.integral_comp_add_left (fun v => v ^ 2) ξ, integral_pow]
  ring

private lemma chat26_drift (b ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, ((b : ℂ) * ↑(ξ + u) * Complex.I)
      = 2 * (b : ℂ) * ↑ξ * Complex.I := by
  have hc : (fun u : ℝ => ((b : ℂ) * ↑(ξ + u) * Complex.I)) =
      fun u : ℝ => ((b : ℂ) * Complex.I) * (↑(ξ + u) : ℂ) := by
    funext u
    ring
  rw [hc, show (∫ u in (-1 : ℝ)..1, ((b : ℂ) * Complex.I) * (↑(ξ + u) : ℂ))
        = ((b : ℂ) * Complex.I) * ∫ u in (-1 : ℝ)..1, (↑(ξ + u) : ℂ)
      from intervalIntegral.integral_const_mul _ _,
      intervalIntegral.integral_ofReal, chat26_linear]
  push_cast
  ring

private lemma chat26_gauss (s ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, ((s : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2)
      = (s : ℂ) * (ξ : ℂ) ^ 2 + (s : ℂ) / 3 := by
  have hc : (fun u : ℝ => ((s : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2)) =
      fun u : ℝ => ((s : ℂ) / 2) * (↑((ξ + u) ^ 2 : ℝ) : ℂ) := by
    funext u
    push_cast
    ring
  rw [hc, show (∫ u in (-1 : ℝ)..1, ((s : ℂ) / 2) * (↑((ξ + u) ^ 2 : ℝ) : ℂ))
        = ((s : ℂ) / 2) * ∫ u in (-1 : ℝ)..1, (↑((ξ + u) ^ 2 : ℝ) : ℂ)
      from intervalIntegral.integral_const_mul _ _,
      intervalIntegral.integral_ofReal, chat26_quadratic]
  push_cast
  ring

theorem solution (T : LevyKhintchineTriple) (ξ : ℝ) :
    T.exponent ξ - (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1, T.exponent (ξ + u)
      = charFun (smearedMeasure T.gaussianVariance T.levyMeasure) ξ := by
  have hν := T.levyMeasure_isLevyMeasure
  have hdrift_int : IntervalIntegrable
      (fun u => ((T.drift : ℂ) * ↑(ξ + u) * Complex.I)) volume (-1) 1 :=
    (by fun_prop : Continuous fun u : ℝ =>
      ((T.drift : ℂ) * ↑(ξ + u) * Complex.I)).intervalIntegrable _ _
  have hgauss_int : IntervalIntegrable
      (fun u => ((T.gaussianVariance : ℝ) : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2) volume (-1) 1 :=
    (by fun_prop : Continuous fun u : ℝ =>
      ((T.gaussianVariance : ℝ) : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2).intervalIntegrable _ _
  have hjump_int : IntervalIntegrable
      (fun u => ∫ x, levyCompensatedIntegrand (ξ + u) x ∂T.levyMeasure) volume (-1) 1 :=
    ((continuous_integral_levyCompensatedIntegrand hν).comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hval : (∫ u in (-1 : ℝ)..1, T.exponent (ξ + u))
      = 2 * (T.drift : ℂ) * ↑ξ * Complex.I
        - (((T.gaussianVariance : ℝ) : ℂ) * (ξ : ℂ) ^ 2 + ((T.gaussianVariance : ℝ) : ℂ) / 3)
        + 2 * ((∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure)
            - ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ)
                ∂T.levyMeasure) := by
    simp only [LevyKhintchineTriple.exponent]
    rw [intervalIntegral.integral_add (hdrift_int.sub hgauss_int) hjump_int,
        intervalIntegral.integral_sub hdrift_int hgauss_int,
        chat26_drift, chat26_gauss, leanlevy_chat26b_intInt_exponent_jump hν]
  rw [LevyKhintchineTriple.exponent, hval,
      leanlevy_chat26_charFun_smearedMeasure_public hν T.gaussianVariance ξ]
  push_cast
  ring