-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat26_smear_integrand_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:23:51.665531+00:00
-- url     : https://prove2.me/submissions/b70bc837-32c9-49a4-a030-91a5a463dd3b

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Theorems.Thm_ProbabilityTheory_leanlevy_chat23_intInt_exp_shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ξ x : ℝ) :
    levyCompensatedIntegrand ξ x
        - (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1, levyCompensatedIntegrand (ξ + u) x
      = Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ) := by
  have hexp_int : IntervalIntegrable
      (fun u => Complex.exp (↑x * ↑(ξ + u) * Complex.I)) volume (-1) 1 :=
    (Complex.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _
  have hlin_int : IntervalIntegrable
      (fun u => (↑x * ↑(ξ + u) * Complex.I *
        (if |x| < (1 : ℝ) then (1 : ℂ) else 0))) volume (-1) 1 :=
    (by fun_prop : Continuous fun u : ℝ =>
      (↑x * ↑(ξ + u) * Complex.I *
        (if |x| < (1 : ℝ) then (1 : ℂ) else 0))).intervalIntegrable _ _
  have hlinear : (∫ u in (-1 : ℝ)..1, (↑(ξ + u) : ℂ)) =
      (2 : ℂ) * (ξ : ℂ) := by
    rw [intervalIntegral.integral_ofReal,
      intervalIntegral.integral_comp_add_left (fun v : ℝ => v) ξ, integral_id]
    push_cast
    ring
  have hlin : (∫ u in (-1 : ℝ)..1,
      (↑x * ↑(ξ + u) * Complex.I *
        (if |x| < (1 : ℝ) then (1 : ℂ) else 0))) =
      (↑x * Complex.I * (if |x| < (1 : ℝ) then (1 : ℂ) else 0)) *
        (2 * (ξ : ℂ)) := by
    have hc : (fun u : ℝ =>
        (↑x * ↑(ξ + u) * Complex.I *
          (if |x| < (1 : ℝ) then (1 : ℂ) else 0))) =
        fun u : ℝ => (↑x * Complex.I *
          (if |x| < (1 : ℝ) then (1 : ℂ) else 0)) * (↑(ξ + u) : ℂ) := by
      funext u
      ring
    rw [hc, intervalIntegral.integral_const_mul, hlinear]
  have h1c : (∫ _u in (-1 : ℝ)..1, (1 : ℂ)) = 2 := by
    rw [intervalIntegral.integral_const]
    show (1 - -1 : ℝ) • (1 : ℂ) = 2
    rw [Complex.real_smul]
    push_cast
    ring
  have hval : (∫ u in (-1 : ℝ)..1,
      levyCompensatedIntegrand (ξ + u) x) =
      Complex.exp (↑x * ↑ξ * Complex.I) * (2 * (Real.sinc x : ℂ)) - 2 -
        (↑x * Complex.I * (if |x| < (1 : ℝ) then (1 : ℂ) else 0)) *
          (2 * (ξ : ℂ)) := by
    simp only [levyCompensatedIntegrand]
    rw [intervalIntegral.integral_sub (hexp_int.sub intervalIntegrable_const) hlin_int,
      intervalIntegral.integral_sub hexp_int intervalIntegrable_const,
      leanlevy_chat23_intInt_exp_shift, hlin, h1c]
  rw [hval]
  simp only [levyCompensatedIntegrand]
  push_cast
  ring
