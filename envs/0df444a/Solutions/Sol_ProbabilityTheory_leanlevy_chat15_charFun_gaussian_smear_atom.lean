-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_charFun_gaussian_smear_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:46:31.973384+00:00
-- url     : https://prove2.me/submissions/e6772218-cb7f-49e8-b1ed-0b46989f2225

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- The Fourier transform of the Gaussian smear atom is its constant mass. -/
theorem solution (σ_sq : ℝ≥0) (ξ : ℝ) :
    charFun (((σ_sq : ℝ≥0∞) / 6) • Measure.dirac (0 : ℝ)) ξ
      = (((σ_sq : ℝ) / 6 : ℝ) : ℂ) := by
  haveI : IsFiniteMeasure (((σ_sq : ℝ≥0∞) / 6) • Measure.dirac (0 : ℝ)) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ 0), mul_one]
    exact ENNReal.div_lt_top (by simp) (by simp)
  rw [charFun_apply_real, integral_smul_measure, integral_dirac,
      show (↑ξ : ℂ) * ↑(0 : ℝ) * Complex.I = 0 from by simp, Complex.exp_zero]
  show ((↑σ_sq / 6 : ℝ≥0∞).toReal) • (1 : ℂ) = ↑((σ_sq : ℝ) / 6)
  rw [Complex.real_smul, mul_one]
  congr 1
  rw [ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.toReal_ofNat]
