-- Prove2me | solution 1 for ProbabilityTheory.LevyKhintchineTriple.exponent_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:48:10.071204+00:00
-- url     : https://prove2.me/submissions/86b78869-ac6e-4e21-893c-3e58372d7907

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_hermitian_integral_levyCompensatedIntegrand
import Mathlib.Data.Complex.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (T : LevyKhintchineTriple) (ξ : ℝ) :
    T.exponent (-ξ) = starRingEnd ℂ (T.exponent ξ) := by
  simp only [LevyKhintchineTriple.exponent, map_add, map_sub,
    hermitian_integral_levyCompensatedIntegrand ξ,
    Complex.ofReal_neg, map_mul, map_div₀, map_pow, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  ring
