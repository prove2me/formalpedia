-- Prove2me | solution 1 for P2M_Deduction_LFunctionConjugation_Gamma__conj_2d580e70eb48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:47.522204+00:00
-- url     : https://prove2.me/submissions/a7d208ce-8a0e-43d4-8243-f48e7c596de5

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Theorems.Thm_Deduction_LFunctionConjugation_ofReal_cpow_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
open Deduction.LFunctionConjugation
open HurwitzZeta
namespace Deduction.LFunctionConjugation
theorem _root_.solution (s : ℂ) : Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Gammaℝ s) := by
  have h1 : -(starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (-s / 2) := by
    rw [map_div₀, map_neg, map_ofNat]
  have h2 : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) := by
    rw [map_div₀, map_ofNat]
  rw [Gammaℝ, Gammaℝ, h1, h2, ofReal_cpow_conj Real.pi_pos.le, Complex.Gamma_conj, map_mul]
end Deduction.LFunctionConjugation
