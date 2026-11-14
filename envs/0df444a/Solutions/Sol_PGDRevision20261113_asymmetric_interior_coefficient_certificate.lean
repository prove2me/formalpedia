-- Prove2me | solution 1 for PGDRevision20261113.asymmetric_interior_coefficient_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T09:45:52.633632+00:00
-- url     : https://prove2.me/submissions/b3ddbb3b-4944-44cc-a896-0e3bdc3b69e9

import Definitions.Def_PGDRevision20261113_AlgebraicCertificates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 4000000
open PGDRevision20261113
open scoped BigOperators

private def transformedPowerCoefficients : List ℝ :=
  [126930799,5365449950,106983876225,1325013540500,11296729933125,
   69454391418750,313684387734375,1040230186250000,2486434493750000,
   4099723453125000,4223064179687500,1969593750000000,-592726562500000,
   -1025156250000000,-284765625000000]

private lemma transformed_coeff_eq (i : Fin 15) :
    asymTransformedCoefficient i = transformedPowerCoefficients.getD i.val 0 := by
  fin_cases i <;> norm_num [asymTransformedCoefficient, asymMinusCoefficients,
    transformedPowerCoefficients, Fin.sum_univ_succ, Nat.choose]

theorem solution : AsymmetricCoefficientCertificateClaim := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [asymPlusCoefficients]
  · norm_num [asymBernsteinCoefficients]
  · intro j
    fin_cases j <;> norm_num [asymPlusCoefficients]
  · refine ⟨14, ?_⟩
    norm_num [asymPlusCoefficients]
  · intro j
    fin_cases j <;> norm_num [asymBernsteinCoefficients]
  · refine ⟨0, ?_⟩
    norm_num [asymBernsteinCoefficients]
  · intro j
    fin_cases j <;> norm_num [asymBernsteinCoefficients, transformed_coeff_eq,
      transformedPowerCoefficients, Fin.sum_univ_succ, Nat.choose]
  · intro z
    norm_num [asymQMinus, evalDescending, asymMinusCoefficients,
      asymBernsteinCoefficients, Fin.sum_univ_succ, Nat.choose]
    <;> ring
  · norm_num [asymTailCoefficients]
  · intro j
    fin_cases j <;> norm_num [asymTailCoefficients]
  · refine ⟨0, ?_⟩
    norm_num [asymTailCoefficients]
  · intro z hz
    have hu : 6 + z ≠ 0 := ne_of_gt (by linarith)
    have hd : (6 + z) ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
    dsimp [asymLower, asymS, asymB, evalDescending, asymTailCoefficients]
    field_simp
    <;> ring
