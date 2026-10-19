-- Prove2me | solution 1 for QuantumParallelRepetition.pdfFullQuantitativeSamplingLoss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/4f10fd68-fe90-4289-86ca-a537b8192c8f

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfGapBase_twelfth_le_one
import Theorems.Thm_QuantumParallelRepetition_pdfEntropyRoundingLoss_lt_gapQuarter
import Theorems.Thm_QuantumParallelRepetition_pdfCatalystAccuracy_samplingLoss
import Theorems.Thm_QuantumParallelRepetition_pdfUniversalErrorCeiling_pos
import Theorems.Thm_QuantumParallelRepetition_pdfRoundingCoefficient_one_le
import Theorems.Thm_QuantumParallelRepetition_pdfQuantitativeRoundingLoss

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {K ε eta kappa : ℝ}
    (constant : 1 ≤ K)
    (gap : 0 < ε)
    (unit : ε ≤ 1)
    (entropy : 0 ≤ eta)
    (small :
      eta <
        (ε / (4 * pdfRoundingCoefficient K)) ^ (12 : ℕ))
    (pinsker : kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta)) :
    totalSamplingLoss K (pdfCatalystAccuracy K ε) eta
      (kappa + ε / (16 * (5 + 2 * universalErrorCeiling K))) <
        ε / 2 := by
  have coefficient : 1 ≤ pdfRoundingCoefficient K :=
    pdfRoundingCoefficient_one_le constant
  have bounded : eta ≤ 1 :=
    small.le.trans
      (pdfGapBase_twelfth_le_one coefficient gap unit)
  have loss := pdfQuantitativeRoundingLoss
    (K := K) (alpha := pdfCatalystAccuracy K ε)
    (eta := eta) (kappa := kappa)
    (gamma := ε / (16 * (5 + 2 * universalErrorCeiling K)))
    (by linarith) entropy bounded pinsker
  have entropy_loss :
      pdfRoundingCoefficient K * eta ^ (1 / 12 : ℝ) <
        ε / 4 :=
    pdfEntropyRoundingLoss_lt_gapQuarter
      coefficient gap entropy small
  have catalyst_loss :
      2 * K *
        (pdfCatalystAccuracy K ε) ^ (1 / 12 : ℝ) =
        ε / 8 :=
    pdfCatalystAccuracy_samplingLoss constant gap
  have ceiling : 0 < universalErrorCeiling K :=
    pdfUniversalErrorCeiling_pos constant
  have gamma_loss :
      (5 + 2 * universalErrorCeiling K) *
          (ε / (16 * (5 + 2 * universalErrorCeiling K))) =
        ε / 16 := by
    field_simp
  linarith
end QuantumParallelRepetition
