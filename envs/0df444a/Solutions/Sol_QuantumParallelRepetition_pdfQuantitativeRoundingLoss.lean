-- Prove2me | solution 1 for QuantumParallelRepetition.pdfQuantitativeRoundingLoss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/ea7c04c6-f794-4181-ad90-346944f73801

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfPinskerRoot_le_twelfthRoot
import Theorems.Thm_QuantumParallelRepetition_pdfSqrtEight_le_twelfthRoot

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {K alpha eta kappa gamma : ℝ}
    (constant : 0 ≤ K)
    (nonnegative : 0 ≤ eta)
    (bounded : eta ≤ 1)
    (pinsker : kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta)) :
    totalSamplingLoss K alpha eta (kappa + gamma) ≤
      2 * K * alpha ^ (1 / 12 : ℝ) +
        pdfRoundingCoefficient K * eta ^ (1 / 12 : ℝ) +
        (5 + 2 * universalErrorCeiling K) * gamma := by
  have ceiling : 0 ≤ universalErrorCeiling K := by
    unfold universalErrorCeiling
    positivity
  have classical_coefficient :
      0 ≤ 5 + 2 * universalErrorCeiling K := by
    nlinarith
  have pinsker_bound :=
    pdfPinskerRoot_le_twelfthRoot nonnegative bounded pinsker
  have weighted_pinsker :
      (5 + 2 * universalErrorCeiling K) * kappa ≤
        (5 + 2 * universalErrorCeiling K) *
          (Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ)) :=
    mul_le_mul_of_nonneg_left pinsker_bound classical_coefficient
  have sqrt_bound :=
    pdfSqrtEight_le_twelfthRoot nonnegative bounded
  have weighted_sqrt :
      2 * Real.sqrt (8 * eta) ≤
        2 * (Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ)) :=
    mul_le_mul_of_nonneg_left sqrt_bound (by norm_num)
  have source_bounds := add_le_add weighted_pinsker weighted_sqrt
  calc
    totalSamplingLoss K alpha eta (kappa + gamma) =
        2 * K * alpha ^ (1 / 12 : ℝ) +
          ((5 + 2 * universalErrorCeiling K) * kappa +
            2 * Real.sqrt (8 * eta)) +
          2 * K *
            ((32 : ℝ) ^ (1 / 12 : ℝ) * eta ^ (1 / 12 : ℝ)) +
          (5 + 2 * universalErrorCeiling K) * gamma := by
      unfold totalSamplingLoss
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) nonnegative]
      ring
    _ ≤ 2 * K * alpha ^ (1 / 12 : ℝ) +
          ((5 + 2 * universalErrorCeiling K) *
              (Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ)) +
            2 * (Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ))) +
          2 * K *
            ((32 : ℝ) ^ (1 / 12 : ℝ) * eta ^ (1 / 12 : ℝ)) +
          (5 + 2 * universalErrorCeiling K) * gamma := by
      gcongr
    _ = 2 * K * alpha ^ (1 / 12 : ℝ) +
          pdfRoundingCoefficient K * eta ^ (1 / 12 : ℝ) +
          (5 + 2 * universalErrorCeiling K) * gamma := by
      unfold pdfRoundingCoefficient
      ring
end QuantumParallelRepetition
