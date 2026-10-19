-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSmallSourcePhysicalRoundedLower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/284c1e81-994e-41e0-95c3-c1a778f31ee6

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSmallSourcePhysicalLoss

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    (K eta alpha deviation clipping epsilon lam actual : ℝ)
    (constant :
      1024 + 8 *
          (4 * Real.sqrt
            (34 + unconditionalPrefactorBucketCoefficient) + 2) ≤ K)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small :
      64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_deviation :
      deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)))
    (actual_clipping :
      clipping ≤
        16 * eta + 8 * (3 * alpha ^ (1 / 3 : ℝ) / 2))
    (lam_nonnegative : 0 ≤ lam)
    (actual_original_verifier :
      1 - epsilon / 2 - 5 * lam -
        ((64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) +
            (alpha ^ (1 / 3 : ℝ)) ^ 2) +
          4 * Real.sqrt deviation + 4 * Real.sqrt clipping +
          2 * Real.sqrt (8 * eta)) ≤ actual) :
    roundedWinningLowerBound epsilon K alpha eta lam ≤ actual := by
  let R : ℝ :=
    alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
  have loss := unconditionalSmallSourcePhysicalLoss
    K eta alpha deviation clipping constant eta_nonnegative
    alpha_positive alpha_bounded small actual_deviation actual_clipping
  have K_nonnegative : 0 ≤ K := by
    have root_nonnegative :=
      Real.sqrt_nonneg (34 + unconditionalPrefactorBucketCoefficient)
    linarith
  have R_nonnegative : 0 ≤ R := by
    dsimp [R]
    exact add_nonneg
      (Real.rpow_nonneg alpha_positive.le _)
      (Real.rpow_nonneg (by positivity) _)
  have ceiling_nonnegative : 0 ≤ universalErrorCeiling K := by
    unfold universalErrorCeiling
    have root_nonnegative :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 / 6 : ℝ)
    nlinarith [mul_nonneg K_nonnegative
      (show 0 ≤ 1 + (2 : ℝ) ^ (1 / 6 : ℝ) by positivity)]
  have transfer_nonnegative : 0 ≤ universalErrorCeiling K * lam :=
    mul_nonneg ceiling_nonnegative lam_nonnegative
  have quantum_nonnegative : 0 ≤ K * R :=
    mul_nonneg K_nonnegative R_nonnegative
  change
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) +
        (alpha ^ (1 / 3 : ℝ)) ^ 2) +
      4 * Real.sqrt deviation + 4 * Real.sqrt clipping ≤ K * R
      at loss
  unfold roundedWinningLowerBound totalSamplingLoss
  change
    1 - epsilon / 2 -
      (5 * lam +
        2 * (K * R + Real.sqrt (8 * eta) +
          universalErrorCeiling K * lam)) ≤ actual
  nlinarith
end QuantumParallelRepetition
