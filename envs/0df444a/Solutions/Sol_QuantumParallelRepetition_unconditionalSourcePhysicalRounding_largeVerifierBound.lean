-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourcePhysicalRounding_largeVerifierBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/263c998a-291f-4c21-a4b9-1db15af9bdbc

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalPrefactor_largeVerifier_twelfthRoot_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    (K eta alpha lam epsilon : ℝ)
    (constant : 128 ≤ K)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (lam_nonnegative : 0 ≤ lam)
    (epsilon_nonnegative : 0 ≤ epsilon)
    (large : 1 < 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) :
    roundedWinningLowerBound epsilon K alpha eta lam ≤ 0 := by
  have eta_root_nonnegative : 0 ≤ eta ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg eta_nonnegative _
  have alpha_root_nonnegative : 0 ≤ alpha ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg alpha_positive.le _
  have scaled_nonnegative : 0 ≤ (32 * eta) ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have root_scaled : eta ^ (1 / 12 : ℝ) ≤
      (32 * eta) ^ (1 / 12 : ℝ) := by
    apply Real.rpow_le_rpow eta_nonnegative
    · nlinarith
    · norm_num
  have root_sum_nonnegative :
      0 ≤ eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ) :=
    add_nonneg eta_root_nonnegative alpha_root_nonnegative
  have constant_nonnegative : 0 ≤ K := by linarith
  have universal_nonnegative : 0 ≤ universalErrorCeiling K := by
    unfold universalErrorCeiling
    positivity
  have hazard :=
    unconditionalPrefactor_largeVerifier_twelfthRoot_le
      eta_nonnegative alpha_positive alpha_bounded large
  have quantum :
      2 ≤ K *
        (alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)) := by
    calc
      (2 : ℝ) ≤
          128 * (eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ)) :=
        hazard
      _ ≤ K *
          (alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)) := by
        apply mul_le_mul constant
        · linarith
        · exact root_sum_nonnegative
        · exact constant_nonnegative
  have lam_error : 0 ≤ universalErrorCeiling K * lam :=
    mul_nonneg universal_nonnegative lam_nonnegative
  have sqrt_error : 0 ≤ Real.sqrt (8 * eta) :=
    Real.sqrt_nonneg _
  unfold roundedWinningLowerBound totalSamplingLoss
  nlinarith
end QuantumParallelRepetition
