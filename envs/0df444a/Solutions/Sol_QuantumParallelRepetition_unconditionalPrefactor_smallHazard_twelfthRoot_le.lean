-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPrefactor_smallHazard_twelfthRoot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/f06545ac-d8a2-4e7d-b3bc-7ae738704a9f

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalPrefactor_fourthRoot_async_le_twelfth
import Theorems.Thm_QuantumParallelRepetition_unconditionalPrefactor_balancedHazard_sqrt_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    {eta alpha : ℝ}
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1) :
    Real.sqrt
      ((34 / Real.sqrt
          (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
          (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
        4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
        unconditionalPrefactorBucketCoefficient *
          Real.sqrt
            (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) ≤
      (4 * Real.sqrt
          (34 + unconditionalPrefactorBucketCoefficient) + 2) *
        (eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ)) := by
  let a : ℝ := 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)
  let rho : ℝ := alpha ^ (1 / 12 : ℝ)
  have alpha_third_positive : 0 < alpha ^ (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos alpha_positive _
  have a_positive : 0 < a := by
    dsimp [a]
    have := Real.sqrt_nonneg eta
    linarith
  have eta_root_square : (Real.sqrt eta) ^ 2 = eta :=
    Real.sq_sqrt eta_nonnegative
  have eta_bounded : eta ≤ 1 := by
    have eta_root_bounded : Real.sqrt eta ≤ 1 := by
      nlinarith [Real.sqrt_nonneg eta, alpha_third_positive]
    nlinarith [Real.sqrt_nonneg eta]
  have rho_nonnegative : 0 ≤ rho := by
    dsimp [rho]
    exact Real.rpow_nonneg alpha_positive.le _
  have eta_twelfth_nonnegative : 0 ≤ eta ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg eta_nonnegative _
  have quarter :=
    unconditionalPrefactor_fourthRoot_async_le_twelfth
      eta_nonnegative eta_bounded alpha_positive.le
  have balanced :=
    unconditionalPrefactor_balancedHazard_sqrt_le
      a_positive rho_nonnegative
  have coefficient_root_nonnegative :
      0 ≤ Real.sqrt
        (34 + unconditionalPrefactorBucketCoefficient) :=
    Real.sqrt_nonneg _
  change
    Real.sqrt
      ((34 / Real.sqrt a) * a + 4 * rho ^ 2 +
        unconditionalPrefactorBucketCoefficient * Real.sqrt a) ≤
      (4 * Real.sqrt
          (34 + unconditionalPrefactorBucketCoefficient) + 2) *
        (eta ^ (1 / 12 : ℝ) + rho)
  change a ^ (1 / 4 : ℝ) ≤
    4 * eta ^ (1 / 12 : ℝ) + rho at quarter
  nlinarith [mul_nonneg coefficient_root_nonnegative
    (sub_nonneg.mpr quarter),
    mul_nonneg coefficient_root_nonnegative rho_nonnegative,
    mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num)
      eta_twelfth_nonnegative]
end QuantumParallelRepetition
