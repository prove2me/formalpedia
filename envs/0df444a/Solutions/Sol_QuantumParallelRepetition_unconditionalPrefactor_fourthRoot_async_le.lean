-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPrefactor_fourthRoot_async_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/48cf588e-2708-4428-9fd6-b374ca371cd5

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalPrefactor_sixtyFour_fourthRoot_le

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
    (alpha_nonnegative : 0 ≤ alpha) :
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) ≤
      4 * eta ^ (1 / 8 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
  have asynchronous_nonnegative : 0 ≤ (64 : ℝ) * Real.sqrt eta := by
    positivity
  have precision_nonnegative : 0 ≤ alpha ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg alpha_nonnegative _
  have split := Real.rpow_add_le_add_rpow
    asynchronous_nonnegative precision_nonnegative
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have eta_identity :
      (Real.sqrt eta) ^ (1 / 4 : ℝ) = eta ^ (1 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul eta_nonnegative]
    norm_num
  have alpha_identity :
      (alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) =
        alpha ^ (1 / 12 : ℝ) := by
    rw [← Real.rpow_mul alpha_nonnegative]
    norm_num
  have numerical :=
    unconditionalPrefactor_sixtyFour_fourthRoot_le
  calc
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ)
        ≤ (64 * Real.sqrt eta) ^ (1 / 4 : ℝ) +
          (alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) := split
    _ = (64 : ℝ) ^ (1 / 4 : ℝ) * eta ^ (1 / 8 : ℝ) +
          alpha ^ (1 / 12 : ℝ) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64)
            (Real.sqrt_nonneg eta), eta_identity, alpha_identity]
    _ ≤ 4 * eta ^ (1 / 8 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
          gcongr
end QuantumParallelRepetition
