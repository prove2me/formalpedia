-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPrefactor_fourthRoot_async_le_twelfth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/5d679f46-a0f9-43ab-853f-665c91bf6f1a

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalPrefactor_fourthRoot_async_le

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
    (eta_bounded : eta ≤ 1)
    (alpha_nonnegative : 0 ≤ alpha) :
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) ≤
      4 * eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
  have root_compare : eta ^ (1 / 8 : ℝ) ≤ eta ^ (1 / 12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge'
      eta_nonnegative eta_bounded
      (by norm_num : (0 : ℝ) ≤ 1 / 12)
      (by norm_num : (1 / 12 : ℝ) ≤ 1 / 8)
  calc
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ)
        ≤ 4 * eta ^ (1 / 8 : ℝ) + alpha ^ (1 / 12 : ℝ) :=
          unconditionalPrefactor_fourthRoot_async_le
            eta_nonnegative alpha_nonnegative
    _ ≤ 4 * eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
          gcongr
end QuantumParallelRepetition
