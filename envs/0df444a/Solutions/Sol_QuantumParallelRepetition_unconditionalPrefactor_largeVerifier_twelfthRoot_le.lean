-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPrefactor_largeVerifier_twelfthRoot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/646d1a2f-bfab-45ba-869d-9402f6cd7d77

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    (alpha_bounded : alpha ≤ 1)
    (large : 1 < 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) :
    (2 : ℝ) ≤
      128 * (eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ)) := by
  have eta_root_nonnegative : 0 ≤ eta ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg eta_nonnegative _
  have alpha_root_nonnegative : 0 ≤ alpha ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg alpha_positive.le _
  by_cases eta_bounded : eta ≤ 1
  · have eta_root_compare :
        Real.sqrt eta ≤ eta ^ (1 / 12 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge'
        eta_nonnegative eta_bounded
        (by norm_num : (0 : ℝ) ≤ 1 / 12)
        (by norm_num : (1 / 12 : ℝ) ≤ 1 / 2)
    have alpha_root_compare :
        alpha ^ (1 / 3 : ℝ) ≤ alpha ^ (1 / 12 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge'
        alpha_positive.le alpha_bounded
        (by norm_num : (0 : ℝ) ≤ 1 / 12)
        (by norm_num : (1 / 12 : ℝ) ≤ 1 / 3)
    nlinarith
  · have eta_large : 1 ≤ eta := (lt_of_not_ge eta_bounded).le
    have eta_root_large : 1 ≤ eta ^ (1 / 12 : ℝ) :=
      Real.one_le_rpow eta_large (by norm_num : (0 : ℝ) ≤ 1 / 12)
    nlinarith
end QuantumParallelRepetition
