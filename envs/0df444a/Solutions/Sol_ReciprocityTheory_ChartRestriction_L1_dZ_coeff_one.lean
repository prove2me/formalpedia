-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.dZ_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:38:47.110143+00:00
-- url     : https://prove2.me/submissions/51502ec1-dd78-4eaf-9d59-0fc6b8892edf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eisenstein_cube_sub_sq_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_dZ_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
namespace ReciprocityTheory.ChartRestriction.L1
private theorem dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq : dZ = tZ + PowerSeries.C (100 : ℤ) * s3Z ^ 2 +
    PowerSeries.C (8000 : ℤ) * s3Z ^ 3 - PowerSeries.C (147 : ℤ) * s5Z ^ 2 := by
  have h := dZ_mul.trans eisenstein_cube_sub_sq_eq
  refine mul_left_cancel₀ (fun h0 => ?_) h
  have := congrArg PowerSeries.constantCoeff h0
  rw [PowerSeries.constantCoeff_C, map_zero] at this
  norm_num at this
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : PowerSeries.coeff 1 dZ = 1 := by
  rw [dZ_eq_tZ_add_s3Z_sq_add_s3Z_cube_sub_s5Z_sq]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, pow_succ, pow_zero, one_mul,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, tZ, s3Z, s5Z, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
  norm_num
end ReciprocityTheory.ChartRestriction.L1
