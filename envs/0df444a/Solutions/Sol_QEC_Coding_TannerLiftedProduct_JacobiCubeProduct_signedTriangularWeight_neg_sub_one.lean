-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedTriangularWeight_neg_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:16.16675+00:00
-- url     : https://prove2.me/submissions/e13dabe7-b670-48eb-a33b-f112f0a99c32

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_neg_one_zpow_eq_jacobiParitySign

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution (z : ℤ) :
    jacobiParitySign (-z - 1) * (2 * ((-z - 1 : ℤ) : ℚ) + 1) =
      jacobiParitySign z * (2 * (z : ℚ) + 1) := by
  rw [← neg_one_zpow_eq_jacobiParitySign,
    ← neg_one_zpow_eq_jacobiParitySign]
  have hsign : ((-1 : ℚ) ^ (-z - 1)) = -((-1 : ℚ) ^ z) := by
    rw [show -z - 1 = -z + (-1 : ℤ) by ring,
      zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0), zpow_neg]
    norm_num
    rw [neg_one_zpow_eq_ite]
    split <;> norm_num
  rw [hsign]
  push_cast
  ring
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
