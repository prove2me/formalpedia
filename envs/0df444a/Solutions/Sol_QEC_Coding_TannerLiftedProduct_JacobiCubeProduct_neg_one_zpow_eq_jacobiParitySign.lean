-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.neg_one_zpow_eq_jacobiParitySign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:22:51.72874+00:00
-- url     : https://prove2.me/submissions/6cbc103a-602e-4ef1-8216-87462cac9f1c

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution (z : ℤ) :
    ((-1 : ℚ) ^ z) = jacobiParitySign z := by
  rw [neg_one_zpow_eq_ite]
  rfl
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
