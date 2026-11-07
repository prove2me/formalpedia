-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPositiveTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:33:36.154099+00:00
-- url     : https://prove2.me/submissions/ce07cda6-49c9-4309-b859-aa119cdf6989

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
theorem _root_.solution (n : ℕ) :
    signedEuler (jtpPositiveTerm n) =
      PowerSeries.C (((n : ℤ) : ℚ) * ((-1 : ℚ) ^ (n : ℤ))) *
        PowerSeries.X ^ n.choose 2 := by
  rw [jtpPositiveTerm, signedEuler_C_T_mul_X_pow]
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
