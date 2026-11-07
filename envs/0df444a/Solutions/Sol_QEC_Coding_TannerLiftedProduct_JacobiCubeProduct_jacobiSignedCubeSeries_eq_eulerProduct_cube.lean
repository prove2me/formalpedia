-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiSignedCubeSeries_eq_eulerProduct_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:42:38.393917+00:00
-- url     : https://prove2.me/submissions/fdae642a-e5f5-4ae0-944a-1c296483c7a7

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jacobiProd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jacobiBilateral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_jacobiTripleProduct


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution :
    jacobiSignedCubeSeries = eulerProduct ^ 3 := by
  have h := congrArg signedEuler
    jacobiTripleProduct
  rw [signedEuler_jacobiProd, signedEuler_jacobiBilateral] at h
  exact (neg_injective h).symm
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
