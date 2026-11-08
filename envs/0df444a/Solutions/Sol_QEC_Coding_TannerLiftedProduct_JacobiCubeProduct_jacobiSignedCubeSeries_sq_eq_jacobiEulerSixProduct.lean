-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiSignedCubeSeries_sq_eq_jacobiEulerSixProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:24:48.911074+00:00
-- url     : https://prove2.me/submissions/b414f0a9-edd9-4b7b-b6ef-d75c2c972056

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiSignedCubeSeries_eq_eulerProduct_cube
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiEulerSixProduct_eq_eulerProduct_pow_six

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution :
    jacobiSignedCubeSeries ^ 2 = jacobiEulerSixProduct := by
  rw [jacobiSignedCubeSeries_eq_eulerProduct_cube,
    jacobiEulerSixProduct_eq_eulerProduct_pow_six]
  ring
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
