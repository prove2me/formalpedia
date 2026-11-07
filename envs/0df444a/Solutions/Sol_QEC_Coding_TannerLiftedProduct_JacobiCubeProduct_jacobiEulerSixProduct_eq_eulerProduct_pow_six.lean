-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiEulerSixProduct_eq_eulerProduct_pow_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:34:13.79107+00:00
-- url     : https://prove2.me/submissions/97918336-c2af-4d72-a571-504b2c12af57

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiEulerSixProduct_eq_tprod_pow


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution :
    jacobiEulerSixProduct = eulerProduct ^ 6 := by
  rw [jacobiEulerSixProduct_eq_tprod_pow]
  rfl
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
