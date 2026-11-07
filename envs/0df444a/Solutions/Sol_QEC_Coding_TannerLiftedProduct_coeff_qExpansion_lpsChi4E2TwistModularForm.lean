-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsChi4E2TwistModularForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:26:58.9022+00:00
-- url     : https://prove2.me/submissions/529c9f9c-9e9a-4085-aca0-e0db046e7b0d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_coeff_qExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 lpsChi4E2TwistModularForm)=
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsChi4E2Character (n:ZMod 4) :=
  lpsChi4E2Twist_coeff_qExpansion n
end QEC.Coding.TannerLiftedProduct
