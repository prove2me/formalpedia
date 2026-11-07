-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsChi4PrimeE2TwistModularForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:26:03.585873+00:00
-- url     : https://prove2.me/submissions/4b2b7f08-44e8-408c-a058-a8850cd126e0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4PrimeE2Twist_coeff_qExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4PrimeE2TwistModularForm q hq2))=
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*lpsChi4E2Character (n:ZMod 4) :=
  lpsChi4PrimeE2Twist_coeff_qExpansion q hq2 n
end QEC.Coding.TannerLiftedProduct
