-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsChi4E2ThetaBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:51:48.463664+00:00
-- url     : https://prove2.me/submissions/6a661312-c9be-4a94-8829-db97c3c97ccd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsChi4E2DilateModularForm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (b : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsChi4E2ThetaBasis q b))=
      if q^b.val∣n then -24*(ArithmeticFunction.sigma 1 (n/q^b.val):ℂ)*
        lpsChi4E2Character ((n/q^b.val:ℕ):ZMod 4) else 0 :=
  coeff_qExpansion_lpsChi4E2DilateModularForm _ _ n
end QEC.Coding.TannerLiftedProduct
