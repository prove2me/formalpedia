-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsQuadraticE2ThetaBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:52:21.311066+00:00
-- url     : https://prove2.me/submissions/59114ae1-8ad8-441e-b7a3-8d0ae9b2fcef

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsQuadraticE2DilateModularForm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : Fin 5) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsQuadraticE2ThetaBasis q hq2 a))=
      if 2^a.val∣n then -24*(ArithmeticFunction.sigma 1 (n/2^a.val):ℂ)*
        lpsQuadraticE2Character q ((n/2^a.val:ℕ):ZMod q) else 0 :=
  coeff_qExpansion_lpsQuadraticE2DilateModularForm q hq2 _ _ n
end QEC.Coding.TannerLiftedProduct
