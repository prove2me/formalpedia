-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsE2DifferenceThetaBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:51:41.453207+00:00
-- url     : https://prove2.me/submissions/0e37d3ef-8e96-4f52-81ea-febb7ff21b70

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsE2DifferenceModularForm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (a : Fin 5) (b : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsE2DifferenceThetaBasis q a b))=
      lpsE2DifferenceCoefficient (2^a.val*q^b.val) n :=
  coeff_qExpansion_lpsE2DifferenceModularForm _ _ n
end QEC.Coding.TannerLiftedProduct
