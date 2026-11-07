-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralCuspComplexMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:41:57.258035+00:00
-- url     : https://prove2.me/submissions/7df1164d-6577-4a72-9145-ee9fab55cdde

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPhaseRing_complexEmbedding_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_injective


set_option autoImplicit false
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) :
    Function.Injective (lpsOriginalCuspCoefficientMap (lpsOriginalLevelPhaseRing N).val.toRingHom) :=
  lpsOriginalCuspCoefficientMap_injective
    (R := lpsOriginalLevelPhaseRing N) (S := ℂ) (lpsOriginalLevelPhaseRing N).val.toRingHom
    (lpsOriginalLevelPhaseRing_complexEmbedding_injective N)
end QEC.Coding.TannerLiftedProduct
