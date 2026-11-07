-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedTaylor_function
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:26:37.622141+00:00
-- url     : https://prove2.me/submissions/b2ea1640-c7f1-4d00-8be8-73ca130e3ce5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F : lpsOriginalCuspAnalyticSubring) :
    lpsOriginalAnalyticCuspLocalizedTaylor
      (algebraMap lpsOriginalCuspAnalyticSubring lpsOriginalAnalyticCuspLaurentRing F)=
      algebraMap (PowerSeries ℂ) lpsOriginalComplexCuspLaurentRing
        (lpsOriginalCuspTaylorRingHom F) :=
  IsLocalization.Away.lift_eq _ _ _
end QEC.Coding.TannerLiftedProduct
