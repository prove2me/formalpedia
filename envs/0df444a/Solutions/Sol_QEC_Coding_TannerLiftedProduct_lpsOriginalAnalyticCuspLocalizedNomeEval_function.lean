-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspLocalizedNomeEval_function
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:26:02.35133+00:00
-- url     : https://prove2.me/submissions/27b02517-502c-4925-8de8-e33ca75c89cb

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
    (τ : ℍ) (F : lpsOriginalCuspAnalyticSubring) :
    lpsOriginalAnalyticCuspLocalizedNomeEval τ
      (algebraMap lpsOriginalCuspAnalyticSubring lpsOriginalAnalyticCuspLaurentRing F)=
      F.val (Function.Periodic.qParam 1 (τ:ℂ)) :=
  IsLocalization.Away.lift_eq _ _ _
end QEC.Coding.TannerLiftedProduct
