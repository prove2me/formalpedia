-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.rawTuples_filterMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:34:03.749607+00:00
-- url     : https://prove2.me/submissions/1f9cd8d7-1a7f-46d0-9b94-f2febe901108

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
theorem _root_.solution (q:ℕ):
 (rawTuples q).filterMap (fun x=>lpsSLMatrixCandidate q x.1 x.2.1 x.2.2.1 x.2.2.2)=lpsSLList q:=by
 simp only [rawTuples,lpsSLList,List.filterMap_flatMap,List.filterMap_map,Function.comp_def]
end QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
