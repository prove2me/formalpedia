-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexOverflow_iff_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:34:05.173195+00:00
-- url     : https://prove2.me/submissions/ee5d8b36-dca1-4b06-b335-f7c54ab4cc7a

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
theorem _root_.solution (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):
 indexOverflow q i=true ↔ i.val+1=(lpsPSLList q).length:=by
 simp [indexOverflow,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.carried,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.candidate,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.bump]
end QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
