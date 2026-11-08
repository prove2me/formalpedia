-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.ordinal_wrap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:32:59.399188+00:00
-- url     : https://prove2.me/submissions/939158d4-18d7-43e5-a665-b9189dc25ce3

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
theorem _root_.solution {q:ℕ} (x:Tuple q) (h:overflow x=true):ordinal (next x)=0:=by
 simpa only [ordinal,digits_next] using QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank_wrap q (coords x) (coords_lt x) h
end QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
