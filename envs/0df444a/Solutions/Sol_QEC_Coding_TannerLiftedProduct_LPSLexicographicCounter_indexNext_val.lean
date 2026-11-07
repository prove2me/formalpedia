-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexNext_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:55:54.897114+00:00
-- url     : https://prove2.me/submissions/17af381d-7681-40dd-9c74-c00fbae62a76

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_RippleCounter_digit_eq_mod


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
theorem _root_.solution (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):
 (indexNext q i).val=(i.val+1)%(lpsPSLList q).length:=by
 exact QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.digit_eq_mod _ _ true i.isLt
end QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
