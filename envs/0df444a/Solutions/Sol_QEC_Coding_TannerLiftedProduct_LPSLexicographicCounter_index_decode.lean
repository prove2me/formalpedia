-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.index_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:55:56.267007+00:00
-- url     : https://prove2.me/submissions/29d8e975-6eef-460b-aa03-1e67f6296f44

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
theorem _root_.solution (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):
 (lpsPSLEnumerationEquiv q) i=(lpsPSLList q).get i:=rfl
end QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
