-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexInput_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:33:05.221046+00:00
-- url     : https://prove2.me/submissions/dc6fd12a-8d6e-4819-a7e2-d8f769cc856c

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrefixProjection_stream_suffix_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
theorem _root_.solution (q:ℕ) [Fact q.Prime]:Function.Injective (indexInput q):=by
 intro x y h
 have he:=PrefixProjection.stream_suffix_injective [(lpsPSLList q).length,x.1.val]
  [(lpsPSLList q).length,y.1.val] x.2 y.2 (by rfl) h
 have hi:=List.cons.inj (List.cons.inj he.1).2
 exact Prod.ext (Fin.ext hi.1) he.2
end QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
