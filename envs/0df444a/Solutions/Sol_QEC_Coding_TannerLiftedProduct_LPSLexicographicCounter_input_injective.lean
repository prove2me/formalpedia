-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:33:00.89157+00:00
-- url     : https://prove2.me/submissions/79aad0b3-6dfd-429d-b10d-a526f86c7c36

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrefixProjection_stream_suffix_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
theorem _root_.solution (q:ℕ):Function.Injective (input q):=by
 intro x y h
 have he:=PrefixProjection.stream_suffix_injective (q::coords x.1) (q::coords y.1) x.2 y.2 (by simp [coords]) h
 exact Prod.ext (coords_injective q (List.cons.inj he.1).2) he.2
end QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
