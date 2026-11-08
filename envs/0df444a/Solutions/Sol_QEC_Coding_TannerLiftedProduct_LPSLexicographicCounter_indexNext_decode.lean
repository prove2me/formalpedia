-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter.indexNext_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:33:10.865115+00:00
-- url     : https://prove2.me/submissions/000061c6-2966-471b-bb87-e5ea2ae63953

import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSVertexEnumeration
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_indexNext_val
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_index_decode

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
theorem _root_.solution (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length)
 (hi:i.val+1<(lpsPSLList q).length):
 (lpsPSLEnumerationEquiv q) (indexNext q i)=(lpsPSLList q).get ⟨i.val+1,hi⟩:=by
 rw [index_decode]
 congr 1
 apply Fin.ext
 rw [indexNext_val,Nat.mod_eq_of_lt hi]
end QEC.Coding.TannerLiftedProduct.LPSLexicographicCounter
