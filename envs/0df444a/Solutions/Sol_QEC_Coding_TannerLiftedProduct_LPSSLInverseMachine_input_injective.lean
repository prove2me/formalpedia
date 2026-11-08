-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSSLInverseMachine.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:01:15.146015+00:00
-- url     : https://prove2.me/submissions/92c1691c-4ce8-4843-a5da-8110bc60daa9

import Definitions.Def_QEC_Coding_BitTuring_UnaryModularAdjugate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSLInverseMachine
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSMatrixProductMachine_fields_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSSLInverseMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSSLInverseMachine
theorem _root_.solution (q:ℕ) (hq:0<q) : Function.Injective (input q) := by
  intro A B h
  have he:=FieldProjection.stream_injective h
  have hm:=LPSMatrixProductMachine.fields_injective q hq (List.append_cancel_right he)
  exact Subtype.ext hm
end QEC.Coding.TannerLiftedProduct.LPSSLInverseMachine
