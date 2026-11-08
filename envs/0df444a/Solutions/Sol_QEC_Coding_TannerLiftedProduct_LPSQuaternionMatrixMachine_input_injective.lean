-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSQuaternionMatrixMachine.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:25:16.885796+00:00
-- url     : https://prove2.me/submissions/425b67ba-eb5a-4e48-8889-0518872382b2

import Definitions.Def_QEC_Coding_BitTuring_UnaryQuaternionMatrix
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRecordMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionMatrixMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrime_unary_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSQuaternionMatrixMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open FieldProjection
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSQuaternionMatrixMachine
theorem _root_.solution (p:ℕ) : Function.Injective (fun a:LPSResiduePrime p=>unary a.q) :=
  lpsResiduePrime_unary_injective p
end QEC.Coding.TannerLiftedProduct.LPSQuaternionMatrixMachine
