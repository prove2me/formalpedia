-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:07:17.03316+00:00
-- url     : https://prove2.me/submissions/3cee782e-3a59-469e-85cf-0d0ed8e352d8

import Definitions.Def_QEC_Coding_BitTuring_UnarySignedCoefficient
import Definitions.Def_QEC_Coding_BitTuring_ModulusQuery
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSInverseMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRecordMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrime_unary_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open FieldProjection
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine
theorem _root_.solution (p:ℕ) : Function.Injective (fun a:LPSResiduePrime p=>unary a.q) :=
  lpsResiduePrime_unary_injective p
end QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine
