-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:30:56.549927+00:00
-- url     : https://prove2.me/submissions/3edf8842-5af2-4a96-ae44-2278800b4e70

import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionMatrixMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrime_unary_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct Turing StateTransition FieldProjection MatrixListQuery
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
theorem _root_.solution (p:ℕ) : Function.Injective (fun a:LPSResiduePrime p=>unary a.q) :=
   lpsResiduePrime_unary_injective p
end QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
