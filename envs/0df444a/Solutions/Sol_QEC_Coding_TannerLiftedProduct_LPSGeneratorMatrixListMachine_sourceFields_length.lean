-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine.sourceFields_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:14:24.557993+00:00
-- url     : https://prove2.me/submissions/bd772c8f-34ec-4f6b-83f8-b08c5c424d20

import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionMatrixMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSGeneratorMatrixListMachine_sourceDirections_length

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct Turing StateTransition FieldProjection MatrixListQuery
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
theorem _root_.solution {p:ℕ} (a:LPSResiduePrime p) :
    (listFields a (sourceDirections a.degreePrime a.degreeModFour)).length=4*(p+1) :=by
  rw [listFields_length,sourceDirections_length]
end QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
