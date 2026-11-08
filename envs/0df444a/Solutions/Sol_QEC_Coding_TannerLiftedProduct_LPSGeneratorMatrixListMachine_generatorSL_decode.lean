-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine.generatorSL_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:31:38.020947+00:00
-- url     : https://prove2.me/submissions/a581707e-1450-450f-9d7b-4d7748124aaa

import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionMatrixMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionPSL_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct Turing StateTransition FieldProjection MatrixListQuery
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
theorem _root_.solution {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p) :
    (QuotientGroup.mk (generatorSL a t):PSL(2,ZMod a.q))=lpsQuaternionLabel a t :=by
  exact lpsEffectiveQuaternionPSL_eq a t.val _
end QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
