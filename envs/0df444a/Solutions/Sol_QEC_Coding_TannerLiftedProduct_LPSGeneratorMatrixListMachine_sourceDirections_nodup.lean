-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine.sourceDirections_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:31:49.555195+00:00
-- url     : https://prove2.me/submissions/50d3e849-ec20-413a-93f7-bfdc6f5bc6a0

import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionMatrixMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct Turing StateTransition FieldProjection MatrixListQuery
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
theorem _root_.solution {p:ℕ} (hp:p.Prime) (hp4:p%4=1) :
    (sourceDirections hp hp4).Nodup :=by
  apply List.nodup_ofFn_ofInjective
  exact (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4)).injective
end QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
