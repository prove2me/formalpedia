-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine.sourceDirection_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:17:50.158937+00:00
-- url     : https://prove2.me/submissions/49d190ee-25a4-4647-ade8-916a9883eabe

import Definitions.Def_QEC_Coding_BitTuring_UnaryMatrixListQuery
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionMatrixMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSGeneratorMatrixListMachine_generatorSL_decode
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct Turing StateTransition FieldProjection MatrixListQuery
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
theorem _root_.solution {p:ℕ} (hp:p.Prime) (hp4:p%4=1) (n:ℕ) (j:Fin (p+1)) :
    (QuotientGroup.mk (generatorSL (lpsEffectiveResiduePrimeAt hp hp4 n)
      (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4) j)):
      PSL(2,ZMod (lpsEffectiveResiduePrimeAt hp hp4 n).q))=
        lpsFinQuaternionFamilyLabel hp hp4 (card_lpsQuaternionShell_eq_prime_add_one hp hp4) n j :=by
  rw [generatorSL_decode]
  rfl
end QEC.Coding.TannerLiftedProduct.LPSGeneratorMatrixListMachine
