-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine.scalar_normalizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:55:28.747196+00:00
-- url     : https://prove2.me/submissions/3050ead4-4d4f-4b8f-af62-afad98be26f8

import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldInverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSquareRootMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSInverseMachine
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSDegreeInverseMachine_scalar_cast

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
namespace QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine
theorem _root_.solution {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    (scalar a:ZMod a.q) • lpsQuaternionMatrix a.q t=(lpsEffectiveQuaternionSL a t ht).val := by
  rw [scalar_cast]
  rfl
end QEC.Coding.TannerLiftedProduct.LPSDegreeInverseMachine
