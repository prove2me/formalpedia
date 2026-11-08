-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:12:08.323333+00:00
-- url     : https://prove2.me/submissions/3eaea0be-0ff8-4291-9a8f-f1e934b9aefc

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Mathlib.LinearAlgebra.StdBasis
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26FiniteAlternatingCore
open MultiscaleDecoder
open Module
attribute [instance] FiniteCochainCarrier.fintypeC0
attribute [instance] FiniteCochainCarrier.fintypeC1
attribute [instance] FiniteCochainCarrier.fintypeC2
namespace QEC.Coding.BDL26FiniteAlternatingCore
theorem _root_.solution (depth i : Nat) (h : 2 * i < depth) :
    (finiteRxStepIndex depth i h).succ.val = 2 * i + 1 := rfl
end QEC.Coding.BDL26FiniteAlternatingCore
