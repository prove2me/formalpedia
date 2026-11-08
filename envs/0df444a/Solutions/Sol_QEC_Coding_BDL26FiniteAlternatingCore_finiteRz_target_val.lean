-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:13:03.212468+00:00
-- url     : https://prove2.me/submissions/aedd6687-7187-4b91-be13-9a75d02e193c

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
theorem _root_.solution (depth i : Nat) (h : 2 * i + 1 < depth) :
    (finiteRzStepIndex depth i h).succ.val = 2 * i + 2 := rfl
end QEC.Coding.BDL26FiniteAlternatingCore
