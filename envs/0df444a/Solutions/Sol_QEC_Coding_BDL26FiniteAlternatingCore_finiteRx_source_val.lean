-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:12:54.452225+00:00
-- url     : https://prove2.me/submissions/30b66845-2671-46ab-8c22-7b694e2f82b9

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
    (finiteRxStepIndex depth i h).castSucc.val = 2 * i := rfl
end QEC.Coding.BDL26FiniteAlternatingCore
