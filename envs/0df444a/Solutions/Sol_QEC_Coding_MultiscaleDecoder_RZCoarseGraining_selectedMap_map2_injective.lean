-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.RZCoarseGraining.selectedMap_map2_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:07:49.43734+00:00
-- url     : https://prove2.me/submissions/5f8d1da0-bb28-4936-bfe7-9e04c5d3b0a3

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_rzMap_map2_injective
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_selectedMap_eq_rz_of_even_input

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RZCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]
open RZCoarseGrainingData
namespace QEC.Coding.MultiscaleDecoder.RZCoarseGraining
theorem _root_.solution (A : RZCoarseGrainingData D i V)
    (hEven : i.succ.val % 2 = 0) : Function.Injective (D.selectedMap i).map2 := by
  rw [selectedMap_eq_rz_of_even_input D i hEven]
  exact rzMap_map2_injective A
end QEC.Coding.MultiscaleDecoder.RZCoarseGraining
