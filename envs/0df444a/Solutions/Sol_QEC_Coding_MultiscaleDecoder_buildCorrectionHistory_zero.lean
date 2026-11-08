-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:50:40.62905+00:00
-- url     : https://prove2.me/submissions/282be240-bbde-4e76-b948-003bb15f6060

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
namespace QEC.Coding.MultiscaleDecoder
theorem _root_.solution
    {A0 A1 A2 : LevelIndex 0 → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData 0 A0 A1 A2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex 0)) :
    buildCorrectionHistory D S B sigma =
      [.base {
        input := sigma
        correction := B.decode sigma
        relation := (B.rightInverse sigma).symm }] := by
  rw [buildCorrectionHistory, buildHistoryAux]
  rfl
end QEC.Coding.MultiscaleDecoder
