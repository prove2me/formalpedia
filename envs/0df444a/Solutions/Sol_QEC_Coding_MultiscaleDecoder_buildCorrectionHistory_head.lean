-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:24:51.24955+00:00
-- url     : https://prove2.me/submissions/8fc507b5-e93e-4b54-8720-e7aa2e8c09b2

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly

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
    (n : Nat) {A0 A1 A2 : LevelIndex (n + 1) → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData (n + 1) A0 A1 A2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex (n + 1))) :
    ∃ tail, buildCorrectionHistory D S B sigma =
      CorrectionHistoryEntry.step (Fin.last n) (S.step (Fin.last n) sigma) :: tail := by
  refine ⟨buildHistoryAux D S B n (Nat.le_succ n)
    (S.step (Fin.last n) sigma).coarse, ?_⟩
  rw [buildCorrectionHistory, buildHistoryAux]
  rfl
end QEC.Coding.MultiscaleDecoder
