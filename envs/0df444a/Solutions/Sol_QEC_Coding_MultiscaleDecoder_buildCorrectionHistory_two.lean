-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.buildCorrectionHistory_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:24:53.116031+00:00
-- url     : https://prove2.me/submissions/e52a5199-340e-4fa1-8eda-900bda469b64

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
    {A0 A1 A2 : LevelIndex 2 → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData 2 A0 A1 A2) (S : AlternatingStepData D)
    (B : AuditedBaseDecoder D) (sigma : D.family.Syndrome (TopIndex 2)) :
    buildCorrectionHistory D S B sigma =
      [.step 1 (S.step 1 sigma),
       .step 0 (S.step 0 (S.step 1 sigma).coarse),
       .base { input := (S.step 0 (S.step 1 sigma).coarse).coarse
               correction := B.decode (S.step 0 (S.step 1 sigma).coarse).coarse
               relation := (B.rightInverse (S.step 0 (S.step 1 sigma).coarse).coarse).symm }] := by
  unfold buildCorrectionHistory
  rw [buildHistoryAux]
  change CorrectionHistoryEntry.step 1 (S.step 1 sigma) ::
    buildHistoryAux D S B 1 (by decide) (S.step 1 sigma).coarse = _
  rw [buildHistoryAux]
  change CorrectionHistoryEntry.step 1 (S.step 1 sigma) ::
    CorrectionHistoryEntry.step 0 (S.step 0 (S.step 1 sigma).coarse) ::
    buildHistoryAux D S B 0 (by decide) (S.step 0 (S.step 1 sigma).coarse).coarse = _
  rw [buildHistoryAux]
  rfl
end QEC.Coding.MultiscaleDecoder
