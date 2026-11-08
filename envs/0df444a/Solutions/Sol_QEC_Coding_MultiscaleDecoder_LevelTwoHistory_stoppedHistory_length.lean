-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.LevelTwoHistory.stoppedHistory_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:54:37.880637+00:00
-- url     : https://prove2.me/submissions/0b6c69a6-375a-4013-9e98-28c5e0f8c557

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_terminates


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.MultiscaleDecoder.LevelTwoHistory
theorem _root_.solution (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (S : AboveTwoSteps D) (B : AuditedBaseDecoder (suffixData D))
    (sigma : D.family.Syndrome (TopIndex (n + 2))) :
    (stoppedHistory D S B sigma).length = n + 1 :=
  buildCorrectionHistory_terminates (suffixData D) (suffixSteps D S) B sigma
end QEC.Coding.MultiscaleDecoder.LevelTwoHistory
