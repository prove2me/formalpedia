-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.LevelTwoHistory.stoppedHistory_base_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:55:11.0472+00:00
-- url     : https://prove2.me/submissions/69d12797-46bf-49be-8b1a-12945351f06d

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_syndromeReadout_physical
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_base_readout


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.MultiscaleDecoder.LevelTwoHistory
theorem _root_.solution
    (D : BDL26DecoderData (n + 2) C0 C1 C2) (S : AboveTwoSteps D)
    (B : AuditedBaseDecoder (suffixData D))
    (sigma : D.family.Syndrome (TopIndex (n + 2))) :
    syndromeReadout D (stoppedHistory D S B sigma) (physicalLevel (0 : LevelIndex n)) =
      (terminalInput (suffixData D) (suffixSteps D S) sigma).val := by
  rw [syndromeReadout_physical]
  exact buildCorrectionHistory_base_readout (suffixData D) (suffixSteps D S) B sigma
end QEC.Coding.MultiscaleDecoder.LevelTwoHistory
