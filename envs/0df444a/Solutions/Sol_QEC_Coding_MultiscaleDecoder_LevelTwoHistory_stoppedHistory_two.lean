-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.LevelTwoHistory.stoppedHistory_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:54:32.293855+00:00
-- url     : https://prove2.me/submissions/26a17439-f930-4e9c-9dd9-36e66c6118c7

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_buildCorrectionHistory_two
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.MultiscaleDecoder.LevelTwoHistory
theorem _root_.solution
    {A0 A1 A2 : LevelIndex 4 → Type u}
    [∀ i, Fintype (A0 i)] [∀ i, Fintype (A1 i)] [∀ i, Fintype (A2 i)]
    (D : BDL26DecoderData 4 A0 A1 A2) (S : AboveTwoSteps (n := 2) D)
    (B : AuditedBaseDecoder (suffixData (n := 2) D))
    (sigma : D.family.Syndrome (TopIndex 4)) :
    stoppedHistory (n := 2) D S B sigma =
      [.step 1 (suffixOutput D 1 (S.step 3 (by decide) sigma)),
       .step 0 (suffixOutput D 0 (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse)),
       .base { input := (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse).coarse
               correction := B.decode (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse).coarse
               relation := (B.rightInverse
                 (S.step 2 (by decide) (S.step 3 (by decide) sigma).coarse).coarse).symm }] :=
  buildCorrectionHistory_two (suffixData D) (suffixSteps D S) B sigma
end QEC.Coding.MultiscaleDecoder.LevelTwoHistory
