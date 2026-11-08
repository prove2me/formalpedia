-- Prove2me | solution 1 for QEC.Coding.MultiscaleDecoder.LevelTwoHistory.suffixOutput_supports
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:54:07.013726+00:00
-- url     : https://prove2.me/submissions/0e84eb5b-7976-47c5-81fc-6b6b44c7c1b5

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_LevelTwoHistory

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.LevelTwoHistory
universe u v
variable {n : Nat}
variable {C0 C1 C2 : LevelIndex (n + 2) → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.MultiscaleDecoder.LevelTwoHistory
theorem _root_.solution (D : BDL26DecoderData (n + 2) C0 C1 C2)
    (i : StepIndex n) (O : AssemblyStepOutput D (physicalStep i)) :
    (suffixOutput D i O).componentSupports = O.componentSupports := rfl
end QEC.Coding.MultiscaleDecoder.LevelTwoHistory
