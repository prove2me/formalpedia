-- Prove2me | solution 1 for PfaffianRecognition.Recognition.pfaffian_recognition_in_corp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:26:07.949478+00:00
-- url     : https://prove2.me/submissions/23bd2bae-64d5-4a2c-ae2a-5c34f27536d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PfaffianRecognition_CoRP_inCoRP_of_polyProgram
import Theorems.Thm_PfaffianRecognition_CoRP_polyProgram_pfAlg
import Theorems.Thm_PfaffianRecognition_CoRP_pfAlg_complete
import Theorems.Thm_PfaffianRecognition_CoRP_pfAlg_sound

theorem solution : PfaffianRecognition.Recognition.InCoRP PfaffianRecognition.Recognition.pfaffianLanguage :=
  PfaffianRecognition.CoRP.inCoRP_of_polyProgram PfaffianRecognition.Recognition.pfaffianLanguage
    PfaffianRecognition.CoRP.pfAlg PfaffianRecognition.CoRP.polyProgram_pfAlg 8
    (fun w h ρ _ => PfaffianRecognition.CoRP.pfAlg_complete ρ w h)
    (fun w h => PfaffianRecognition.CoRP.pfAlg_sound w h)
