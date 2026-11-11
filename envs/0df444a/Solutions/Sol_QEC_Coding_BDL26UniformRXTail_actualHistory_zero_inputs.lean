-- Prove2me | solution 1 for QEC.Coding.BDL26UniformRXTail.actualHistory_zero_inputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:53:48.323514+00:00
-- url     : https://prove2.me/submissions/c07ac61e-ceab-4829-b3da-c171c9439a0a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
import Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actualStep_zero_coarse
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_LevelTwoHistory_stoppedHistory_zero_inputs


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26UniformRXTail
theorem _root_.solution (S : OddScale) (n : Nat)
    (sigma : (indexedFamily S (n + 2)).Syndrome (TopIndex (n + 2)))
    (hs : sigma.val = 0) :
    ∀ e ∈ actualHistory S n sigma, e.inputSyndrome.2.val = 0 := by
  exact LevelTwoHistory.stoppedHistory_zero_inputs
    (indexedDecoderData S (n + 2)) (actualAboveTwoSteps S n) (actualBase S n)
    (fun i _ s hz => actualStep_zero_coarse S (n + 2) i s hz) sigma hs
end QEC.Coding.BDL26UniformRXTail
