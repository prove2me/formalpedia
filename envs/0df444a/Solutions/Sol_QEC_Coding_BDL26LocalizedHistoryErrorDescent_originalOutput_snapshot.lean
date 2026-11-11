-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.originalOutput_snapshot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:08:06.904471+00:00
-- url     : https://prove2.me/submissions/ca56cd72-8e65-42a3-bc8a-68284faf7c77

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_original_input_eq


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
theorem _root_.solution (i : StepIndex n) : originalOutput S n sigma i =
    BDL26CanonicalHistoryMarks.outputAt S n sigma i := by
  change actualStep S (n+2) (Edge n i) (actualInputs S n sigma i.succ)=
    actualStep S (n+2) (Edge n i) (BDL26CanonicalHistoryMarks.inputAt S n sigma i.succ)
  rw [BDL26RZPhysicalXStarTransport.original_input_eq]
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
