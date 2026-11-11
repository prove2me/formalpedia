-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.actualOutput_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:12:19.155325+00:00
-- url     : https://prove2.me/submissions/dafd7aec-7adc-4d0d-99f1-6ebe9ef3efff

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (sigma : TopInput S n) (i : StepIndex n) :
    (actualOutput S n sigma i).correction =
      (actualStep S (n+2) (LevelTwoHistory.physicalStep i)
        (actualInputs S n sigma i.succ)).correction := rfl
end QEC.Coding.BDL26HistoryErrorTelescoping
