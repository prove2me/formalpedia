-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:41:45.78036+00:00
-- url     : https://prove2.me/submissions/b9daaefc-cd25-49a8-b098-c9419af41c53

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum


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
    (actualOutput S n sigma i).correction = (actualOutput S n sigma i).localComponents.sum :=
  (actualOutput S n sigma i).correction_decomposition
end QEC.Coding.BDL26HistoryErrorTelescoping
