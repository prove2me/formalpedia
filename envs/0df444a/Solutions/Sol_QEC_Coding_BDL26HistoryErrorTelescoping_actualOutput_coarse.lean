-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.actualOutput_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:41:13.623778+00:00
-- url     : https://prove2.me/submissions/e4d5df82-26f0-4d24-bb5f-8f22c2793043

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_step
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
    (actualOutput S n sigma i).coarse = actualInputs S n sigma i.castSucc :=
  (actualInputs_step S n sigma i).symm
end QEC.Coding.BDL26HistoryErrorTelescoping
