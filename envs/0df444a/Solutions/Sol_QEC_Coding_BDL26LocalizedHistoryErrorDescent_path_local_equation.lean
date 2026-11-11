-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.path_local_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:27:12.047753+00:00
-- url     : https://prove2.me/submissions/f193fd3c-cf7d-4616-ba33-7dde5c5e0b3c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_step

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
theorem _root_.solution (i : StepIndex n) :
    ((Data S n).selectedMap i).map1 (path S n sigma tau top i.castSucc).word=
      (path S n sigma tau top i.succ).word+
        (actualOutput S n sigma i).correction+(actualOutput S n tau i).correction+
        (Data S n).family.coboundary0 i.succ (edgePotential S n sigma tau top i) := by
  rw [path_step]
  exact (step S n sigma tau i (path S n sigma tau top i.succ)).equation
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
