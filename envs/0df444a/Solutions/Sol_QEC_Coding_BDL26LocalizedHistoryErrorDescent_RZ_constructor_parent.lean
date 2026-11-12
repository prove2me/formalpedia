-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.RZ_constructor_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:39:27.501107+00:00
-- url     : https://prove2.me/submissions/8f2d72dd-7f33-4ca7-92ef-336b4fd92f95

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_parent_chart
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_parent_chart


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
theorem _root_.solution (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (v : BDL26RZLocalReplacement.RZX (state S (Edge n i).val).presentation S) :
    parent S ((Edge n i).val+1)
      (Vertex.x (BDL26RZPhysicalXStarTransport.upperXChart S (n+2) (Edge n i) h v))=
      BDL26RZPhysicalXStarTransport.rawParent (state S (Edge n i).val).presentation S v :=
  BDL26RZPhysicalXStarTransport.parent_chart S (n+2) (Edge n i) h v
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
