-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.step_rz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:59:48.093378+00:00
-- url     : https://prove2.me/submissions/46648229-7775-4bfc-b205-41ed5d2b15ec

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
theorem _root_.solution (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) : step S n sigma tau i u=rzResult S n sigma tau i h u := dif_neg h
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
