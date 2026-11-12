-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.represented_RZ_records
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:38:26.889513+00:00
-- url     : https://prove2.me/submissions/04e1c92c-5863-49e3-bad3-8e48f890b5f2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_originalOutput_snapshot
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RZErrorPullback.run S (n+2) (Edge n i) h (first S n sigma i)=
        BDL26CanonicalHistoryMarks.outputAt S n sigma i ∧
      BDL26RZErrorPullback.run S (n+2) (Edge n i) h (second S n sigma tau i u)=
        BDL26CanonicalHistoryMarks.outputAt S n tau i :=
  ⟨(rz_first S n sigma i h).trans (originalOutput_snapshot S n sigma i),
    (rz_second S n sigma tau i h u).trans (originalOutput_snapshot S n tau i)⟩
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
