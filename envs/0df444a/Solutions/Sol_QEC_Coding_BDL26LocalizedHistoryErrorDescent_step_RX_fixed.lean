-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.step_RX_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:09:42.078762+00:00
-- url     : https://prove2.me/submissions/e63d8170-9328-47a6-90b4-f574a4b48406

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_step_rx
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalStarTransport_parent_computed
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_parent_computed


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
theorem _root_.solution (i : StepIndex n) (h : (Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    (step S n sigma tau i u).lower.word=
      BDL26RXPhysicalStarTransport.L S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u) ∧
    (step S n sigma tau i u).potential=
      BDL26RXPhysicalStarTransport.Phi S (n+2) (Edge n i) h u.center
        (first S n sigma i) (second S n sigma tau i u) ∧
    parent S ((Edge n i).val+1) (Vertex.x u.center)=
      some (Vertex.x (step S n sigma tau i u).lower.center) := by
  rw [step_rx S n sigma tau i h u]
  exact ⟨rfl,rfl,BDL26RXPhysicalStarTransport.parent_computed S (n+2) (Edge n i) h u.center⟩
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
