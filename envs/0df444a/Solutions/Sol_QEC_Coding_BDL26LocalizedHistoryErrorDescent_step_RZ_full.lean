-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.step_RZ_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:38:43.150098+00:00
-- url     : https://prove2.me/submissions/068d79ed-2c1a-46a8-ac42-f9a5b94247e5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_step_rz
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_oldX_zero
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalXStarTransport_oldX_zero


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
    BDL26RZFiniteBlockTransport.Pullback S (n+2) (Edge n i) h
      (BDL26RZPhysicalXStarTransport.Q0 S (n+2) (Edge n i) h u.center)
      (BDL26RZPhysicalXStarTransport.Z0 S (n+2) (Edge n i) h u.center)
      (first S n sigma i) (second S n sigma tau i u) (step S n sigma tau i u).potential ∧
    (step S n sigma tau i u).lower.word=
      BDL26RZFiniteBlockTransport.lowerError S (n+2) (Edge n i) h
        (first S n sigma i) (second S n sigma tau i u) ∧
    (step S n sigma tau i u).lower.center=
      BDL26RZPhysicalXStarTransport.downX S (n+2) (Edge n i) h u.center ∧
    (∀ x : (state S (Edge n i).val).presentation.X, ∀ c : BDL26FiniteTannerSquare.Two,
      BDL26RZFiniteBlockTransport.read0 S (n+2) (Edge n i) h
        (step S n sigma tau i u).potential (.inr (x,c))=0) := by
  rw [step_rz S n sigma tau i h u]
  have hp := rzPotential_full S n sigma tau i h u
  exact ⟨hp,rfl,rfl,BDL26RZPhysicalXStarTransport.oldX_zero S (n+2) (Edge n i) h
    u.center _ _ _ hp⟩
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
