-- Prove2me | solution 1 for QEC.Coding.BDL26RXPhysicalCoordinateTrace.trace_semantics
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:48:52.768841+00:00
-- url     : https://prove2.me/submissions/8637e573-ecd4-4c10-9288-a6edea7c7084

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalCoordinateTrace_rx_vertex_supported
import Theorems.Thm_QEC_Coding_BDL26RXPhysicalCoordinateTrace_rz_vertex_supported
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_step
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_pair_original_path
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_pair_original_steps
import Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_pair_supported


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXPhysicalCoordinateTrace
theorem _root_.solution {S : OddScale} {b : Nat} {q : Physical S (b+2)} {leaf : Leaf S}
    (t : Trace S b q leaf) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) (hb : b≤N)
    (hw : hammingSupport (path S N sigma tau top ⟨b,Nat.lt_succ_of_le hb⟩).word ⊆ {q}) :
    LeafMeaning S N sigma tau top leaf := by
  induction t generalizing N with
  | c2 r => exact hw
  | face a =>
      let i : StepIndex N := ⟨0,by omega⟩
      have hs := BDL26RXFaceEdgeTower.seed_step_supported S N sigma tau hb a
        (path S N sigma tau top i.succ) hw
      change hammingSupport (path S N sigma tau top i.castSucc).word ⊆ _
      rw [path_step]
      exact hs
  | rzEdge k ho z e =>
      let i : StepIndex N := ⟨k,by omega⟩
      have hz := BDL26RZLocalEdgeTower.seed_step_zero S N sigma tau i ho
        (path S N sigma tau top i.succ) z e hw
      refine ⟨by omega,?_⟩
      change (path S N sigma tau top i.castSucc).word=0
      rw [path_step]
      exact hz
  | higherFace j a =>
      let hN : 2*j+3≤N := hb
      have hz := BDL26HigherRXFaceTower.seed_two_step_zero S N sigma tau j hN a
        (path S N sigma tau top (BDL26RXQEdgePairTransport.rxIndex N j hN).succ) hw
      have hpair : (BDL26RXQEdgePairTransport.pairResult S N sigma tau j hN
          (path S N sigma tau top (BDL26RXQEdgePairTransport.rxIndex N j hN).succ)).lower.word=0 := by
        rw [BDL26RXQEdgePairTransport.pair_original_steps]
        exact hz
      rw [BDL26RXQEdgePairTransport.pair_original_path] at hpair
      exact ⟨by omega,hpair⟩
  | primitive p => exact ⟨hb,hw⟩
  | @rx k r leaf t he v ih =>
      let i : StepIndex N := ⟨k,by omega⟩
      have hs := (rx_vertex_supported S N sigma tau i he
        (path S N sigma tau top i.succ) r v hw).2
      apply ih N sigma tau top (by omega)
      change hammingSupport (path S N sigma tau top i.castSucc).word ⊆ {r}
      rw [path_step]
      exact hs
  | @rz k r leaf t ho v ih =>
      let i : StepIndex N := ⟨k,by omega⟩
      have hs := rz_vertex_supported S N sigma tau i ho
        (path S N sigma tau top i.succ) r v hw
      apply ih N sigma tau top (by omega)
      change hammingSupport (path S N sigma tau top i.castSucc).word ⊆ {r}
      rw [path_step]
      exact hs
  | qEdgePair j a t ih =>
      let hN : 2*j+3≤N := hb
      have hs := BDL26RXQEdgePairTransport.pair_supported S N sigma tau j hN a
        (path S N sigma tau top (BDL26RXQEdgePairTransport.rxIndex N j hN).succ) hw
      rw [BDL26RXQEdgePairTransport.pair_original_path] at hs
      exact ih N sigma tau top (by omega) hs
end QEC.Coding.BDL26RXPhysicalCoordinateTrace
