-- Prove2me | solution 1 for QEC.Coding.BDL26RZLocalEdgeTower.accumulated_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:05:20.248251+00:00
-- url     : https://prove2.me/submissions/85d72d3a-a7e7-4975-a6a9-441622813fd9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_terminal_zero
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_base_calls
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_full_history
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZLocalEdgeTower
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26TransposedStoppedDecoder
open PauliSymplectic
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RZLocalEdgeTower
theorem _root_.solution (S : OddScale) (n : Nat) (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Killed S n q) :
    (SuffixData S n).family.coboundary0 (TopIndex n)
      (BDL26ActualFailureReadout.accumulated S n u q)=
      BDL26LogicalDefectProtection.deltaX S n u q := by
  let b : (SuffixData S n).family.Cochain1 0 :=
    (actualBase S n).decode
      (actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0)
  have hc : (actualBase S n).decode (actualInputs S n (input S n u) 0)=b :=
    (base_calls S n u q t).2.1
  have hz : (descent S n u q).word=0 := terminal_zero S n u q t
  have he := congrArg₂ (fun x y : (SuffixData S n).family.Cochain1 0 => x+y) hz hc
  have hs := congrArg (fun x : (SuffixData S n).family.Cochain1 0 => x+b) he
  have hb : b+b=(0 : (SuffixData S n).family.Cochain1 0) := word_add_self b
  have hbase : (descent S n u q).word+
      (actualBase S n).decode (actualInputs S n (input S n u) 0)+
      (actualBase S n).decode
        (actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0)=0 :=
    hs.trans ((congrArg (fun x : (SuffixData S n).family.Cochain1 0 => x+b)
      (zero_add b)).trans hb)
  have h := BDL26ActualFailureReadout.full_history S n u q
  rw [hbase,map_zero,zero_add] at h
  exact h.symm
end QEC.Coding.BDL26RZLocalEdgeTower
