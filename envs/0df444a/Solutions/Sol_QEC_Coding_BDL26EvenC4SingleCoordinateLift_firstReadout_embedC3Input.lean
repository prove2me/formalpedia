-- Prove2me | solution 1 for QEC.Coding.BDL26EvenC4SingleCoordinateLift.firstReadout_embedC3Input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:47:12.785167+00:00
-- url     : https://prove2.me/submissions/b61ee9eb-8267-4c12-92a0-e81b4a311ae5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4SingleCoordinateLift
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_step
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_top
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_map2_coarse
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26EvenC4SingleCoordinateLift
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26AlternatingCochain BDL26OwnerIncidenceMasks
open BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical
private theorem headOutput_rz (S : OddScale) (s : TopInput S 2) :
    headOutput S s=BDL26RZDecoderAdapter.rzStepOutput S 4 topRZ topRZ_odd (headInput4 S s) :=
  congrFun (actualStep_rz S 4 topRZ topRZ_odd) (headInput4 S s)
private theorem rx2_coarse_depth_four_eq_three (S : OddScale) (s : TopInput S 1) :
    rx4Coarse S s=rx3Coarse S s := by
  have hb4 := congrFun (actualStep_rx S 4 (2 : StepIndex 4) (by decide)) (rxInput4 S s)
  have hb3 := congrFun (actualStep_rx S 3 (2 : StepIndex 3) (by decide)) (rxInput3 S s)
  have hc4 := BDL26RXDecoderAdapter.rxStepOutput_coarse
    S 4 (2 : StepIndex 4) (by decide) (rxInput4 S s)
  have hc3 := BDL26RXDecoderAdapter.rxStepOutput_coarse
    S 3 (2 : StepIndex 3) (by decide) (rxInput3 S s)
  funext z
  calc
    rx4Coarse S s z=(BDL26RXDecoderAdapter.rxStepOutput S 4 (2 : StepIndex 4)
        (by decide) (rxInput4 S s)).coarse.val z := congrArg (fun O => O.coarse.val z) hb4
    _=rxCoarseWord (BDL26RXDecoderAdapter.rxData S 4 (2 : StepIndex 4)
        (by decide)) (rxInput4 S s).val z := congrFun hc4 z
    _=rxCoarseWord (BDL26RXDecoderAdapter.rxData S 3 (2 : StepIndex 3)
        (by decide)) (rxInput3 S s).val z := by rfl
    _=(BDL26RXDecoderAdapter.rxStepOutput S 3 (2 : StepIndex 3)
        (by decide) (rxInput3 S s)).coarse.val z := (congrFun hc3 z).symm
    _=rx3Coarse S s z := (congrArg (fun O => O.coarse.val z) hb3).symm
private theorem actualTopInput4_eq (S : OddScale) (s : TopInput S 2) :
    actualTopInput4 S s=headInput4 S s := by
  apply Subtype.ext
  exact congrArg Subtype.val (actualInputs_top S 2 s)
private theorem actualInputs_mid (S : OddScale) (s : TopInput S 2) :
    actualInputs S 2 s (1 : LevelIndex 2)=coarseTop S s := by
  have h : actualInputs S 2 s (1 : LevelIndex 2)=
      (actualStep S 4 topRZ (actualTopInput4 S s)).coarse :=
    actualInputs_step S 2 s (1 : StepIndex 2)
  rw [actualTopInput4_eq] at h
  apply Subtype.ext
  exact congrArg Subtype.val h
private theorem midInput4_eq (S : OddScale) (s : TopInput S 2) :
    midInput4 S s=rxInput4 S (coarseTop S s) := by
  apply Subtype.ext
  exact congrArg Subtype.val (actualInputs_mid S s)
private theorem topInput3_eq (S : OddScale) (s : TopInput S 1) :
    topInput3 S s=rxInput3 S s := by
  apply Subtype.ext
  exact congrArg Subtype.val (actualInputs_top S 1 s)
private theorem actualInputs_base (S : OddScale) (s : TopInput S 2) :
    actualInputs S 2 s 0=actualInputs S 1 (coarseTop S s) 0 := by
  have h4 : actualInputs S 2 s (0 : LevelIndex 2)=
      (actualStep S 4 (2 : StepIndex 4) (midInput4 S s)).coarse :=
    actualInputs_step S 2 s (0 : StepIndex 2)
  have h3 : actualInputs S 1 (coarseTop S s) (0 : LevelIndex 1)=
      (actualStep S 3 (2 : StepIndex 3) (topInput3 S (coarseTop S s))).coarse :=
    actualInputs_step S 1 (coarseTop S s) (0 : StepIndex 1)
  rw [midInput4_eq] at h4
  rw [topInput3_eq] at h3
  apply Subtype.ext
  calc
    (actualInputs S 2 s 0).val=rx4Coarse S (coarseTop S s) := congrArg Subtype.val h4
    _=rx3Coarse S (coarseTop S s) := rx2_coarse_depth_four_eq_three S (coarseTop S s)
    _=(actualInputs S 1 (coarseTop S s) 0).val := (congrArg Subtype.val h3).symm
private theorem input_domainOfTop (S : OddScale) (n : Nat) (s : TopInput S n) :
    input S n (domainOfTop S n s)=s := Subtype.ext rfl
private theorem input_coarseInput (S : OddScale) (u : XSyndromeDomain S 2) :
    input S 1 (coarseInput S u)=coarseTop S (input S 2 u) :=
  input_domainOfTop S 1 _
private theorem firstReadout_head_split (S : OddScale) (u : XSyndromeDomain S 2) :
    firstReadout S 2 u=firstReadout S 1 (coarseInput S u) := by
  change (actualInputs S 2 (input S 2 u) 0).val=
    (actualInputs S 1 (input S 1 (coarseInput S u)) 0).val
  rw [input_coarseInput]
  exact congrArg Subtype.val (actualInputs_base S (input S 2 u))
private theorem headInput_embedC3Input (S : OddScale) (u : XSyndromeDomain S 1) :
    headInput4 S (input S 2 (embedC3Input S u))=embeddedHeadInput4 S u := by
  apply Subtype.ext
  funext z
  rfl
private theorem coarseInput_embedC3Input (S : OddScale) (u : XSyndromeDomain S 1) :
    coarseInput S (embedC3Input S u)=u := by
  have ho := BDL26RZDecoderAdapter.rzStepOutput_map2_coarse
    S 4 topRZ topRZ_odd (lowerRZInput4 S u)
  have hi := headInput_embedC3Input S u
  apply Subtype.ext
  funext z
  calc
    (coarseInput S (embedC3Input S u)).val z=
        (headOutput S (input S 2 (embedC3Input S u))).coarse.val z := rfl
    _=(BDL26RZDecoderAdapter.rzStepOutput S 4 topRZ topRZ_odd
        (headInput4 S (input S 2 (embedC3Input S u)))).coarse.val z :=
      congrArg (fun O => O.coarse.val z) (headOutput_rz S (input S 2 (embedC3Input S u)))
    _=(BDL26RZDecoderAdapter.rzStepOutput S 4 topRZ topRZ_odd
        (embeddedHeadInput4 S u)).coarse.val z :=
      congrArg (fun t : (indexedFamily S 4).Syndrome topRZ.succ =>
        (BDL26RZDecoderAdapter.rzStepOutput S 4 topRZ topRZ_odd t).coarse.val z) hi
    _=(lowerRZInput4 S u).val z := congrArg (fun t => t.val z) ho
    _=u.val z := rfl
end QEC.Coding.BDL26EvenC4SingleCoordinateLift
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26EvenC4SingleCoordinateLift
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26AlternatingCochain BDL26OwnerIncidenceMasks
open BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical
namespace QEC.Coding.BDL26EvenC4SingleCoordinateLift
theorem _root_.solution (S : OddScale) (u : XSyndromeDomain S 1) :
    firstReadout S 2 (embedC3Input S u)=firstReadout S 1 u := by
  rw [firstReadout_head_split,coarseInput_embedC3Input]
end QEC.Coding.BDL26EvenC4SingleCoordinateLift
