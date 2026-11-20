-- Prove2me | solution 1 for QEC.Coding.BDL26EvenC4SingleCoordinateLift.deltaX_embedC3Input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:09:34.833998+00:00
-- url     : https://prove2.me/submissions/63843691-35f1-463f-8790-c928250a67dc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4SingleCoordinateLift
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_input_correction
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actualOutput_correction
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_succ
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_top
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_assembledPrefix_zero
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_toggle
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_step
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_top
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_coarse
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_correction
import Theorems.Thm_QEC_Coding_BDL26RZDecoderAdapter_rzStepOutput_map2_coarse
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_one_q_block
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_qBlock_owner
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_coord1_upperQChart
import Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_lower_physicalQ_basis
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26RZPhysicalStarTransport.coord1_upperQChart


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
private theorem twice {I : Type} (w : Word F I) : w+w=0 := by
  funext i
  exact CharTwo.add_self_eq_zero (w i)
private theorem shift {I : Type} (a e : Word F I) : a+(a+e)=e := by
  rw [← add_assoc,twice,zero_add]
private theorem headOutput_rz (S : OddScale) (s : TopInput S 2) :
    headOutput S s=BDL26RZDecoderAdapter.rzStepOutput S 4 topRZ topRZ_odd (headInput4 S s) :=
  congrFun (actualStep_rz S 4 topRZ topRZ_odd) (headInput4 S s)
private theorem rx2_correction_depth_four_eq_three (S : OddScale) (s : TopInput S 1) :
    rx4Word S s=rx3Word S s := by
  have hb4 := congrFun (actualStep_rx S 4 (2 : StepIndex 4) (by decide)) (rxInput4 S s)
  have hb3 := congrFun (actualStep_rx S 3 (2 : StepIndex 3) (by decide)) (rxInput3 S s)
  have hc4 := BDL26RXDecoderAdapter.rxStepOutput_correction
    S 4 (2 : StepIndex 4) (by decide) (rxInput4 S s)
  have hc3 := BDL26RXDecoderAdapter.rxStepOutput_correction
    S 3 (2 : StepIndex 3) (by decide) (rxInput3 S s)
  funext q
  calc
    rx4Word S s q=(BDL26RXDecoderAdapter.rxStepOutput S 4 (2 : StepIndex 4)
        (by decide) (rxInput4 S s)).correction q := congrArg (fun O => O.correction q) hb4
    _=rxCorrectionTotal (BDL26RXDecoderAdapter.rxData S 4 (2 : StepIndex 4)
        (by decide)) (rxInput4 S s).val q := congrFun hc4 q
    _=rxCorrectionTotal (BDL26RXDecoderAdapter.rxData S 3 (2 : StepIndex 3)
        (by decide)) (rxInput3 S s).val q := by rfl
    _=(BDL26RXDecoderAdapter.rxStepOutput S 3 (2 : StepIndex 3)
        (by decide) (rxInput3 S s)).correction q := (congrFun hc3 q).symm
    _=rx3Word S s q := (congrArg (fun O => O.correction q) hb3).symm
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
private theorem output_rx4_word (S : OddScale) (s : TopInput S 2) (q : Physical S 3) :
    (actualOutput S 2 s (0 : StepIndex 2)).correction q=rx4Word S (coarseTop S s) q := by
  have h : (actualOutput S 2 s (0 : StepIndex 2)).correction q=
      (actualStep S 4 (2 : StepIndex 4) (midInput4 S s)).correction q :=
    congrFun (actualOutput_correction S 2 s (0 : StepIndex 2)) q
  exact h.trans (congrArg (fun t : (indexedFamily S 4).Syndrome (Fin.succ (2 : StepIndex 4)) =>
    (actualStep S 4 (2 : StepIndex 4) t).correction q) (midInput4_eq S s))
private theorem output_rx3_word (S : OddScale) (s : TopInput S 1) (q : Physical S 3) :
    (actualOutput S 1 s (0 : StepIndex 1)).correction q=rx3Word S s q := by
  have h : (actualOutput S 1 s (0 : StepIndex 1)).correction q=
      (actualStep S 3 (2 : StepIndex 3) (topInput3 S s)).correction q :=
    congrFun (actualOutput_correction S 1 s (0 : StepIndex 1)) q
  exact h.trans (congrArg (fun t : (indexedFamily S 3).Syndrome (Fin.succ (2 : StepIndex 3)) =>
    (actualStep S 3 (2 : StepIndex 3) t).correction q) (topInput3_eq S s))
private theorem output_head_word (S : OddScale) (s : TopInput S 2) (q : Physical S 4) :
    (actualOutput S 2 s (1 : StepIndex 2)).correction q=headWord S s q := by
  have h : (actualOutput S 2 s (1 : StepIndex 2)).correction q=
      (actualStep S 4 topRZ (actualTopInput4 S s)).correction q :=
    congrFun (actualOutput_correction S 2 s (1 : StepIndex 2)) q
  exact h.trans (congrArg (fun t : (indexedFamily S 4).Syndrome topRZ.succ =>
    (actualStep S 4 topRZ t).correction q) (actualTopInput4_eq S s))
private theorem assembledPrefix_mid (S : OddScale) (s : TopInput S 2) :
    (fun q : Physical S 3 => assembledPrefix S 2 s (1 : LevelIndex 2) q)=
      (fun q : Physical S 3 => assembledPrefix S 1 (coarseTop S s) (TopIndex 1) q) := by
  funext q
  have h4 := congrFun (assembledPrefix_succ S 2 s (0 : StepIndex 2)) q
  have h3 := congrFun (assembledPrefix_succ S 1 (coarseTop S s) (0 : StepIndex 1)) q
  have b4 : ((SuffixData S 2).selectedMap (0 : StepIndex 2)).map1
      (assembledPrefix S 2 s 0) q=
      stepMap1 S 2 (BDL26LevelTwoDecoder.decode S (actualInputs S 2 s 0).val) q :=
    congrArg (fun w : (SuffixData S 2).family.Correction 0 =>
      ((SuffixData S 2).selectedMap (0 : StepIndex 2)).map1 w q)
      (assembledPrefix_zero S 2 s)
  have b3 : ((SuffixData S 1).selectedMap (0 : StepIndex 1)).map1
      (assembledPrefix S 1 (coarseTop S s) 0) q=
      stepMap1 S 2 (BDL26LevelTwoDecoder.decode S (actualInputs S 1 (coarseTop S s) 0).val) q :=
    congrArg (fun w : (SuffixData S 1).family.Correction 0 =>
      ((SuffixData S 1).selectedMap (0 : StepIndex 1)).map1 w q)
      (assembledPrefix_zero S 1 (coarseTop S s))
  have h3' : assembledPrefix S 1 (coarseTop S s) (TopIndex 1) q=
      rx3Word S (coarseTop S s) q+
        stepMap1 S 2 (BDL26LevelTwoDecoder.decode S
          (actualInputs S 1 (coarseTop S s) 0).val) q :=
    h3.trans (congrArg₂ (fun a b : F => a+b) (output_rx3_word S (coarseTop S s) q) b3)
  calc
    assembledPrefix S 2 s (1 : LevelIndex 2) q=
        rx4Word S (coarseTop S s) q+
          stepMap1 S 2 (BDL26LevelTwoDecoder.decode S (actualInputs S 2 s 0).val) q :=
      h4.trans (congrArg₂ (fun a b : F => a+b) (output_rx4_word S s q) b4)
    _=rx3Word S (coarseTop S s) q+
        stepMap1 S 2 (BDL26LevelTwoDecoder.decode S
          (actualInputs S 1 (coarseTop S s) 0).val) q :=
      congrArg₂ (fun a b : F => a+b)
        (congrFun (rx2_correction_depth_four_eq_three S (coarseTop S s)) q)
        (congrArg (fun w : Word F (state S 2).presentation.Z =>
          stepMap1 S 2 (BDL26LevelTwoDecoder.decode S w) q)
          (congrArg Subtype.val (actualInputs_base S s)))
    _=assembledPrefix S 1 (coarseTop S s) (TopIndex 1) q := h3'.symm
private theorem fullCorrection_head_split (S : OddScale) (s : TopInput S 2) :
    (fun q : Physical S 4 => fullCorrection S 2 s q)=headWord S s+
      stepMap1 S 3 (fun q : Physical S 3 => fullCorrection S 1 (coarseTop S s) q) := by
  funext q
  have h := congrFun (assembledPrefix_succ S 2 s (1 : StepIndex 2)) q
  have hm : ((SuffixData S 2).selectedMap (1 : StepIndex 2)).map1
      (assembledPrefix S 2 s (1 : LevelIndex 2)) q=
      stepMap1 S 3 (fun r : Physical S 3 => fullCorrection S 1 (coarseTop S s) r) q := by
    have hmid := assembledPrefix_mid S s
    have htop : (fun r : Physical S 3 =>
        assembledPrefix S 1 (coarseTop S s) (TopIndex 1) r)=
        (fun r : Physical S 3 => fullCorrection S 1 (coarseTop S s) r) :=
      assembledPrefix_top S 1 (coarseTop S s)
    exact congrArg (fun w : Word F (Physical S 3) => stepMap1 S 3 w q) (hmid.trans htop)
  calc
    fullCorrection S 2 s q=assembledPrefix S 2 s (TopIndex 2) q :=
      (congrFun (assembledPrefix_top S 2 s) q).symm
    _=headWord S s q+
        stepMap1 S 3 (fun r : Physical S 3 => fullCorrection S 1 (coarseTop S s) r) q :=
      h.trans (congrArg₂ (fun a b : F => a+b) (output_head_word S s q) hm)
private theorem input_domainOfTop (S : OddScale) (n : Nat) (s : TopInput S n) :
    input S n (domainOfTop S n s)=s := Subtype.ext rfl
private theorem input_coarseInput (S : OddScale) (u : XSyndromeDomain S 2) :
    input S 1 (coarseInput S u)=coarseTop S (input S 2 u) :=
  input_domainOfTop S 1 _
private theorem xCorrection_head_split (S : OddScale) (u : XSyndromeDomain S 2) :
    xCorrection S 2 u=headWord S (input S 2 u)+
      stepMap1 S 3 (xCorrection S 1 (coarseInput S u)) := by
  have hc : (fun q : Physical S 3 => fullCorrection S 1 (coarseTop S (input S 2 u)) q)=
      xCorrection S 1 (coarseInput S u) := by
    have hi := congrArg (fun t : TopInput S 1 =>
      fun q : Physical S 3 => fullCorrection S 1 t q) (input_coarseInput S u)
    have hd : (fun q : Physical S 3 =>
        fullCorrection S 1 (input S 1 (coarseInput S u)) q)=xCorrection S 1 (coarseInput S u) :=
      input_correction S 1 (coarseInput S u)
    exact hi.symm.trans hd
  funext q
  calc
    xCorrection S 2 u q=fullCorrection S 2 (input S 2 u) q :=
      (congrFun (input_correction S 2 u) q).symm
    _=headWord S (input S 2 u) q+
        stepMap1 S 3 (fun r : Physical S 3 => fullCorrection S 1 (coarseTop S (input S 2 u)) r) q :=
      congrFun (fullCorrection_head_split S (input S 2 u)) q
    _=headWord S (input S 2 u) q+stepMap1 S 3 (xCorrection S 1 (coarseInput S u)) q :=
      congrArg (fun w : Word F (Physical S 3) => headWord S (input S 2 u) q+stepMap1 S 3 w q) hc
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
private theorem coordinate_in_qBlock (S : OddScale) (q : Physical S 3)
    (v : BDL26TannerLocalRegularity.QDoubleCylinderVertex
      (transposePresentation (state S 3).presentation) q S) :
    rzOldQCoordinate S q v ∈
      BDL26RZFiniteBlockTransport.qBlocks S 4 topRZ topRZ_odd {q} := by
  have hc : BDL26RZFiniteBlockTransport.coord1 S 4 topRZ topRZ_odd
      (rzOldQCoordinate S q v)=
      (.inr ⟨q,v⟩ : BDL26RZLocalReplacement.RZQ (state S 3).presentation S) :=
    BDL26RZPhysicalStarTransport.coord1_upperQChart S 4 topRZ topRZ_odd (.inr ⟨q,v⟩)
  apply (BDL26RZFiniteBlockTransport.qBlock_owner S 4 topRZ topRZ_odd
    q (rzOldQCoordinate S q v)).mpr
  rw [hc]
  rfl
private theorem physical_delta0 (S : OddScale)
    (p : (indexedFamily S 4).Cochain0 topRZ.succ) :
    (fun q : Physical S 4 => (indexedFamily S 4).coboundary0 topRZ.succ p q)=
      tannerCoboundary0 (state S 4).presentation (physicalPotential S p) := by
  funext q
  exact congrFun (LinearMap.congr_fun (indexedFamily_coboundary0 S 4 topRZ.succ) p) q
private theorem original_singleton_head_pullback (S : OddScale)
    (u : XSyndromeDomain S 2) (q : Physical S 3)
    (v : BDL26TannerLocalRegularity.QDoubleCylinderVertex
      (transposePresentation (state S 3).presentation) q S) :
    ∃ p : Word F (state S 4).presentation.X,
      stepMap1 S 3 (canonicalBasisWord (F:=F) q)=
        canonicalBasisWord (F:=F) (rzOldQCoordinate S q v)+headWord S (input S 2 u)+
          headWord S (input S 2 (translateX S 2 u
            (canonicalBasisWord (F:=F) (rzOldQCoordinate S q v))))+
          tannerCoboundary0 (state S 4).presentation p ∧
      (coarseInput S u).val+
        (coarseInput S (translateX S 2 u
          (canonicalBasisWord (F:=F) (rzOldQCoordinate S q v)))).val=
        zSyndrome S 3 (canonicalBasisWord (F:=F) q) := by
  obtain ⟨a,ha⟩ := u.property
  let e : Word F (Physical S 4) := canonicalBasisWord (F:=F) (rzOldQCoordinate S q v)
  let ua := indexedUpper S a
  let ub := indexedUpper S (a+e)
  have hsA : BDL26RZErrorPullback.errorSyndrome S 4 topRZ ua=
      headInput4 S (input S 2 u) := by
    apply Subtype.ext
    funext z
    have hd := congrFun (LinearMap.congr_fun
      (indexedFamily_coboundary1 S 4 topRZ.succ) ua) z
    exact hd.trans (congrFun ha z)
  have hsB : BDL26RZErrorPullback.errorSyndrome S 4 topRZ ub=
      headInput4 S (input S 2 (translateX S 2 u e)) := by
    apply Subtype.ext
    funext z
    have hd := congrFun (LinearMap.congr_fun
      (indexedFamily_coboundary1 S 4 topRZ.succ) ub) z
    have hm := congrFun (map_add (zSyndrome S 4) a e) z
    exact hd.trans (hm.trans (congrArg (fun c : F => c+zSyndrome S 4 e z) (congrFun ha z)))
  have hrA : BDL26RZErrorPullback.run S 4 topRZ topRZ_odd ua=
      headOutput S (input S 2 u) := by
    rw [BDL26RZErrorPullback.run,hsA,headOutput_rz]
  have hrB : BDL26RZErrorPullback.run S 4 topRZ topRZ_odd ub=
      headOutput S (input S 2 (translateX S 2 u e)) := by
    rw [BDL26RZErrorPullback.run,hsB,headOutput_rz]
  have he : hammingSupport (ua+ub) ⊆
      BDL26RZFiniteBlockTransport.qBlocks S 4 topRZ topRZ_odd {q} := by
    intro r hr
    have hreq : r=rzOldQCoordinate S q v := by
      by_contra hn
      apply (Finset.mem_filter.mp hr).2
      change a r+(a r+e r)=0
      have hz : e r=0 := by
        change Pi.single (M := fun _ : Physical S 4 => F)
          (rzOldQCoordinate S q v) (1 : F) r=0
        apply Pi.single_eq_of_ne
        exact hn
      rw [hz,add_zero,CharTwo.add_self_eq_zero]
    subst r
    exact coordinate_in_qBlock S q v
  obtain ⟨p,hp⟩ := BDL26RZFiniteBlockTransport.one_q_block
    S 4 topRZ topRZ_odd (by decide) q ua ub he
  have hl : BDL26RZFiniteBlockTransport.lowerError S 4 topRZ topRZ_odd ua ub=
      canonicalBasisWord (F:=F) q :=
    BDL26RZPhysicalStarTransport.lower_physicalQ_basis S 4 topRZ topRZ_odd ua q v
  have hword := hp.1
  rw [hl] at hword
  have hw : stepMap1 S 3 (canonicalBasisWord (F:=F) q)=
      e+headWord S (input S 2 u)+headWord S (input S 2 (translateX S 2 u e))+
        tannerCoboundary0 (state S 4).presentation (physicalPotential S p) := by
    funext r
    have h := congrFun hword r
    change stepMap1 S 3 (canonicalBasisWord (F:=F) q) r=
      (a r+(a r+e r))+(BDL26RZErrorPullback.run S 4 topRZ topRZ_odd ua).correction r+
        (BDL26RZErrorPullback.run S 4 topRZ topRZ_odd ub).correction r+
        (indexedFamily S 4).coboundary0 topRZ.succ p r at h
    have hz : a r+(a r+e r)=e r := by
      rw [← add_assoc,CharTwo.add_self_eq_zero,zero_add]
    rw [hz,hrA,hrB] at h
    exact h.trans (congrArg (fun c : F => e r+headWord S (input S 2 u) r+
      headWord S (input S 2 (translateX S 2 u e)) r+c) (congrFun (physical_delta0 S p) r))
  have hcoarse := hp.2.1
  rw [hl,hrA,hrB] at hcoarse
  refine ⟨physicalPotential S p,hw,?_⟩
  funext z
  have hd := congrFun (LinearMap.congr_fun (indexedFamily_coboundary1 S 4 topRZ.castSucc)
    (canonicalBasisWord (F:=F) q)) z
  exact ((congrFun hcoarse z).symm.trans hd)
private theorem coarseInput_perturbed_embed (S : OddScale) (u : XSyndromeDomain S 1)
    (q : Physical S 3)
    (v : BDL26TannerLocalRegularity.QDoubleCylinderVertex (transposePresentation (state S 3).presentation) q S) :
    coarseInput S (translateX S 2 (embedC3Input S u) (BDL26ActualFailureReadout.flip S 2 (rzOldQCoordinate S q v)))=
      translateX S 1 u (BDL26ActualFailureReadout.flip S 1 q) := by
  obtain ⟨p,hword,hc⟩ := original_singleton_head_pullback S (embedC3Input S u) q v
  rw [coarseInput_embedC3Input,← flip_eq_basis S 2 (rzOldQCoordinate S q v),
    ← flip_eq_basis S 1 q] at hc
  apply Subtype.ext
  change (coarseInput S
    (translateX S 2 (embedC3Input S u) (BDL26ActualFailureReadout.flip S 2 (rzOldQCoordinate S q v)))).val=
      u.val+zSyndrome S 3 (BDL26ActualFailureReadout.flip S 1 q)
  calc
    _=u.val+(u.val+(coarseInput S
        (translateX S 2 (embedC3Input S u) (BDL26ActualFailureReadout.flip S 2 (rzOldQCoordinate S q v)))).val) :=
      (shift _ _).symm
    _=u.val+zSyndrome S 3 (BDL26ActualFailureReadout.flip S 1 q) := congrArg (fun w => u.val+w) hc
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
theorem _root_.solution (S : OddScale) (u : XSyndromeDomain S 1)
    (q : Physical S 3)
    (v : BDL26TannerLocalRegularity.QDoubleCylinderVertex (transposePresentation (state S 3).presentation) q S) :
    ∃ p : Word F (state S 4).presentation.X,
      BDL26LogicalDefectProtection.deltaX S 2 (embedC3Input S u) (rzOldQCoordinate S q v)=
        stepMap1 S 3 (BDL26LogicalDefectProtection.deltaX S 1 u q)+
          tannerCoboundary0 (state S 4).presentation p := by
  let u4 := embedC3Input S u
  let q4 := rzOldQCoordinate S q v
  let t3 := translateX S 1 u (BDL26ActualFailureReadout.flip S 1 q)
  let t4 := translateX S 2 u4 (BDL26ActualFailureReadout.flip S 2 q4)
  obtain ⟨p,hp,_⟩ := original_singleton_head_pullback S u4 q v
  rw [← flip_eq_basis S 2 q4,← flip_eq_basis S 1 q] at hp
  have hA := xCorrection_head_split S u4
  have hB := xCorrection_head_split S t4
  rw [coarseInput_embedC3Input] at hA
  rw [coarseInput_perturbed_embed] at hB
  have hE : BDL26ActualFailureReadout.flip S 2 q4+headWord S (input S 2 u4)+
      headWord S (input S 2 t4)=
      stepMap1 S 3 (BDL26ActualFailureReadout.flip S 1 q)+tannerCoboundary0 (state S 4).presentation p :=
    BDL26HistoryErrorTelescoping.word_toggle _ _ _ hp
  refine ⟨p,?_⟩
  change xCorrection S 2 t4+BDL26ActualFailureReadout.flip S 2 q4+xCorrection S 2 u4=
    stepMap1 S 3 (xCorrection S 1 t3+BDL26ActualFailureReadout.flip S 1 q+xCorrection S 1 u)+
      tannerCoboundary0 (state S 4).presentation p
  rw [hB,hA,map_add,map_add]
  calc
    _=(BDL26ActualFailureReadout.flip S 2 q4+headWord S (input S 2 u4)+
        headWord S (input S 2 t4))+
        (stepMap1 S 3 (xCorrection S 1 t3)+stepMap1 S 3 (xCorrection S 1 u)) := by abel
    _=(stepMap1 S 3 (BDL26ActualFailureReadout.flip S 1 q)+tannerCoboundary0 (state S 4).presentation p)+
        (stepMap1 S 3 (xCorrection S 1 t3)+stepMap1 S 3 (xCorrection S 1 u)) :=
      congrArg (fun w => w+(stepMap1 S 3 (xCorrection S 1 t3)+
        stepMap1 S 3 (xCorrection S 1 u))) hE
    _=_ := by abel
end QEC.Coding.BDL26EvenC4SingleCoordinateLift
