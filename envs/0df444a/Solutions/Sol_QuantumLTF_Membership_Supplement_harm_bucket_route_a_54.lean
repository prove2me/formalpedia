-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.harm_bucket_route_a_54
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T07:14:16.816166+00:00
-- url     : https://prove2.me/submissions/415e8053-7c59-461c-aab0-316b6c031e58

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Comb
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Circs
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketHL54V2
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_1
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_2
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_3
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_4
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_5
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_6
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_7
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_8
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_9
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_10
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54

set_option autoImplicit false

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

lemma hbInitSlotCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (q : ℕ) (hq : q < arity (dHbOf K + 1)) :
    (hbInitSlotCirc as arith n K d q hq).size ≤ 11 * wOf K + 12 := by
  dsimp [hbInitSlotCirc]
  by_cases hq2 : q < 2 * K
  · rw [dif_pos hq2]
    simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, LayeredCircuit.mapWires_size]
    have h1 := arith.copyRegCircuit_size 1
    have h2 := arith.setConstMSBCircuit_size 1 1
    have h3 := arith.ctrlCopyRegCircuit_size (wOf K)
    have h5 := arith.setConstMSBCircuit_size 2 2
    have h6 := arith.ctrlConstXorMSBCircuit_size 2 2
    have h7 := arith.setConstMSBCircuit_size (wOf K) q
    have h8 := arith.setConstMSBCircuit_size 2 3
    have h9 := arith.ctrlConstXorMSBCircuit_size 2 3
    omega
  · by_cases hqB : q < arity (dHbOf K)
    · rw [dif_neg hq2, if_pos hqB]
      simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, LayeredCircuit.mapWires_size]
      have h1 := arith.setConstMSBCircuit_size 1 1
      have h2 := arith.setConstMSBCircuit_size 2 2
      have h3 := arith.setConstMSBCircuit_size (wOf K) q
      have h4 := arith.setConstMSBCircuit_size 2 3
      omega
    · rw [dif_neg hq2, if_neg hqB]
      simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, LayeredCircuit.mapWires_size]
      have h1 := arith.setConstMSBCircuit_size (wOf K)
        (if hb : q - arity (dHbOf K) < (bucketPairs (2 * K)).length then (bucketPairs (2 * K))[q - arity (dHbOf K)].1
          else 2 * K + 1 + (q - arity (dHbOf K)))
      have h2 := arith.setConstMSBCircuit_size (wOf K)
        (if hb : q - arity (dHbOf K) < (bucketPairs (2 * K)).length then (bucketPairs (2 * K))[q - arity (dHbOf K)].2 else 0)
      have h3 := arith.setConstMSBCircuit_size 2 1
      have h4 := arith.setConstMSBCircuit_size (wOf K) q
      have h6 := arith.setConstMSBCircuit_size (wOf K) (q - arity (dHbOf K))
      omega

lemma act_hbInitSlotCirc (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) {l : Fin (2 * K) → Fin (n + 1)} (z : Qubits (totWiresDef as n K d))
    (arr : Fin (arity (dHbOf K + 1)) → Qubits (wR1Hb K))
    (hzAct : z ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l))
    (hzM : z ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l))
    (hzOcc : z ∘ eOccReg as n K d = flatReg (2 * K) (wOf K) (occBitsFn K l))
    (hzRec : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr)
    (q : ℕ) (hq : q < arity (dHbOf K + 1)) (hq0 : arr ⟨q, hq⟩ = fun _ => false) :
    act (hbInitSlotCirc as arith n K d q hq).unitary (ket z) =
      ket (updateOn (eRec2 as n K d) z
        (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (Function.update arr ⟨q, hq⟩ (hbInitArr K l ⟨q, hq⟩)))) := by
  let qF : Fin (arity (dHbOf K + 1)) := ⟨q, hq⟩
  let w := wOf K
  let eSlot := ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) qF
  let slot0 := rec2SlotFn w (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
    (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
  have hz_slot : z = updateOn eSlot z slot0 := by
    symm; apply updateOn_noop
    rw [comp_ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) z arr hzRec qF,
      hq0]; dsimp only [slot0]; rw [rec2SlotFn_zero]
  dsimp only [hbInitSlotCirc]
  by_cases hq2 : q < 2 * K
  · rw [dif_pos hq2]
    have h1K : 1 ≤ K := by omega
    have hq_B2 : q < arity (dHbOf K) := lt_trans hq2 (two_K_lt_B2 h1K)
    simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, LayeredCircuit.id_unitary, act_one]
    let iF : Fin (2 * K) := ⟨q, hq2⟩
    let actB := actBitsFn K l iF
    let actBit : Bool := actB 0
    let naVal : Qubits 1 := fun _ => !actBit
    let mVal : Qubits w := if actBit then mBitsFn K l iF else fun _ => false
    let occVal : Qubits w := if actBit then occBitsFn K l iF else fun _ => false
    let kr1Val : Qubits 2 := if actBit then natToBits 2 0 else natToBits 2 2
    let kindVal : Qubits 2 := if actBit then natToBits 2 0 else natToBits 2 3
    let slot1 := rec2SlotFn w actB (fun _ => false) (fun _ => false) (fun _ => false)
      (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
    let slot2 := rec2SlotFn w naVal (fun _ => false) (fun _ => false) (fun _ => false)
      (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
    let slot3 := rec2SlotFn w naVal mVal (fun _ => false) (fun _ => false)
      (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
    let slot4 := rec2SlotFn w naVal mVal occVal (fun _ => false)
      (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
    let slot5 := rec2SlotFn w naVal mVal occVal (natToBits 2 2)
      (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
    let slot6 := rec2SlotFn w naVal mVal occVal kr1Val
      (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
    let slot7 := rec2SlotFn w naVal mVal occVal kr1Val
      (natToBits w q) (fun _ => false) (fun _ => false) (fun _ => false)
    let slot8 := rec2SlotFn w naVal mVal occVal kr1Val
      (natToBits w q) (natToBits 2 3) (fun _ => false) (fun _ => false)
    have hz_act : z ∘ eActSlot as n K d iF = actB := by
      funext b; have h := congrFun hzAct (finProdFinEquiv (iF, b)); simpa [eActSlot, flatReg, Function.comp_apply] using h
    have hz_m : z ∘ eMSlot as n K d iF = mBitsFn K l iF := by
      funext b; have h := congrFun hzM (finProdFinEquiv (iF, b)); simpa [eMSlot, flatReg, Function.comp_apply] using h
    have hz_occ : z ∘ eOccSlot as n K d iF = occBitsFn K l iF := by
      funext b; have h := congrFun hzOcc (finProdFinEquiv (iF, b)); simpa [eOccSlot, flatReg, Function.comp_apply] using h
    conv_lhs => rw [hz_slot]
    -- c1: copy eActSlot -> eRec2Inact
    rw [act_copyRegOn arith (hSD := eActSlot_disjoint_eRec2Inact as n K d _ _)]
    have hc1_in : updateOn eSlot z slot0 ∘ eRec2Inact as n K d qF = fun _ => false := by
      dsimp only [eSlot, eRec2Inact]; rw [comp_ancRegField_of_eq_slot]; exact rec2SlotFn_comp_0 ..
    have hc1_act : updateOn eSlot z slot0 ∘ eActSlot as n K d iF = actB := by
      dsimp only [eSlot]; rw [updateOn_comp_disjoint _ _ (eRec2Slot_disjoint_eActSlot as n K d qF iF)]; exact hz_act
    have hv1 : (fun j => xor (updateOn eSlot z slot0 (eRec2Inact as n K d qF j))
        (updateOn eSlot z slot0 (eActSlot as n K d iF j))) = actB := by
      funext j
      change xor ((updateOn eSlot z slot0 ∘ eRec2Inact as n K d qF) j)
        ((updateOn eSlot z slot0 ∘ eActSlot as n K d iF) j) = actB j
      rw [hc1_in, hc1_act]; exact xor_false_left _
    rw [hv1]
    have hupd1 : updateOn (eRec2Inact as n K d qF) (updateOn eSlot z slot0) actB = updateOn eSlot z slot1 := by
      dsimp only [eRec2Inact, eSlot, slot0, slot1, qF]
      rw [updateOn_ancRegField_on_slot, updateOn_rec2SlotFn_0]
    rw [hupd1]
    change act _ (act _ (act _ (act _ (act _ (act _ (act _ (act _ (ket (updateOn eSlot z slot1))))))))) = _
    -- c2: setConst 1 1 -> naVal
    rw [act_setConstOn arith]
    have hc2_in : updateOn eSlot z slot1 ∘ eRec2Inact as n K d qF = actB := by
      dsimp only [eSlot, eRec2Inact]; rw [comp_ancRegField_of_eq_slot]; exact rec2SlotFn_comp_0 ..
    have hv2 : (fun i => xor (updateOn eSlot z slot1 (eRec2Inact as n K d qF i)) (natToBits 1 1 i)) = naVal := by
      funext i; have hi0 : i = 0 := Fin.ext (by omega); subst hi0
      change xor ((updateOn eSlot z slot1 ∘ eRec2Inact as n K d qF) 0) (natToBits 1 1 0) = naVal 0
      rw [hc2_in, natToBits_one_one comb]; dsimp only [actBit, naVal]; cases actB 0 <;> rfl
    rw [hv2]
    have hupd2 : updateOn (eRec2Inact as n K d qF) (updateOn eSlot z slot1) naVal = updateOn eSlot z slot2 := by
      dsimp only [eRec2Inact, eSlot, slot1, slot2, qF]
      rw [updateOn_ancRegField_on_slot, updateOn_rec2SlotFn_0]
    rw [hupd2]
    change act _ (act _ (act _ (act _ (act _ (act _ (act _ (ket (updateOn eSlot z slot2)))))))) = _
    -- c3: ctrlCopy eActSlot, eMSlot -> eRec2M
    dsimp only [comb3]
    rw [act_ctrlCopyRegOn arith
      (hCS := eActSlot_disjoint_eMSlot as n K d _ _)
      (hCD := eActSlot_disjoint_eRec2M as n K d _ _)
      (hSD := eMSlot_disjoint_eRec2M as n K d _ _)]
    have hc3_act0 : updateOn eSlot z slot2 (eActSlot as n K d iF 0) = actBit := by
      change (updateOn eSlot z slot2 ∘ eActSlot as n K d iF) 0 = actBit
      dsimp only [eSlot]; rw [updateOn_comp_disjoint _ _ (eRec2Slot_disjoint_eActSlot as n K d qF iF)]
      exact congrFun hz_act 0
    have hc3_mslot : updateOn eSlot z slot2 ∘ eMSlot as n K d iF = mBitsFn K l iF := by
      dsimp only [eSlot]; rw [updateOn_comp_disjoint _ _ (eRec2Slot_disjoint_eMSlot as n K d qF iF)]; exact hz_m
    have hc3_recM : updateOn eSlot z slot2 ∘ eRec2M as n K d qF = fun _ => false := by
      dsimp only [eSlot, eRec2M]; rw [comp_ancRegField_of_eq_slot]; exact rec2SlotFn_comp_1 ..
    have hv3 : (if updateOn eSlot z slot2 (eActSlot as n K d iF 0) then
        fun j => xor (updateOn eSlot z slot2 (eRec2M as n K d qF j))
          (updateOn eSlot z slot2 (eMSlot as n K d iF j))
        else updateOn eSlot z slot2 ∘ eRec2M as n K d qF) = mVal := by
      rw [hc3_act0]; dsimp only [mVal]
      split_ifs
      · funext j
        change xor ((updateOn eSlot z slot2 ∘ eRec2M as n K d qF) j)
          ((updateOn eSlot z slot2 ∘ eMSlot as n K d iF) j) = _
        rw [hc3_recM, hc3_mslot]; exact xor_false_left _
      · exact hc3_recM
    rw [hv3]
    have hupd3 : updateOn (eRec2M as n K d qF) (updateOn eSlot z slot2) mVal = updateOn eSlot z slot3 := by
      dsimp only [eRec2M, eSlot, slot2, slot3, qF]
      rw [updateOn_ancRegField_on_slot, updateOn_rec2SlotFn_1]
    rw [hupd3]
    change act _ (act _ (act _ (act _ (act _ (act _ (ket (updateOn eSlot z slot3))))))) = _
    -- c4: ctrlCopy eActSlot, eOccSlot -> eRec2Occ
    rw [act_ctrlCopyRegOn arith
      (hCS := eActSlot_disjoint_eOccSlot as n K d _ _)
      (hCD := eActSlot_disjoint_eRec2Occ as n K d _ _)
      (hSD := eOccSlot_disjoint_eRec2Occ as n K d _ _)]
    have hc4_act0 : updateOn eSlot z slot3 (eActSlot as n K d iF 0) = actBit := by
      change (updateOn eSlot z slot3 ∘ eActSlot as n K d iF) 0 = actBit
      dsimp only [eSlot]; rw [updateOn_comp_disjoint _ _ (eRec2Slot_disjoint_eActSlot as n K d qF iF)]
      exact congrFun hz_act 0
    have hc4_occslot : updateOn eSlot z slot3 ∘ eOccSlot as n K d iF = occBitsFn K l iF := by
      dsimp only [eSlot]; rw [updateOn_comp_disjoint _ _ (eRec2Slot_disjoint_eOccSlot as n K d qF iF)]; exact hz_occ
    have hc4_recOcc : updateOn eSlot z slot3 ∘ eRec2Occ as n K d qF = fun _ => false := by
      dsimp only [eSlot, eRec2Occ]; rw [comp_ancRegField_of_eq_slot]; exact rec2SlotFn_comp_2 ..
    have hv4 : (if updateOn eSlot z slot3 (eActSlot as n K d iF 0) then
        fun j => xor (updateOn eSlot z slot3 (eRec2Occ as n K d qF j))
          (updateOn eSlot z slot3 (eOccSlot as n K d iF j))
        else updateOn eSlot z slot3 ∘ eRec2Occ as n K d qF) = occVal := by
      rw [hc4_act0]; dsimp only [occVal]
      split_ifs
      · funext j
        change xor ((updateOn eSlot z slot3 ∘ eRec2Occ as n K d qF) j)
          ((updateOn eSlot z slot3 ∘ eOccSlot as n K d iF) j) = _
        rw [hc4_recOcc, hc4_occslot]; exact xor_false_left _
      · exact hc4_recOcc
    rw [hv4]
    have hupd4 : updateOn (eRec2Occ as n K d qF) (updateOn eSlot z slot3) occVal = updateOn eSlot z slot4 := by
      dsimp only [eRec2Occ, eSlot, slot3, slot4, qF]
      rw [updateOn_ancRegField_on_slot, updateOn_rec2SlotFn_2]
    rw [hupd4]
    change act _ (act _ (act _ (act _ (act _ (ket (updateOn eSlot z slot4)))))) = _
    -- c5: setConst 2 2 -> eRec2KR1
    have hstep5 : act ((arith.setConstMSBCircuit 2 2).mapWires (eRec2KR1 as n K d qF)).unitary
        (ket (updateOn eSlot z slot4)) = ket (updateOn eSlot z slot5) := by
      dsimp only [eRec2KR1, eSlot, slot4, slot5, w, qF]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        (1 + wOf K + wOf K) 2 _ 2 (rec2SlotFn_comp_3 ..), updateOn_rec2SlotFn_3]
    rw [show qF = ⟨q, hq⟩ from rfl] at hstep5
    rw [hstep5]
    change act _ (act _ (act _ (act _ (ket (updateOn eSlot z slot5))))) = _
    -- c6: ctrlConstXor 2 2 -> kr1Val
    rw [act_ctrlConstXorOn arith (hCB := eActSlot_disjoint_eRec2KR1 as n K d _ _)]
    have hc6_act0 : updateOn eSlot z slot5 (eActSlot as n K d iF 0) = actBit := by
      change (updateOn eSlot z slot5 ∘ eActSlot as n K d iF) 0 = actBit
      dsimp only [eSlot]; rw [updateOn_comp_disjoint _ _ (eRec2Slot_disjoint_eActSlot as n K d qF iF)]
      exact congrFun hz_act 0
    have hc6_kr1 : updateOn eSlot z slot5 ∘ eRec2KR1 as n K d qF = natToBits 2 2 := by
      dsimp only [eSlot, eRec2KR1]; rw [comp_ancRegField_of_eq_slot]; exact rec2SlotFn_comp_3 ..
    have hv6 : (if updateOn eSlot z slot5 (eActSlot as n K d iF 0) then
        fun j => xor (updateOn eSlot z slot5 (eRec2KR1 as n K d qF j)) (natToBits 2 2 j)
        else updateOn eSlot z slot5 ∘ eRec2KR1 as n K d qF) = kr1Val := by
      rw [hc6_act0]; dsimp only [kr1Val]
      split_ifs
      · funext j
        change xor ((updateOn eSlot z slot5 ∘ eRec2KR1 as n K d qF) j) (natToBits 2 2 j) = _
        rw [hc6_kr1, xor_self_cancel]; exact (congrFun (natToBits_zero comb 2) j).symm
      · exact hc6_kr1
    rw [hv6]
    have hupd6 : updateOn (eRec2KR1 as n K d qF) (updateOn eSlot z slot5) kr1Val = updateOn eSlot z slot6 := by
      dsimp only [eRec2KR1, eSlot, slot5, slot6, qF]
      rw [updateOn_ancRegField_on_slot, updateOn_rec2SlotFn_3]
    rw [hupd6]
    change act _ (act _ (act _ (ket (updateOn eSlot z slot6)))) = _
    -- c7: setConst w q -> eRec2Orig
    have hstep7 : act ((arith.setConstMSBCircuit w q).mapWires (eRec2Orig as n K d qF)).unitary
        (ket (updateOn eSlot z slot6)) = ket (updateOn eSlot z slot7) := by
      dsimp only [eRec2Orig, eSlot, slot6, slot7, w, qF]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        (1 + wOf K + wOf K + 2) (wOf K) _ q (rec2SlotFn_comp_4 ..), updateOn_rec2SlotFn_4]
    rw [show qF = ⟨q, hq⟩ from rfl] at hstep7
    rw [hstep7]
    change act _ (act _ (ket (updateOn eSlot z slot7))) = _
    -- c8: setConst 2 3 -> eRec2Kind
    have hstep8 : act ((arith.setConstMSBCircuit 2 3).mapWires (eRec2Kind as n K d qF)).unitary
        (ket (updateOn eSlot z slot7)) = ket (updateOn eSlot z slot8) := by
      dsimp only [eRec2Kind, eSlot, slot7, slot8, w, qF]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        (wK1Hb K) 2 _ 3 (rec2SlotFn_comp_5 ..), updateOn_rec2SlotFn_5]
    rw [show qF = ⟨q, hq⟩ from rfl] at hstep8
    rw [hstep8]
    change act _ (ket (updateOn eSlot z slot8)) = _
    -- c9: ctrlConstXor 2 3 -> kindVal
    rw [act_ctrlConstXorOn arith (hCB := eActSlot_disjoint_eRec2Kind as n K d _ _)]
    have hc9_act0 : updateOn eSlot z slot8 (eActSlot as n K d iF 0) = actBit := by
      change (updateOn eSlot z slot8 ∘ eActSlot as n K d iF) 0 = actBit
      dsimp only [eSlot]; rw [updateOn_comp_disjoint _ _ (eRec2Slot_disjoint_eActSlot as n K d qF iF)]
      exact congrFun hz_act 0
    have hc9_kind : updateOn eSlot z slot8 ∘ eRec2Kind as n K d qF = natToBits 2 3 := by
      dsimp only [eSlot, eRec2Kind]; rw [comp_ancRegField_of_eq_slot]; exact rec2SlotFn_comp_5 ..
    have hv9 : (if updateOn eSlot z slot8 (eActSlot as n K d iF 0) then
        fun j => xor (updateOn eSlot z slot8 (eRec2Kind as n K d qF j)) (natToBits 2 3 j)
        else updateOn eSlot z slot8 ∘ eRec2Kind as n K d qF) = kindVal := by
      rw [hc9_act0]; dsimp only [kindVal]
      split_ifs
      · funext j
        change xor ((updateOn eSlot z slot8 ∘ eRec2Kind as n K d qF) j) (natToBits 2 3 j) = _
        rw [hc9_kind, xor_self_cancel]; exact (congrFun (natToBits_zero comb 2) j).symm
      · exact hc9_kind
    rw [hv9]
    dsimp only [eRec2Kind, eSlot, qF]
    rw [updateOn_ancRegField_on_slot, updateOn_rec2SlotFn_5]
    rw [updateOn_ancRegSlot_eq as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) z arr hzRec ⟨q, hq⟩]
    have hrec_eq : ancRegSlice as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) =
        eRec2 as n K d := rfl
    rw [hrec_eq]
    apply congrArg ket; apply congrArg (updateOn (eRec2 as n K d) z)
    apply congrArg (flatReg (arity (dHbOf K + 1)) (wR1Hb K)); apply congrArg (Function.update arr ⟨q, hq⟩)
    dsimp only [hbInitArr, hbRecToBits]
    rw [hbInit_getElem_lt_2K l hq2 hq_B2]
    change _ = rec2SlotFn w (natToBits 1 (hbInactive (if 2 ≤ runOffset l iF then _ else _))) _ _ _ _ _ _ _
    by_cases hact : actBit = true
    · have h2le : 2 ≤ runOffset l iF := by
        dsimp [actBit, actB, actBitsFn] at hact; exact of_decide_eq_true hact
      rw [if_pos h2le]
      dsimp only [hbInactive, hbKindRank1]
      simp only [↓reduceIte]
      have hna : naVal = natToBits 1 0 := by
        dsimp only [naVal]; rw [hact]; simpa using (natToBits_zero comb 1).symm
      have hm : mVal = natToBits w (runOffset l iF) := by dsimp [mVal]; rw [if_pos hact]; rfl
      have ho : occVal = natToBits w (runOcc l iF) := by
        dsimp [occVal, occBitsFn]; rw [if_pos hact, if_pos h2le]
      have hkr : kr1Val = natToBits 2 0 := by dsimp [kr1Val]; rw [if_pos hact]
      have hk : kindVal = natToBits 2 0 := by dsimp [kindVal]; rw [if_pos hact]
      have hd0 : (fun _ : Fin w => false) = natToBits w 0 := (natToBits_zero comb w).symm
      rw [hna, hm, ho, hkr, hk, hd0]; norm_num; rfl
    · have hf : actBit = false := Bool.eq_false_iff.mpr hact
      have hnot2 : ¬ 2 ≤ runOffset l iF := fun h2 => hact (by dsimp [actBit, actB, actBitsFn]; exact decide_eq_true h2)
      rw [if_neg hnot2]
      dsimp only [hbInactive, hbKindRank1]
      simp only [↓reduceIte, OfNat.ofNat_ne_zero]
      have hna : naVal = natToBits 1 1 := by
        dsimp only [naVal]; rw [hf]; simpa using (natToBits_one_one comb).symm
      have hm : mVal = natToBits w 0 := by dsimp [mVal]; rw [if_neg hact, natToBits_zero comb]
      have ho : occVal = natToBits w 0 := by dsimp [occVal]; rw [if_neg hact, natToBits_zero comb]
      have hkr : kr1Val = natToBits 2 2 := by dsimp [kr1Val]; rw [if_neg hact]
      have hk : kindVal = natToBits 2 3 := by dsimp [kindVal]; rw [if_neg hact]
      have hd0 : (fun _ : Fin w => false) = natToBits w 0 := (natToBits_zero comb w).symm
      rw [hna, hm, ho, hkr, hk, hd0]; norm_num; rfl
  · by_cases hqB : q < arity (dHbOf K)
    · rw [dif_neg hq2, dif_pos hqB]
      simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, LayeredCircuit.id_unitary, act_one]
      conv_lhs => rw [hz_slot]
      dsimp only [eRec2Inact, eRec2KR1, eRec2Orig, eRec2Kind, eSlot, slot0, w, qF]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        0 1 _ 1 (rec2SlotFn_comp_0 ..), updateOn_rec2SlotFn_0]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        (1 + wOf K + wOf K) 2 _ 2 (rec2SlotFn_comp_3 ..), updateOn_rec2SlotFn_3]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        (1 + wOf K + wOf K + 2) (wOf K) _ q (rec2SlotFn_comp_4 ..), updateOn_rec2SlotFn_4]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        (wK1Hb K) 2 _ 3 (rec2SlotFn_comp_5 ..), updateOn_rec2SlotFn_5]
      rw [updateOn_ancRegSlot_eq as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) z arr hzRec ⟨q, hq⟩]
      have hrec_eq : ancRegSlice as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) =
          eRec2 as n K d := rfl
      rw [hrec_eq]
      apply congrArg ket; apply congrArg (updateOn (eRec2 as n K d) z)
      apply congrArg (flatReg (arity (dHbOf K + 1)) (wR1Hb K)); apply congrArg (Function.update arr ⟨q, hq⟩)
      dsimp only [hbInitArr, hbRecToBits]
      rw [hbInit_getElem_mid l hq2 hqB]
      dsimp only [hbInactive, hbKindRank1]
      simp only [↓reduceIte, OfNat.ofNat_ne_zero]
      have hz0 : (fun _ : Fin (wOf K) => false) = natToBits (wOf K) 0 := (natToBits_zero comb (wOf K)).symm
      rw [hz0]; norm_num
    · rw [dif_neg hq2, dif_neg hqB]
      simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, LayeredCircuit.id_unitary, act_one]
      conv_lhs => rw [hz_slot]
      let b := q - arity (dHbOf K)
      let pair := bucketPairs (2 * K)
      let mb := if hb : b < pair.length then pair[b].1 else 2 * K + 1 + b
      let occb := if hb : b < pair.length then pair[b].2 else 0
      dsimp only [eRec2M, eRec2Occ, eRec2KR1, eRec2Orig, eRec2Kind, eRec2Dest, eSlot, slot0, w, qF]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        1 (wOf K) _ mb (rec2SlotFn_comp_1 ..), updateOn_rec2SlotFn_1]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        (1 + wOf K) (wOf K) _ occb (rec2SlotFn_comp_2 ..), updateOn_rec2SlotFn_2]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        (1 + wOf K + wOf K) 2 _ 1 (rec2SlotFn_comp_3 ..), updateOn_rec2SlotFn_3]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        (1 + wOf K + wOf K + 2) (wOf K) _ q (rec2SlotFn_comp_4 ..), updateOn_rec2SlotFn_4]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        (wK1Hb K) 2 _ 1 (rec2SlotFn_comp_5 ..), updateOn_rec2SlotFn_5]
      rw [act_setConst_ancRegField_zero as arith n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z ⟨q, hq⟩ _
        (wK1Hb K + 2) (wOf K) _ b (rec2SlotFn_comp_6 ..), updateOn_rec2SlotFn_6]
      rw [updateOn_ancRegSlot_eq as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) z arr hzRec ⟨q, hq⟩]
      have hrec_eq : ancRegSlice as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) =
          eRec2 as n K d := rfl
      rw [hrec_eq]
      apply congrArg ket; apply congrArg (updateOn (eRec2 as n K d) z)
      apply congrArg (flatReg (arity (dHbOf K + 1)) (wR1Hb K)); apply congrArg (Function.update arr ⟨q, hq⟩)
      dsimp only [hbInitArr, hbRecToBits]
      rw [hbInit_getElem_ge_B2 l hqB hq]
      dsimp only [mb, occb, hbInactive, hbKindRank1, b, pair]
      by_cases hb : q - arity (dHbOf K) < (bucketPairs (2 * K)).length
      · have hz0 : (fun _ : Fin 1 => false) = natToBits 1 0 := (natToBits_zero comb 1).symm
        simp only [hb, ↓reduceDIte]
        norm_num
        rw [hz0]
      · have hz01 : (fun _ : Fin 1 => false) = natToBits 1 0 := (natToBits_zero comb 1).symm
        have hz0w : (fun _ : Fin (wOf K) => false) = natToBits (wOf K) 0 := (natToBits_zero comb (wOf K)).symm
        simp only [hb, ↓reduceDIte]
        norm_num
        rw [hz01, hz0w]

lemma hbInitCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) :
    (hbInitCirc as arith n K d).size ≤ arity (dHbOf K + 1) * (11 * wOf K + 12) := by
  dsimp [hbInitCirc]
  have h := LayeredCircuit_seqList_size_le
    ((List.range (arity (dHbOf K + 1))).map fun q =>
      if hq : q < arity (dHbOf K + 1) then hbInitSlotCirc as arith n K d q hq else LayeredCircuit.id _)
    (11 * wOf K + 12)
    (by
      intro lc hlc; simp only [List.mem_map] at hlc; rcases hlc with ⟨q, _, rfl⟩
      split_ifs with hq
      · exact hbInitSlotCirc_size as arith n K d q hq
      · simp)
  simpa using h

lemma act_hbInitCirc (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) {l : Fin (2 * K) → Fin (n + 1)} (z : Qubits (totWiresDef as n K d))
    (hzAct : z ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l))
    (hzM : z ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l))
    (hzOcc : z ∘ eOccReg as n K d = flatReg (2 * K) (wOf K) (occBitsFn K l))
    (hzRec : z ∘ ancEmb as n K d ⟨11, by decide⟩ = fun _ => false) :
    act (hbInitCirc as arith n K d).unitary (ket z) =
      ket (updateOn (eRec2 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hbInitArr K l))) := by
  let arrP (p : ℕ) (q : Fin (arity (dHbOf K + 1))) : Qubits (wR1Hb K) :=
    if q.1 < p then hbInitArr K l q else fun _ => false
  let st (p : ℕ) : Qubits (totWiresDef as n K d) :=
    updateOn (eRec2 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (arrP p))
  have h0 : st 0 = z := by
    apply updateOn_noop; funext idx
    rcases finProdFinEquiv.surjective idx with ⟨⟨q, b⟩, rfl⟩
    have hzr : z (eRec2 as n K d (finProdFinEquiv (q, b))) = false := congrFun hzRec _
    simp [hzr, arrP, flatReg]
  conv_lhs => rw [← h0]
  dsimp [hbInitCirc]
  have hloop := act_seqList_range st
    (fun q => if hq : q < arity (dHbOf K + 1) then hbInitSlotCirc as arith n K d q hq else LayeredCircuit.id _)
    (arity (dHbOf K + 1))
    (fun q hq => by
      rw [dif_pos hq]
      have hzA' : st q ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l) := by
        dsimp only [st]; rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_eActReg as n K d)]; exact hzAct
      have hzM' : st q ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l) := by
        dsimp only [st]; rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_eMReg as n K d)]; exact hzM
      have hzO' : st q ∘ eOccReg as n K d = flatReg (2 * K) (wOf K) (occBitsFn K l) := by
        dsimp only [st]; rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_eOccReg as n K d)]; exact hzOcc
      have hzR' : st q ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (arrP q) :=
        updateOn_comp_emb _ _ _
      have hq0 : arrP q ⟨q, hq⟩ = fun _ => false := by dsimp [arrP]; simp
      have hs := act_hbInitSlotCirc comb as arith n K d (st q) (arrP q) hzA' hzM' hzO' hzR' q hq hq0
      rw [hs]
      dsimp only [st]
      rw [updateOn_idem]
      apply congrArg ket; apply congrArg (updateOn (eRec2 as n K d) z)
      apply congrArg (flatReg (arity (dHbOf K + 1)) (wR1Hb K)); funext r
      by_cases hr : r = ⟨q, hq⟩
      · subst hr; simp [arrP]
      · rw [Function.update_of_ne hr]
        have hne : r.1 ≠ q := fun hv => hr (Fin.ext hv)
        by_cases hlt : r.1 < q
        · simp [arrP, hlt, Nat.lt_trans hlt (Nat.lt_succ_self _)]
        · simp [arrP, hlt, show ¬ r.1 < q + 1 by omega])
  rw [hloop]
  dsimp only [st]
  have harr : arrP (arity (dHbOf K + 1)) = hbInitArr K l := funext fun q => by
    dsimp only [arrP]; rw [if_pos q.isLt]
  rw [harr]

/-! #### 7.4 Sorting 1 (`sortHb1Circ` & `hb1SortedList`) -/

lemma sortHb1Circ_size (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ) :
    ((sortHb1Circ as br n K d).size : ℝ) ≤
      br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + 1) := by
  dsimp [sortHb1Circ]
  rw [LayeredCircuit.mapWires_size]
  simpa [wR1Hb, add_assoc] using br.bitonicSortKeyCircuit_size (dHbOf K + 1) (wK1Hb K) (wP1Hb K) true

lemma act_sortHb1Circ (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ)
    {l : Fin (2 * K) → Fin (n + 1)} (z : Qubits (totWiresDef as n K d))
    (hzRec : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hbInitArr K l))
    (hzTr : z ∘ ancEmb as n K d ⟨12, by decide⟩ = fun _ => false)
    (hzAnc : z ∘ ancEmb as n K d ⟨17, by decide⟩ = fun _ => false) :
    act (sortHb1Circ as br n K d).unitary (ket z) =
      ket (updateOn (eTr2a as n K d)
        (updateOn (eRec2 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (rec2SortedArr K l)))
        (rec2SortTr K l)) := by
  dsimp only [sortHb1Circ]
  have htr : z ∘ eTr2a as n K d = fun _ => false := funext fun j => congrFun hzTr _
  have hanc : z ∘ eSort2aAnc as n K d = fun _ => false := funext fun k => congrFun hzAnc _
  have hcomp := comp_packDTA54Emb (eRec2 as n K d) (eTr2a as n K d) (eSort2aAnc as n K d)
    (eRec2_disjoint_eTr2a as n K d) (eRec2_disjoint_eSort2aAnc as n K d) (eTr2a_disjoint_eSort2aAnc as n K d)
    z (hbInitArr K l) (fun _ => false) hzRec htr hanc
  have hact := act_mapWires_ket_singleton _ _ z _ (by
    rw [hcomp]
    exact br.act_bitonicSortKeyCircuit_ket (dHbOf K + 1) (wK1Hb K) (wP1Hb K) true (hbInitArr K l))
  rw [hact]
  congr 1
  exact updateOn_packDTA54_eq_two (eRec2 as n K d) (eTr2a as n K d) (eSort2aAnc as n K d)
    (eRec2_disjoint_eTr2a as n K d) (eRec2_disjoint_eSort2aAnc as n K d) (eTr2a_disjoint_eSort2aAnc as n K d)
    z hanc (rec2SortedArr K l) (rec2SortTr K l)

lemma rec2SortedArr_eq_hb1Spec (comb : LcgSym54Comb) (br : BitonicRouting54) {n K : ℕ} (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) :
    rec2SortedArr K l = hb1ArrOfList K (hb1SortedList K l) (hb1SortedList_length K l) (fun _ _ => false) := by
  let key : Qubits (wR1Hb K) → ℕ := fun r => bitsToNat (recKey54 r)
  let L₁ : List (Qubits (wR1Hb K)) := List.ofFn (rec2SortedArr K l)
  let L₂ : List (Qubits (wR1Hb K)) := (hb1SortedList K l).map (fun r => hbRecToBits (wOf K) r (fun _ => false))
  have hofFn_init : List.ofFn (hbInitArr K l) =
      (hbInit (2 * K) (arity (dHbOf K)) l).map (fun r => hbRecToBits (wOf K) r (fun _ => false)) := by
    apply List.ext_getElem
    · simp [hbInit_length, arity_eq_two_pow, pow_succ']
    · intro idx h1 h2
      rw [List.length_ofFn] at h1
      simp only [List.getElem_ofFn, List.getElem_map, hbInitArr]
  have hperm12 : L₁.Perm L₂ := by
    have hp1 : L₁.Perm (List.ofFn (hbInitArr K l)) :=
      br.sort_perm key (dHbOf K + 1) true (hbInitArr K l)
    rw [hofFn_init] at hp1
    have hp_ms : List.Perm (hbInit (2 * K) (arity (dHbOf K)) l) (hb1SortedList K l) :=
      (List.mergeSort_perm _ _).symm
    exact hp1.trans (hp_ms.map _)
  have hp1 : L₁.Pairwise (fun x y => key x ≤ key y) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_ofFn] at hi hj
    simp only [L₁, List.getElem_ofFn]
    exact br.monotone_sort key (dHbOf K + 1) (hbInitArr K l) (Nat.le_of_lt hij)
  have hpw_s1 : (hb1SortedList K l).Pairwise (fun a b => hbKey1 a ≤ hbKey1 b) := by
    have hpw : (hb1SortedList K l).Pairwise (fun a b => decide (hbKey1 a ≤ hbKey1 b) = true) := by
      dsimp [hb1SortedList]
      exact List.pairwise_mergeSort
        (fun a b c => by simp only [decide_eq_true_eq]; exact le_trans)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
        (hbInit (2 * K) (arity (dHbOf K)) l)
    exact hpw.imp (fun {a b} h => decide_eq_true_eq.mp h)
  have hbnd : ∀ r ∈ hb1SortedList K l, r.m < 2 ^ wOf K ∧ r.occ < 2 ^ wOf K ∧ r.orig < 2 ^ wOf K := by
    intro r hr
    have h := hbInit_bounds comb h1K l r ((hb1SortedList_mem_iff K l r).mp hr)
    exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2⟩
  have hp2 : L₂.Pairwise (fun x y => key x ≤ key y) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_map] at hi hj
    simp only [L₂, List.getElem_map]
    have ha := hbnd _ (List.getElem_mem hi)
    have hb := hbnd _ (List.getElem_mem hj)
    dsimp [key]
    rw [hbKey1_bitsToNat_le_iff comb (wOf K) _ _ _ _ ha.1 hb.1 ha.2.1 hb.2.1 ha.2.2 hb.2.2]
    exact List.pairwise_iff_getElem.mp hpw_s1 i j hi hj hij
  have hinj : ∀ x ∈ L₂, ∀ y ∈ L₂, key x = key y → x = y := by
    intro x hx y hy hxy
    simp only [L₂, List.mem_map] at hx hy
    rcases hx with ⟨rx, hrx, rfl⟩
    rcases hy with ⟨ry, hry, rfl⟩
    have bx := hbnd rx hrx
    have byy := hbnd ry hry
    dsimp [key] at hxy
    rw [hbKey1_bitsToNat_eq_iff comb (wOf K) rx ry _ _ bx.1 byy.1 bx.2.1 byy.2.1 bx.2.2 byy.2.2] at hxy
    have horig := comb.hbKey1_orig_inj rx ry hxy
    have hreq := eq_of_mem_of_nodup_map (·.orig) (hb1SortedList_orig_nodup K l) hrx hry horig
    subst hreq; rfl
  have heq : L₁ = L₂ := comb.perm_eq_of_sorted_of_inj key L₁ L₂ hperm12 hp1 hp2 hinj
  funext q
  have hget := congrArg (fun xs : List (Qubits (wR1Hb K)) => xs[q.1]?.getD (fun _ => false)) heq
  have hlen₂ : L₂.length = arity (dHbOf K + 1) := by simp [L₂, hb1SortedList_length]
  have hL1 : L₁[q.1]? = some (rec2SortedArr K l q) := by
    rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact q.isLt)]
    simp [L₁]
  have hL2 : L₂[q.1]? = some (hbRecToBits (wOf K) ((hb1SortedList K l)[q.1]'(by rw [hb1SortedList_length]; exact q.isLt)) (fun _ => false)) := by
    rw [List.getElem?_eq_getElem (by rw [hlen₂]; exact q.isLt)]
    simp [L₂]
  rw [hL1, hL2] at hget
  exact hget

/-! #### 7.5 Adjacent Neighbor-Matching Pass (`hbSeqPassCirc`) -/

lemma hbSeqCmpCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K)
    (p : ℕ) (hp : p + 1 < arity (dHbOf K + 1)) :
    (hbSeqCmpCirc as arith n K d h1K p hp).size ≤ 28 * wOf K + 104 := by
  dsimp [hbSeqCmpCirc]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, LayeredCircuit.mapWires_size]
  have h0 := arith.eqConstMSBCircuit_size 2 0
  have h1 := arith.eqConstMSBCircuit_size 2 1
  have h2 := arith.eqRegCircuit_size (wOf K)
  omega

lemma act_hbSeqCmpCirc (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (h1K : 1 ≤ K) (p : ℕ) (hp : p + 1 < arity (dHbOf K + 1))
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (bIn : Qubits 4)
    (hzRec : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d_arr))
    (hzSeqB : z ∘ eSeqB as n K d = bIn)
    (hzAnc22 : z ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false)
    (hk0 : L[p].kind < 4) (hk1 : L[p + 1].kind < 4)
    (hm0 : L[p].m < 2 ^ wOf K) (hm1 : L[p + 1].m < 2 ^ wOf K)
    (ho0 : L[p].occ < 2 ^ wOf K) (ho1 : L[p + 1].occ < 2 ^ wOf K) :
    act (hbSeqCmpCirc as arith n K d h1K p hp).unitary (ket z) =
      ket (updateOn (eSeqB as n K d) z (fun j => xor (bIn j) (hbSeqCmpBits L[p] L[p + 1] j))) := by
  have h5w := five_le_wOf h1K
  let w := wOf K
  let q0 : Fin (arity (dHbOf K + 1)) := ⟨p, by omega⟩
  let q1 : Fin (arity (dHbOf K + 1)) := ⟨p + 1, hp⟩
  let r0 := L[p]
  let r1 := L[p + 1]
  let cmpB := hbSeqCmpBits r0 r1
  have h_anc2 : z ∘ eArith345 as n K d 2 (by omega) = fun _ => false := funext fun j => congrFun hzAnc22 _
  have h_ancW : z ∘ eArith345 as n K d w (by omega) = fun _ => false := funext fun j => congrFun hzAnc22 _
  have hz_k0 : z ∘ eRec2Kind as n K d q0 = natToBits 2 r0.kind := comp_eRec2Kind as n K d z L hL d_arr hzRec q0
  have hz_k1 : z ∘ eRec2Kind as n K d q1 = natToBits 2 r1.kind := comp_eRec2Kind as n K d z L hL d_arr hzRec q1
  have hz_m0 : z ∘ eRec2M as n K d q0 = natToBits w r0.m := comp_eRec2M as n K d z L hL d_arr hzRec q0
  have hz_m1 : z ∘ eRec2M as n K d q1 = natToBits w r1.m := comp_eRec2M as n K d z L hL d_arr hzRec q1
  have hz_o0 : z ∘ eRec2Occ as n K d q0 = natToBits w r0.occ := comp_eRec2Occ as n K d z L hL d_arr hzRec q0
  have hz_o1 : z ∘ eRec2Occ as n K d q1 = natToBits w r1.occ := comp_eRec2Occ as n K d z L hL d_arr hzRec q1
  have hslotSeqB : ∀ (wZ : Qubits (totWiresDef as n K d)) (v : Qubits 4) (j : Fin 4),
      updateOn (eSeqB as n K d) wZ v (eSeqBSlot as n K d j 0) = v j := fun wZ v j => by
    have h := congrFun (updateOn_comp_emb (eSeqB as n K d) wZ v) (sliceEmb j.1 1 (by omega) 0)
    simpa [eSeqBSlot, sliceEmb_apply, Function.comp_apply] using h
  have hz_eq_b0 : z (eSeqBSlot as n K d ⟨0, by decide⟩ 0) = bIn ⟨0, by decide⟩ := by
    simpa [eSeqBSlot, sliceEmb_apply, Function.comp_apply] using congrFun hzSeqB ⟨0, by decide⟩
  let z1 := updateOn (eSeqB as n K d) z (Function.update bIn ⟨0, by decide⟩ (xor (bIn ⟨0, by decide⟩) (cmpB ⟨0, by decide⟩)))
  let z2 := updateOn (eSeqB as n K d) z
    (Function.update (Function.update bIn ⟨0, by decide⟩ (xor (bIn ⟨0, by decide⟩) (cmpB ⟨0, by decide⟩)))
      ⟨1, by decide⟩ (xor (bIn ⟨1, by decide⟩) (cmpB ⟨1, by decide⟩)))
  let z3 := updateOn (eSeqB as n K d) z
    (Function.update (Function.update (Function.update bIn ⟨0, by decide⟩ (xor (bIn ⟨0, by decide⟩) (cmpB ⟨0, by decide⟩)))
      ⟨1, by decide⟩ (xor (bIn ⟨1, by decide⟩) (cmpB ⟨1, by decide⟩)))
      ⟨2, by decide⟩ (xor (bIn ⟨2, by decide⟩) (cmpB ⟨2, by decide⟩)))
  dsimp only [hbSeqCmpCirc, comb3, comb4]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, LayeredCircuit.id_unitary, act_one]
  -- Step 0: eqConst 2 0 on eRec2Kind q0 -> eSeqBSlot 0
  rw [act_eqConstOn arith
    (hIO := eRec2Kind_disjoint_eSeqBSlot as n K d _ _)
    (hIA := eRec2Kind_disjoint_eArith345 as n K d 2 (by omega) _)
    (hOA := eSeqBSlot_disjoint_eArith345 as n K d 2 (by omega) _)
    (hzAnc := h_anc2)]
  have hdec0 : decide (z ∘ eRec2Kind as n K d q0 = natToBits 2 0) = cmpB ⟨0, by decide⟩ := by
    rw [hz_k0, Bool.eq_iff_iff]
    simp only [cmpB, hbSeqCmpBits, decide_eq_true_eq]
    exact ⟨fun h => by have := congrArg bitsToNat h; rw [comb.bitsToNat_natToBits hk0, comb.bitsToNat_natToBits (by norm_num)] at this; exact this,
      fun h => by rw [h]⟩
  rw [hz_eq_b0, hdec0]
  have hupd0 : updateOn (eSeqBSlot as n K d ⟨0, by decide⟩) z (fun _ => xor (bIn ⟨0, by decide⟩) (cmpB ⟨0, by decide⟩)) = z1 :=
    updateOn_eSeqBSlot as n K d z bIn hzSeqB ⟨0, by decide⟩ _
  rw [hupd0]
  -- Step 1: eqConst 2 1 on eRec2Kind q1 -> eSeqBSlot 1
  have hz1_anc2 : z1 ∘ eArith345 as n K d 2 (by omega) = fun _ => false := by
    dsimp only [z1]; rw [updateOn_comp_disjoint _ _ (eSeqB_disjoint_eArith345 as n K d 2 (by omega))]; exact h_anc2
  rw [act_eqConstOn arith
    (hIO := eRec2Kind_disjoint_eSeqBSlot as n K d _ _)
    (hIA := eRec2Kind_disjoint_eArith345 as n K d 2 (by omega) _)
    (hOA := eSeqBSlot_disjoint_eArith345 as n K d 2 (by omega) _)
    (hzAnc := hz1_anc2)]
  have hz1_k1 : z1 ∘ eRec2Kind as n K d q1 = natToBits 2 r1.kind := by
    dsimp only [z1]; rw [updateOn_comp_disjoint _ _ (eSeqB_disjoint_eRec2Kind as n K d q1)]; exact hz_k1
  have hdec1 : decide (z1 ∘ eRec2Kind as n K d q1 = natToBits 2 1) = cmpB ⟨1, by decide⟩ := by
    rw [hz1_k1, Bool.eq_iff_iff]
    simp only [cmpB, hbSeqCmpBits, decide_eq_true_eq]
    exact ⟨fun h => by have := congrArg bitsToNat h; rw [comb.bitsToNat_natToBits hk1, comb.bitsToNat_natToBits (by norm_num)] at this; exact this,
      fun h => by rw [h]⟩
  have hz1_b1 : z1 (eSeqBSlot as n K d ⟨1, by decide⟩ 0) = bIn ⟨1, by decide⟩ := by
    dsimp only [z1]; rw [hslotSeqB z _ ⟨1, by decide⟩, Function.update_of_ne (by decide)]
  rw [hz1_b1, hdec1]
  have hupd1 : updateOn (eSeqBSlot as n K d ⟨1, by decide⟩) z1 (fun _ => xor (bIn ⟨1, by decide⟩) (cmpB ⟨1, by decide⟩)) = z2 := by
    have h := updateOn_eSeqBSlot as n K d z1 _ (updateOn_comp_emb (eSeqB as n K d) z _) ⟨1, by decide⟩
      (xor (bIn ⟨1, by decide⟩) (cmpB ⟨1, by decide⟩))
    dsimp only [z1] at h; dsimp only [z2]; rwa [updateOn_idem] at h
  rw [hupd1]
  -- Step 2: eqReg w on eRec2M q0, eRec2M q1 -> eSeqBSlot 2
  have hz2_ancW : z2 ∘ eArith345 as n K d w (by omega) = fun _ => false := by
    dsimp only [z2]; rw [updateOn_comp_disjoint _ _ (eSeqB_disjoint_eArith345 as n K d w (by omega))]; exact h_ancW
  rw [act_eqRegOn arith
    (hAB := eRec2M_disjoint_slot as n K d (by simp [Fin.ext_iff]))
    (hAO := eRec2M_disjoint_eSeqBSlot as n K d _ _)
    (hBO := eRec2M_disjoint_eSeqBSlot as n K d _ _)
    (hAA := eRec2M_disjoint_eArith345 as n K d w (by omega) _)
    (hBA := eRec2M_disjoint_eArith345 as n K d w (by omega) _)
    (hOA := eSeqBSlot_disjoint_eArith345 as n K d w (by omega) _)
    (hzAnc := hz2_ancW)]
  have hz2_m0 : z2 ∘ eRec2M as n K d q0 = natToBits w r0.m := by
    dsimp only [z2]; rw [updateOn_comp_disjoint _ _ (eSeqB_disjoint_eRec2M as n K d q0)]; exact hz_m0
  have hz2_m1 : z2 ∘ eRec2M as n K d q1 = natToBits w r1.m := by
    dsimp only [z2]; rw [updateOn_comp_disjoint _ _ (eSeqB_disjoint_eRec2M as n K d q1)]; exact hz_m1
  have hdec2 : decide (z2 ∘ eRec2M as n K d q0 = z2 ∘ eRec2M as n K d q1) = cmpB ⟨2, by decide⟩ := by
    rw [hz2_m0, hz2_m1, Bool.eq_iff_iff]
    simp only [cmpB, hbSeqCmpBits, decide_eq_true_eq]
    exact ⟨fun h => by have := congrArg bitsToNat h; rw [comb.bitsToNat_natToBits hm0, comb.bitsToNat_natToBits hm1] at this; exact this,
      fun h => by rw [h]⟩
  have hz2_b2 : z2 (eSeqBSlot as n K d ⟨2, by decide⟩ 0) = bIn ⟨2, by decide⟩ := by
    dsimp only [z2]
    rw [hslotSeqB z _ ⟨2, by decide⟩, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  rw [hz2_b2, hdec2]
  have hupd2 : updateOn (eSeqBSlot as n K d ⟨2, by decide⟩) z2 (fun _ => xor (bIn ⟨2, by decide⟩) (cmpB ⟨2, by decide⟩)) = z3 := by
    have h := updateOn_eSeqBSlot as n K d z2 _ (updateOn_comp_emb (eSeqB as n K d) z _) ⟨2, by decide⟩
      (xor (bIn ⟨2, by decide⟩) (cmpB ⟨2, by decide⟩))
    dsimp only [z2] at h; dsimp only [z3]; rwa [updateOn_idem] at h
  rw [hupd2]
  -- Step 3: eqReg w on eRec2Occ q0, eRec2Occ q1 -> eSeqBSlot 3
  have hz3_ancW : z3 ∘ eArith345 as n K d w (by omega) = fun _ => false := by
    dsimp only [z3]; rw [updateOn_comp_disjoint _ _ (eSeqB_disjoint_eArith345 as n K d w (by omega))]; exact h_ancW
  rw [act_eqRegOn arith
    (hAB := eRec2Occ_disjoint_slot as n K d (by simp [Fin.ext_iff]))
    (hAO := eRec2Occ_disjoint_eSeqBSlot as n K d _ _)
    (hBO := eRec2Occ_disjoint_eSeqBSlot as n K d _ _)
    (hAA := eRec2Occ_disjoint_eArith345 as n K d w (by omega) _)
    (hBA := eRec2Occ_disjoint_eArith345 as n K d w (by omega) _)
    (hOA := eSeqBSlot_disjoint_eArith345 as n K d w (by omega) _)
    (hzAnc := hz3_ancW)]
  have hz3_o0 : z3 ∘ eRec2Occ as n K d q0 = natToBits w r0.occ := by
    dsimp only [z3]; rw [updateOn_comp_disjoint _ _ (eSeqB_disjoint_eRec2Occ as n K d q0)]; exact hz_o0
  have hz3_o1 : z3 ∘ eRec2Occ as n K d q1 = natToBits w r1.occ := by
    dsimp only [z3]; rw [updateOn_comp_disjoint _ _ (eSeqB_disjoint_eRec2Occ as n K d q1)]; exact hz_o1
  have hdec3 : decide (z3 ∘ eRec2Occ as n K d q0 = z3 ∘ eRec2Occ as n K d q1) = cmpB ⟨3, by decide⟩ := by
    rw [hz3_o0, hz3_o1, Bool.eq_iff_iff]
    simp only [cmpB, hbSeqCmpBits, decide_eq_true_eq]
    exact ⟨fun h => by have := congrArg bitsToNat h; rw [comb.bitsToNat_natToBits ho0, comb.bitsToNat_natToBits ho1] at this; exact this,
      fun h => by rw [h]⟩
  have hz3_b3 : z3 (eSeqBSlot as n K d ⟨3, by decide⟩ 0) = bIn ⟨3, by decide⟩ := by
    dsimp only [z3]
    rw [hslotSeqB z _ ⟨3, by decide⟩, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]
  rw [hz3_b3, hdec3]
  have hupd3 : updateOn (eSeqBSlot as n K d ⟨3, by decide⟩) z3 (fun _ => xor (bIn ⟨3, by decide⟩) (cmpB ⟨3, by decide⟩)) =
      updateOn (eSeqB as n K d) z (fun j => xor (bIn j) (cmpB j)) := by
    have h := updateOn_eSeqBSlot as n K d z3 _ (updateOn_comp_emb (eSeqB as n K d) z _) ⟨3, by decide⟩
      (xor (bIn ⟨3, by decide⟩) (cmpB ⟨3, by decide⟩))
    dsimp only [z3] at h
    rw [updateOn_idem] at h
    rw [h]
    apply congrArg (updateOn (eSeqB as n K d) z)
    funext j; fin_cases j <;> simp
  rw [hupd3]

lemma hbSeqStepCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K)
    (p : ℕ) (hp : p + 1 < arity (dHbOf K + 1)) :
    (hbSeqStepCirc as arith n K d h1K p hp).size ≤ 61 * wOf K + 321 := by
  dsimp [hbSeqStepCirc]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, LayeredCircuit.mapWires_size]
  have hcmp := hbSeqCmpCirc_size as arith n K d h1K p hp
  have h4 := arith.eqConstMSBCircuit_size 4 15
  have h5 := arith.ctrlCopyRegCircuit_size (wOf K)
  have h6 := arith.ctrlConstXorMSBCircuit_size 2 3
  have h7 := arith.ctrlConstXorMSBCircuit_size 1 1
  have h12 := arith.eqConstMSBCircuit_size 2 2
  omega

lemma act_hbSeqStepCirc (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (h1K : 1 ≤ K) (p : ℕ) (hp : p + 1 < arity (dHbOf K + 1))
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hzRec : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d_arr))
    (hzSeqB : z ∘ eSeqB as n K d = fun _ => false)
    (hzCtrl : z ∘ eSeqCtrl as n K d = fun _ => false)
    (hzAnc22 : z ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false)
    (hk0 : L[p].kind ≤ 3) (hk1 : L[p + 1].kind ≤ 3) (hk1_ne : L[p + 1].kind ≠ 2)
    (hd0_zero : L[p].kind = 0 → L[p].dest = 0)
    (hm0 : L[p].m < 2 ^ wOf K) (hm1 : L[p + 1].m < 2 ^ wOf K)
    (ho0 : L[p].occ < 2 ^ wOf K) (ho1 : L[p + 1].occ < 2 ^ wOf K)
    (_hd0 : L[p].dest < 2 ^ wOf K) (_hd1 : L[p + 1].dest < 2 ^ wOf K) :
    act (hbSeqStepCirc as arith n K d h1K p hp).unitary (ket z) =
      ket (updateOn (eRec2 as n K d) z
        (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
          (hb1ArrOfList K (hbNeighborStep L p) (by dsimp [hbNeighborStep]; rw [dif_pos (by omega)]; split_ifs <;> simp [hL]) d_arr))) := by
  have h5w := five_le_wOf h1K
  let w := wOf K
  let q0 : Fin (arity (dHbOf K + 1)) := ⟨p, by omega⟩
  let q1 : Fin (arity (dHbOf K + 1)) := ⟨p + 1, hp⟩
  let r0 := L[p]
  let r1 := L[p + 1]
  let L' := hbNeighborStep L p
  have hL' : L'.length = arity (dHbOf K + 1) := by
    dsimp [L', hbNeighborStep]; rw [dif_pos (by omega)]; split_ifs <;> simp [hL]
  let ctrlBit : Bool := decide (r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ)
  let r0' := L'[p]'(by rw [hL']; omega)
  let r1' := L'[p + 1]'(by rw [hL']; exact hp)
  let cmpB := hbSeqCmpBits r0 r1
  let cmpB' := hbSeqCmpBits r0' r1'
  let z1 := updateOn (eSeqB as n K d) z cmpB
  let z2 := updateOn (eSeqCtrl as n K d) z1 (fun _ => ctrlBit)
  have hz_seqB0 : z ∘ eSeqB as n K d = fun _ => false := hzSeqB
  have hslotSeqB : ∀ (wZ : Qubits (totWiresDef as n K d)) (v : Qubits 4) (j : Fin 4),
      updateOn (eSeqB as n K d) wZ v (eSeqBSlot as n K d j 0) = v j := fun wZ v j => by
    have h := congrFun (updateOn_comp_emb (eSeqB as n K d) wZ v) (sliceEmb j.1 1 (by omega) 0)
    simpa [eSeqBSlot, sliceEmb_apply, Function.comp_apply] using h
  have h_xor_false : (fun j => xor false (cmpB j)) = cmpB := funext fun j => xor_false_left _
  dsimp only [hbSeqStepCirc, comb3, comb4]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, LayeredCircuit.id_unitary, act_one]
  -- 1. Forward cmp
  rw [act_hbSeqCmpCirc comb as arith n K d h1K p hp z L hL d_arr (fun _ => false) hzRec hz_seqB0 hzAnc22
    (by omega) (by omega) hm0 hm1 ho0 ho1]
  have hz1_eq : updateOn (eSeqB as n K d) z (fun j => xor false (cmpB j)) = z1 := by
    dsimp [z1]; rw [h_xor_false]
  rw [hz1_eq]
  -- 2. c4: allTrueAnd into eSeqCtrl
  have hz1_anc4 : z1 ∘ eArith345 as n K d 4 (by omega) = fun _ => false := by
    dsimp [z1]; rw [updateOn_comp_disjoint _ _ (eSeqB_disjoint_eArith345 as n K d 4 (by omega))]
    exact funext fun j => congrFun hzAnc22 _
  rw [act_allTrueAndOn comb arith (eSeqB as n K d) (eSeqCtrl as n K d) (eArith345 as n K d 4 (by omega))
    (eSeqB_disjoint_eSeqCtrl as n K d) (eSeqB_disjoint_eArith345 as n K d 4 (by omega))
    (eSeqCtrl_disjoint_eArith345 as n K d 4 (by omega)) z1 hz1_anc4]
  have hz1_ctrl0 : z1 (eSeqCtrl as n K d 0) = false := by
    dsimp [z1]; rw [← Function.comp_apply (f := updateOn _ z cmpB),
      updateOn_comp_disjoint _ _ (eSeqB_disjoint_eSeqCtrl as n K d)]; exact congrFun hzCtrl 0
  have hz1_seqB : z1 ∘ eSeqB as n K d = cmpB := updateOn_comp_emb _ _ _
  have hctrl_dec : decide (∀ i : Fin 4, z1 (eSeqB as n K d i) = true) = ctrlBit := by
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
    have hcongr : (∀ i : Fin 4, z1 (eSeqB as n K d i) = true) ↔
        (cmpB ⟨0, by decide⟩ = true ∧ cmpB ⟨1, by decide⟩ = true ∧ cmpB ⟨2, by decide⟩ = true ∧ cmpB ⟨3, by decide⟩ = true) := by
      constructor
      · intro h; refine ⟨?_, ?_, ?_, ?_⟩
        all_goals exact (congrFun hz1_seqB _).symm.trans (h _)
      · rintro ⟨h0, h1, h2, h3⟩ i; fin_cases i <;> exact (congrFun hz1_seqB _).trans ‹_›
    rw [hcongr]
    dsimp [cmpB, hbSeqCmpBits, ctrlBit]; simp only [decide_eq_true_eq]
  rw [hz1_ctrl0, hctrl_dec, xor_false_left]
  change act _ (act _ (act _ (act _ (act _ (act _ (ket z2)))))) = _
  -- 3. c5: ctrlCopyReg eRec2Dest q1 -> eRec2Dest q0
  rw [act_ctrlCopyRegOn arith
    (hCS := eSeqCtrl_disjoint_eRec2Dest as n K d _)
    (hCD := eSeqCtrl_disjoint_eRec2Dest as n K d _)
    (hSD := eRec2Dest_disjoint_slot as n K d (by simp [Fin.ext_iff]))]
  have hz2_ctrl0 : z2 (eSeqCtrl as n K d 0) = ctrlBit := congrFun (updateOn_comp_emb (eSeqCtrl as n K d) z1 _) 0
  have hz2_rec : z2 ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d_arr) := by
    dsimp [z2, z1]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec2_disjoint_eSeqCtrl as n K d b a h.symm)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec2_disjoint_eSeqB as n K d b a h.symm)]
    exact hzRec
  have hz2_d0 : z2 ∘ eRec2Dest as n K d q0 = natToBits w r0.dest :=
    comp_eRec2Dest as n K d z2 L hL d_arr hz2_rec q0
  have hz2_d1 : z2 ∘ eRec2Dest as n K d q1 = natToBits w r1.dest :=
    comp_eRec2Dest as n K d z2 L hL d_arr hz2_rec q1
  have hd0_val : (if z2 (eSeqCtrl as n K d 0) then
      fun j => xor (z2 (eRec2Dest as n K d q0 j)) (z2 (eRec2Dest as n K d q1 j))
      else z2 ∘ eRec2Dest as n K d q0) = natToBits w r0'.dest := by
    rw [hz2_ctrl0]
    by_cases hct : ctrlBit = true
    · have hcond : r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ := by
        dsimp [ctrlBit] at hct; exact of_decide_eq_true hct
      have hr0d0 : r0.dest = 0 := hd0_zero hcond.1
      have hr0'_dest : r0'.dest = r1.dest := by
        dsimp only [r0', L']; rw [hbNeighborStep_getElem_p_pos L p (by omega) hcond]
      rw [if_pos hct, hr0'_dest]
      funext j
      change xor ((z2 ∘ eRec2Dest as n K d q0) j) ((z2 ∘ eRec2Dest as n K d q1) j) = _
      rw [hz2_d0, hz2_d1, hr0d0, natToBits_zero comb]; simp
    · have hf : ctrlBit = false := Bool.eq_false_iff.mpr hct
      have hnot : ¬ (r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ) := fun hc =>
        hct (decide_eq_true hc)
      have hr0'_dest : r0'.dest = r0.dest := by
        dsimp only [r0', L']; rw [hbNeighborStep_getElem_neg L p (by omega) hnot]
      rw [if_neg hct, hr0'_dest, hz2_d0]
  rw [hd0_val]
  -- Express updated state cleanly by computing updateOn eRec2 first!
  let newArr := hb1ArrOfList K L' hL' d_arr
  let z3 := updateOn (eRec2Dest as n K d q0) z2 (natToBits w r0'.dest)
  -- 4. c6: ctrlConstXor 2 3 on eRec2Kind q1
  rw [act_ctrlConstXorOn arith (hCB := eSeqCtrl_disjoint_eRec2Kind as n K d _)]
  have hz3_ctrl0 : z3 (eSeqCtrl as n K d 0) = ctrlBit := by
    dsimp [z3]; rw [← Function.comp_apply (f := updateOn _ z2 _),
      updateOn_comp_disjoint _ _ (fun a b h => eSeqCtrl_disjoint_eRec2Dest as n K d q0 b a h.symm)]
    exact hz2_ctrl0
  have hz3_k1 : z3 ∘ eRec2Kind as n K d q1 = natToBits 2 r1.kind := by
    dsimp [z3]
    have hdisj : ∀ a b, eRec2Dest as n K d q0 a ≠ eRec2Kind as n K d q1 b :=
      fun a b h => ancRegField_disjoint_slot as n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _)
        (by simp [q0, q1, Fin.ext_iff]) _ _ a b h
    rw [updateOn_comp_disjoint _ _ hdisj]
    exact comp_eRec2Kind as n K d z2 L hL d_arr hz2_rec q1
  have hk1_val : (if z3 (eSeqCtrl as n K d 0) then
      fun j => xor (z3 (eRec2Kind as n K d q1 j)) (natToBits 2 3 j)
      else z3 ∘ eRec2Kind as n K d q1) = natToBits 2 r1'.kind := by
    rw [hz3_ctrl0]
    by_cases hct : ctrlBit = true
    · have hcond : r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ := by
        dsimp [ctrlBit] at hct; exact of_decide_eq_true hct
      have hr1'_kind : r1'.kind = 2 := by
        dsimp only [r1', L']; rw [hbNeighborStep_getElem_succ_pos L p (by omega) hcond]
      rw [if_pos hct, hr1'_kind]
      funext j
      change xor ((z3 ∘ eRec2Kind as n K d q1) j) (natToBits 2 3 j) = _
      rw [hz3_k1, hcond.2.1]
      exact congrFun (natToBits_two_one_xor_three comb) j
    · have hnot : ¬ (r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ) := fun hc =>
        hct (decide_eq_true hc)
      have hr1'_kind : r1'.kind = r1.kind := by
        dsimp only [r1', L']; rw [hbNeighborStep_getElem_neg L p (by omega) hnot]
      rw [if_neg hct, hr1'_kind, hz3_k1]
  rw [hk1_val]
  let z4 := updateOn (eRec2Kind as n K d q1) z3 (natToBits 2 r1'.kind)
  -- 4b. c6b: ctrlConstXor 2 3 on eRec2KR1 q1
  rw [act_ctrlConstXorOn arith (hCB := eSeqCtrl_disjoint_eRec2KR1 as n K d _)]
  have hz4_ctrl0 : z4 (eSeqCtrl as n K d 0) = ctrlBit := by
    dsimp [z4]; rw [← Function.comp_apply (f := updateOn _ z3 _),
      updateOn_comp_disjoint _ _ (eRec2Kind_disjoint_eSeqCtrl as n K d q1)]
    exact hz3_ctrl0
  have hz4_kr1 : z4 ∘ eRec2KR1 as n K d q1 = natToBits 2 (hbKindRank1 r1) := by
    dsimp [z4, z3]
    have hdisj1 : ∀ a b, eRec2Kind as n K d q1 a ≠ eRec2KR1 as n K d q1 b :=
      eRec2Kind_disjoint_eRec2KR1 as n K d q1
    have hdisj2 : ∀ a b, eRec2Dest as n K d q0 a ≠ eRec2KR1 as n K d q1 b :=
      fun a b h => ancRegField_disjoint_slot as n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _)
        (Fin.ne_of_val_ne (by dsimp [q0, q1]; omega)) _ _ a b h
    rw [updateOn_comp_disjoint _ _ hdisj1, updateOn_comp_disjoint _ _ hdisj2]
    exact comp_eRec2KR1 as n K d z2 L hL d_arr hz2_rec q1
  have hkr1_val : (if z4 (eSeqCtrl as n K d 0) then
      fun j => xor (z4 (eRec2KR1 as n K d q1 j)) (natToBits 2 3 j)
      else z4 ∘ eRec2KR1 as n K d q1) = natToBits 2 (hbKindRank1 r1') := by
    rw [hz4_ctrl0]
    by_cases hct : ctrlBit = true
    · have hcond : r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ := by
        dsimp [ctrlBit] at hct; exact of_decide_eq_true hct
      have hr1'_kind : r1'.kind = 2 := by
        dsimp only [r1', L']; rw [hbNeighborStep_getElem_succ_pos L p (by omega) hcond]
      have hr1'_kr : hbKindRank1 r1' = 2 := by dsimp [hbKindRank1]; rw [hr1'_kind]; norm_num
      have hr1_kr : hbKindRank1 r1 = 1 := by dsimp [hbKindRank1]; rw [hcond.2.1]; norm_num
      rw [if_pos hct, hr1'_kr]
      funext j
      change xor ((z4 ∘ eRec2KR1 as n K d q1) j) (natToBits 2 3 j) = _
      rw [hz4_kr1, hr1_kr]
      exact congrFun (natToBits_two_one_xor_three comb) j
    · have hnot : ¬ (r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ) := fun hc =>
        hct (decide_eq_true hc)
      have hr1'_eq : r1' = r1 := by
        dsimp only [r1', L']; exact hbNeighborStep_getElem_neg L p (by omega) hnot (p + 1) _ _
      rw [if_neg hct, hr1'_eq, hz4_kr1]
  rw [hkr1_val]
  -- Show updated state agrees with updateOn eRec2 z newArr everywhere except eSeqB (cmpB) and eSeqCtrl (ctrlBit)!
  have hz4_eq : updateOn (eRec2KR1 as n K d ⟨p + 1, hp⟩) (updateOn (eRec2Kind as n K d ⟨p + 1, hp⟩)
      (updateOn (eRec2Dest as n K d ⟨p, by omega⟩) z2 (natToBits w r0'.dest)) (natToBits 2 r1'.kind))
      (natToBits 2 (hbKindRank1 r1')) =
      updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) (updateOn (eRec2 as n K d) z
        (flatReg (arity (dHbOf K + 1)) (wR1Hb K) newArr)) cmpB) (fun _ => ctrlBit) := by
    change updateOn (eRec2KR1 as n K d q1) (updateOn (eRec2Kind as n K d q1)
        (updateOn (eRec2Dest as n K d q0) z2 (natToBits w r0'.dest)) (natToBits 2 r1'.kind))
        (natToBits 2 (hbKindRank1 r1')) = _
    have hz_arr : updateOn (eRec2KR1 as n K d q1) (updateOn (eRec2Kind as n K d q1)
        (updateOn (eRec2Dest as n K d q0) z2 (natToBits w r0'.dest)) (natToBits 2 r1'.kind))
        (natToBits 2 (hbKindRank1 r1')) =
        updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K) newArr) := by
      let arr1 := Function.update (hb1ArrOfList K L hL d_arr) q0
        (updateOn (sliceEmb (wK1Hb K + 2) (wOf K) (by dsimp [wR1Hb, wP1Hb, wK1Hb]; omega))
          (hb1ArrOfList K L hL d_arr q0) (natToBits w r0'.dest))
      have hupd_q0 : updateOn (eRec2Dest as n K d q0) z2 (natToBits w r0'.dest) =
          updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr1) := by
        have h := updateOn_ancRegSlot_eq as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _)
          z2 (hb1ArrOfList K L hL d_arr) hz2_rec q0
          (updateOn (sliceEmb (wK1Hb K + 2) (wOf K) (by dsimp [wR1Hb, wP1Hb, wK1Hb]; omega))
            (hb1ArrOfList K L hL d_arr q0) (natToBits w r0'.dest))
        dsimp only [eRec2Dest]
        rw [updateOn_ancRegField_eq_slot,
          comp_ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _)
            z2 _ hz2_rec q0]
        exact h
      rw [hupd_q0]
      have hz1_rec : updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr1) ∘ eRec2 as n K d =
          flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr1 := updateOn_comp_emb _ _ _
      have hne_q01 : q1 ≠ q0 := Fin.ne_of_val_ne (by dsimp [q0, q1]; exact Nat.succ_ne_self p)
      have hcomp_q1 : arr1 q1 = hb1ArrOfList K L hL d_arr q1 := by
        dsimp only [arr1]; exact Function.update_of_ne hne_q01 _ _
      let arr2 := Function.update arr1 q1
        (updateOn (sliceEmb (wK1Hb K) 2 (by dsimp [wR1Hb, wP1Hb, wK1Hb]; omega))
          (hb1ArrOfList K L hL d_arr q1) (natToBits 2 r1'.kind))
      have hupd_q1k : updateOn (eRec2Kind as n K d q1)
          (updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr1)) (natToBits 2 r1'.kind) =
          updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr2) := by
        have h := updateOn_ancRegSlot_eq as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _)
          (updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr1)) arr1 hz1_rec q1
          (updateOn (sliceEmb (wK1Hb K) 2 (by dsimp [wR1Hb, wP1Hb, wK1Hb]; omega))
            (hb1ArrOfList K L hL d_arr q1) (natToBits 2 r1'.kind))
        dsimp only [eRec2Kind]
        rw [updateOn_ancRegField_eq_slot,
          comp_ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _)
            (updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr1)) arr1 hz1_rec q1]
        rw [hcomp_q1, h]
        have hrec_eq : ancRegSlice as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) =
            eRec2 as n K d := rfl
        rw [hrec_eq, updateOn_idem]
      rw [hupd_q1k]
      have hz2_rec' : updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr2) ∘ eRec2 as n K d =
          flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr2 := updateOn_comp_emb _ _ _
      let slot_q1 := updateOn (sliceEmb (wK1Hb K) 2 (by dsimp [wR1Hb, wP1Hb, wK1Hb]; omega))
        (hb1ArrOfList K L hL d_arr q1) (natToBits 2 r1'.kind)
      have hupd_q1kr : updateOn (eRec2KR1 as n K d q1)
          (updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr2)) (natToBits 2 (hbKindRank1 r1')) =
          updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
            (Function.update arr2 q1
              (updateOn (sliceEmb (1 + wOf K + wOf K) 2 (by dsimp [wR1Hb, wK1Hb]; omega)) slot_q1 (natToBits 2 (hbKindRank1 r1'))))) := by
        have h := updateOn_ancRegSlot_eq as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _)
          (updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr2)) arr2 hz2_rec' q1
          (updateOn (sliceEmb (1 + wOf K + wOf K) 2 (by dsimp [wR1Hb, wK1Hb]; omega)) slot_q1 (natToBits 2 (hbKindRank1 r1')))
        have harr2_q1 : arr2 q1 = slot_q1 := by dsimp only [arr2]; exact Function.update_self _ _ _
        dsimp only [eRec2KR1]
        rw [updateOn_ancRegField_eq_slot,
          comp_ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _)
            (updateOn (eRec2 as n K d) z2 (flatReg (arity (dHbOf K + 1)) (wR1Hb K) arr2)) arr2 hz2_rec' q1]
        rw [harr2_q1, h]
        have hrec_eq : ancRegSlice as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) =
            eRec2 as n K d := rfl
        rw [hrec_eq, updateOn_idem]
      rw [hupd_q1kr]
      apply congrArg (updateOn (eRec2 as n K d) z2)
      apply congrArg (flatReg (arity (dHbOf K + 1)) (wR1Hb K))
      funext q
      by_cases hq0 : q = q0
      · subst hq0
        rw [Function.update_of_ne hne_q01.symm]
        dsimp only [arr2]; rw [Function.update_of_ne hne_q01.symm]
        dsimp only [arr1]; rw [Function.update_self]
        dsimp only [hb1ArrOfList, newArr, hbRecToBits]
        rw [updateOn_rec2SlotFn_6]
        change rec2SlotFn (wOf K) (natToBits 1 (hbInactive r0)) (natToBits (wOf K) r0.m)
            (natToBits (wOf K) r0.occ) (natToBits 2 (hbKindRank1 r0)) (natToBits (wOf K) r0.orig)
            (natToBits 2 r0.kind) (natToBits (wOf K) r0'.dest) (d_arr q0) =
          rec2SlotFn (wOf K) (natToBits 1 (hbInactive r0')) (natToBits (wOf K) r0'.m)
            (natToBits (wOf K) r0'.occ) (natToBits 2 (hbKindRank1 r0')) (natToBits (wOf K) r0'.orig)
            (natToBits 2 r0'.kind) (natToBits (wOf K) r0'.dest) (d_arr q0)
        by_cases hct : r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ
        · have hr0' : r0' = { r0 with dest := r1.dest } := by
            dsimp only [r0', L']; exact hbNeighborStep_getElem_p_pos L p (by omega) hct _
          rw [hr0']; rfl
        · have hr0' : r0' = r0 := by
            dsimp only [r0', L']; exact hbNeighborStep_getElem_neg L p (by omega) hct p _ _
          rw [hr0']
      · by_cases hq1 : q = q1
        · subst hq1
          rw [Function.update_self]
          dsimp only [slot_q1, hb1ArrOfList, newArr, hbRecToBits]
          rw [updateOn_rec2SlotFn_5, updateOn_rec2SlotFn_3]
          change rec2SlotFn (wOf K) (natToBits 1 (hbInactive r1)) (natToBits (wOf K) r1.m)
              (natToBits (wOf K) r1.occ) (natToBits 2 (hbKindRank1 r1')) (natToBits (wOf K) r1.orig)
              (natToBits 2 r1'.kind) (natToBits (wOf K) r1.dest) (d_arr q1) =
            rec2SlotFn (wOf K) (natToBits 1 (hbInactive r1')) (natToBits (wOf K) r1'.m)
              (natToBits (wOf K) r1'.occ) (natToBits 2 (hbKindRank1 r1')) (natToBits (wOf K) r1'.orig)
              (natToBits 2 r1'.kind) (natToBits (wOf K) r1'.dest) (d_arr q1)
          by_cases hct : r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ
          · have hr1' : r1' = { r1 with kind := 2 } := by
              dsimp only [r1', L']; exact hbNeighborStep_getElem_succ_pos L p (by omega) hct _
            have hinv1 : hbInactive r1 = 0 := by dsimp [hbInactive]; rw [hct.2.1]; norm_num
            have hinv1' : hbInactive r1' = 0 := by rw [hr1']; dsimp [hbInactive]
            rw [hinv1, hinv1', hr1']
          · have hr1' : r1' = r1 := by
              dsimp only [r1', L']; exact hbNeighborStep_getElem_neg L p (by omega) hct (p + 1) _ _
            rw [hr1']
        · rw [Function.update_of_ne hq1]
          dsimp only [arr2]; rw [Function.update_of_ne hq1]
          dsimp only [arr1]; rw [Function.update_of_ne hq0]
          dsimp only [newArr, hb1ArrOfList]
          by_cases hct : r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ
          · have hL'_eq := hbNeighborStep_eq_pos L p (by omega) hct
            have hnq0 : q.1 ≠ p := fun hv => hq0 (Fin.ext (by dsimp [q0]; exact hv))
            have hnq1 : q.1 ≠ p + 1 := fun hv => hq1 (Fin.ext (by dsimp [q1]; exact hv))
            have hget : L'[q.1]'(by rw [hL']; exact q.isLt) = L[q.1]'(by rw [hL]; exact q.isLt) := by
              dsimp only [L']
              simp only [hL'_eq, List.getElem_set_ne hnq1.symm, List.getElem_set_ne hnq0.symm]
            rw [hget]
          · have hget : L'[q.1]'(by rw [hL']; exact q.isLt) = L[q.1]'(by rw [hL]; exact q.isLt) := by
              dsimp only [L']; exact hbNeighborStep_getElem_neg L p (by omega) hct q.1 _ _
            rw [hget]
    rw [hz_arr]
    dsimp [z2, z1]
    rw [updateOn_comm (eRec2 as n K d) (eSeqCtrl as n K d) (eRec2_disjoint_eSeqCtrl as n K d)]
    rw [updateOn_comm (eRec2 as n K d) (eSeqB as n K d) (eRec2_disjoint_eSeqB as n K d)]
  rw [hz4_eq]
  -- 5. c7: ctrlConstXor 1 1 on eSeqCtrl, eSeqBSlot 1
  let zTarget := updateOn (eRec2 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR1Hb K) newArr)
  let zMid := updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB') (fun _ => ctrlBit)
  rw [act_ctrlConstXorOn arith (hCB := eSeqCtrl_disjoint_eSeqBSlot as n K d _)]
  have hz4_ctrl : updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB) (fun _ => ctrlBit)
      (eSeqCtrl as n K d 0) = ctrlBit :=
    congrFun (updateOn_comp_emb (eSeqCtrl as n K d) _ _) 0
  have hz4_b1 : (fun j : Fin 1 => updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB)
      (fun _ => ctrlBit) (eSeqBSlot as n K d ⟨1, by decide⟩ j)) = fun _ => cmpB ⟨1, by decide⟩ := by
    funext j; have hj0 : j = 0 := Fin.ext (by omega); subst hj0
    rw [← Function.comp_apply (f := updateOn (eSeqCtrl as n K d) _ _),
      updateOn_comp_disjoint _ _ (eSeqCtrl_disjoint_eSeqBSlot as n K d ⟨1, by decide⟩)]
    exact hslotSeqB zTarget cmpB ⟨1, by decide⟩
  have hcmps_eq : (∀ j : Fin 4, j ≠ ⟨1, by decide⟩ → cmpB' j = cmpB j) := by
    intro j hj
    dsimp only [cmpB', cmpB, hbSeqCmpBits]
    by_cases hct : ctrlBit = true
    · have hcond : r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ := by
        dsimp [ctrlBit] at hct; exact of_decide_eq_true hct
      have hr0' : r0' = { r0 with dest := r1.dest } := by
        dsimp only [r0', L']; exact hbNeighborStep_getElem_p_pos L p (by omega) hcond _
      have hr1' : r1' = { r1 with kind := 2 } := by
        dsimp only [r1', L']; exact hbNeighborStep_getElem_succ_pos L p (by omega) hcond _
      rw [hr0', hr1']
      fin_cases j <;> simp at hj ⊢
    · have hnot : ¬ (r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ) := fun hc =>
        hct (decide_eq_true hc)
      have hr0' : r0' = r0 := by dsimp only [r0', L']; exact hbNeighborStep_getElem_neg L p (by omega) hnot p _ _
      have hr1' : r1' = r1 := by dsimp only [r1', L']; exact hbNeighborStep_getElem_neg L p (by omega) hnot (p + 1) _ _
      rw [hr0', hr1']
  have hcmp1_xor : (if ctrlBit then fun j : Fin 1 => xor (cmpB ⟨1, by decide⟩) (natToBits 1 1 j)
      else fun _ : Fin 1 => cmpB ⟨1, by decide⟩) = fun _ => cmpB' ⟨1, by decide⟩ := by
    funext j; have hj0 : j = 0 := Fin.ext (by omega); subst hj0
    rw [natToBits_one_one comb]
    dsimp only [cmpB', cmpB, hbSeqCmpBits]
    by_cases hct : ctrlBit = true
    · have hcond : r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ := by
        dsimp [ctrlBit] at hct; exact of_decide_eq_true hct
      have hr1' : r1' = { r1 with kind := 2 } := by
        dsimp only [r1', L']; exact hbNeighborStep_getElem_succ_pos L p (by omega) hcond _
      rw [if_pos hct, hr1', hcond.2.1]; simp
    · have hnot : ¬ (r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ) := fun hc =>
        hct (decide_eq_true hc)
      have hr1' : r1' = r1 := by dsimp only [r1', L']; exact hbNeighborStep_getElem_neg L p (by omega) hnot (p + 1) _ _
      rw [if_neg hct, hr1']; simp
  have hz4_to_zMid : updateOn (eSeqBSlot as n K d ⟨1, by decide⟩)
      (updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB) (fun _ => ctrlBit))
      (if updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB) (fun _ => ctrlBit)
          (eSeqCtrl as n K d 0)
        then fun j => xor (updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB) (fun _ => ctrlBit)
            (eSeqBSlot as n K d ⟨1, by decide⟩ j)) (natToBits 1 1 j)
        else updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB) (fun _ => ctrlBit) ∘
            eSeqBSlot as n K d ⟨1, by decide⟩) = zMid := by
    have hbranch : (if updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB) (fun _ => ctrlBit)
          (eSeqCtrl as n K d 0)
        then fun j => xor (updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB) (fun _ => ctrlBit)
            (eSeqBSlot as n K d ⟨1, by decide⟩ j)) (natToBits 1 1 j)
        else updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB) (fun _ => ctrlBit) ∘
            eSeqBSlot as n K d ⟨1, by decide⟩) = fun _ => cmpB' ⟨1, by decide⟩ := by
      have hz4_b1' : updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB) (fun _ => ctrlBit) ∘
          eSeqBSlot as n K d ⟨1, by decide⟩ = fun _ => cmpB ⟨1, by decide⟩ := hz4_b1
      rw [hz4_ctrl]
      change (if ctrlBit then fun j => xor ((updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB) (fun _ => ctrlBit) ∘
          eSeqBSlot as n K d ⟨1, by decide⟩) j) (natToBits 1 1 j)
        else updateOn (eSeqCtrl as n K d) (updateOn (eSeqB as n K d) zTarget cmpB) (fun _ => ctrlBit) ∘
          eSeqBSlot as n K d ⟨1, by decide⟩) = _
      rw [hz4_b1']; exact hcmp1_xor
    rw [hbranch]
    dsimp only [zMid]
    change updateOn (eSeqBSlot as n K d ⟨1, by decide⟩) _ _ = _
    rw [updateOn_comm (eSeqBSlot as n K d ⟨1, by decide⟩) (eSeqCtrl as n K d)
      (fun a b h => eSeqCtrl_disjoint_eSeqBSlot as n K d ⟨1, by decide⟩ b a h.symm)]
    dsimp only [eSeqBSlot]
    rw [updateOn_trans_emb, updateOn_idem, updateOn_comp_emb]
    apply congrArg (fun x => updateOn (eSeqCtrl as n K d) x (fun _ => ctrlBit))
    apply congrArg (updateOn (eSeqB as n K d) zTarget)
    funext j
    fin_cases j
    · rw [updateOn_apply_not_mem _ _ _ (by rintro ⟨x, hx⟩; have h := congrArg Fin.val hx; simp at h)]
      exact (hcmps_eq ⟨0, by decide⟩ (by decide)).symm
    · change updateOn (sliceEmb 1 1 (by omega)) cmpB (fun _ => cmpB' ⟨1, by decide⟩) (sliceEmb 1 1 (by omega) 0) = _
      rw [updateOn_apply_emb]
    · rw [updateOn_apply_not_mem _ _ _ (by rintro ⟨x, hx⟩; have h := congrArg Fin.val hx; simp at h)]
      exact (hcmps_eq ⟨2, by decide⟩ (by decide)).symm
    · rw [updateOn_apply_not_mem _ _ _ (by rintro ⟨x, hx⟩; have h := congrArg Fin.val hx; simp at h)]
      exact (hcmps_eq ⟨3, by decide⟩ (by decide)).symm
  rw [hz4_to_zMid]
  -- 6. Backward cmp (resets eSeqB from cmpB' to 0)
  have hzMid_rec : zMid ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) newArr := by
    dsimp [zMid, zTarget]
    rw [updateOn_comp_disjoint _ _ (eSeqCtrl_disjoint_eRec2 as n K d)]
    rw [updateOn_comp_disjoint _ _ (eSeqB_disjoint_eRec2 as n K d)]
    exact updateOn_comp_emb _ _ _
  have hzMid_seqB : zMid ∘ eSeqB as n K d = cmpB' := by
    dsimp [zMid]
    rw [updateOn_comp_disjoint _ _ (eSeqCtrl_disjoint_eSeqB as n K d)]
    exact updateOn_comp_emb _ _ _
  have hzMid_anc22 : zMid ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false := by
    dsimp only [zMid, zTarget, eSeqCtrl, eSeqB]
    rw [updateOn_comp_disjoint _ _ (ancPrefix_disjoint_anc as n K d (k1 := ⟨20, by decide⟩) (k2 := ⟨22, by decide⟩) (by decide) _ _)]
    rw [updateOn_comp_disjoint _ _ (ancPrefix_disjoint_anc as n K d (k1 := ⟨19, by decide⟩) (k2 := ⟨22, by decide⟩) (by decide) _ _)]
    rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide))]
    exact hzAnc22
  have hbnd' : r0'.kind < 4 ∧ r1'.kind < 4 ∧ r0'.m < 2 ^ wOf K ∧ r1'.m < 2 ^ wOf K ∧ r0'.occ < 2 ^ wOf K ∧ r1'.occ < 2 ^ wOf K := by
    by_cases hct : r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ
    · have hr0' : r0' = { r0 with dest := r1.dest } := by
        dsimp only [r0', L']; exact hbNeighborStep_getElem_p_pos L p (by omega) hct _
      have hr1' : r1' = { r1 with kind := 2 } := by
        dsimp only [r1', L']; exact hbNeighborStep_getElem_succ_pos L p (by omega) hct _
      rw [hr0', hr1']; dsimp only [r0, r1]; omega
    · have hr0' : r0' = r0 := by dsimp only [r0', L']; exact hbNeighborStep_getElem_neg L p (by omega) hct p _ _
      have hr1' : r1' = r1 := by dsimp only [r1', L']; exact hbNeighborStep_getElem_neg L p (by omega) hct (p + 1) _ _
      rw [hr0', hr1']; dsimp only [r0, r1]; omega
  rw [act_hbSeqCmpCirc comb as arith n K d h1K p hp zMid L' hL' d_arr cmpB' hzMid_rec hzMid_seqB hzMid_anc22
    hbnd'.1 hbnd'.2.1 hbnd'.2.2.1 hbnd'.2.2.2.1 hbnd'.2.2.2.2.1 hbnd'.2.2.2.2.2]
  have hxor_cmp' : (fun j => xor (cmpB' j) (cmpB' j)) = fun _ => false := funext fun j => xor_self_cancel _
  rw [hxor_cmp']
  let zPostCmp := updateOn (eSeqB as n K d) zMid (fun _ => false)
  have hzPost_eq : zPostCmp = updateOn (eSeqCtrl as n K d) zTarget (fun _ => ctrlBit) := by
    dsimp [zPostCmp, zMid]
    rw [updateOn_comm (eSeqB as n K d) (eSeqCtrl as n K d) (eSeqB_disjoint_eSeqCtrl as n K d), updateOn_idem]
    apply congrArg (fun q => updateOn (eSeqCtrl as n K d) q (fun _ => ctrlBit))
    apply updateOn_noop; dsimp [zTarget]
    rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_eSeqB as n K d)]
    exact hzSeqB
  change act _ (ket zPostCmp) = _
  rw [hzPost_eq]
  -- 7. c12: eqConst 2 2 resets eSeqCtrl to 0
  have hzPost_anc2 : updateOn (eSeqCtrl as n K d) zTarget (fun _ => ctrlBit) ∘ eArith345 as n K d 2 (by omega) =
      fun _ => false := by
    rw [updateOn_comp_disjoint _ _ (eSeqCtrl_disjoint_eArith345 as n K d 2 (by omega))]
    dsimp [zTarget]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec2_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide) a _ h)]
    exact funext fun j => congrFun hzAnc22 _
  rw [act_eqConstOn arith
    (hIO := eRec2Kind_disjoint_eSeqCtrl as n K d _)
    (hIA := eRec2Kind_disjoint_eArith345 as n K d 2 (by omega) _)
    (hOA := eSeqCtrl_disjoint_eArith345 as n K d 2 (by omega))
    (hzAnc := hzPost_anc2)]
  have hzPost_k1 : updateOn (eSeqCtrl as n K d) zTarget (fun _ => ctrlBit) ∘ eRec2Kind as n K d q1 =
      natToBits 2 r1'.kind := by
    rw [updateOn_comp_disjoint _ _ (eSeqCtrl_disjoint_eRec2Kind as n K d q1)]
    have hzT_rec : zTarget ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) newArr :=
      updateOn_comp_emb _ _ _
    exact comp_eRec2Kind as n K d zTarget L' hL' d_arr hzT_rec q1
  have hctrl_post : updateOn (eSeqCtrl as n K d) zTarget (fun _ => ctrlBit) (eSeqCtrl as n K d 0) = ctrlBit :=
    congrFun (updateOn_comp_emb (eSeqCtrl as n K d) zTarget _) 0
  have hdec_k1_2 : decide (updateOn (eSeqCtrl as n K d) zTarget (fun _ => ctrlBit) ∘ eRec2Kind as n K d q1 =
      natToBits 2 2) = ctrlBit := by
    rw [hzPost_k1, Bool.eq_iff_iff, decide_eq_true_eq]
    by_cases hct : ctrlBit = true
    · have hcond : r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ := by
        dsimp [ctrlBit] at hct; exact of_decide_eq_true hct
      have hr1'_kind : r1'.kind = 2 := by
        dsimp only [r1', L']; rw [hbNeighborStep_getElem_succ_pos L p (by omega) hcond]
      rw [hr1'_kind, hct]; exact ⟨fun _ => rfl, fun _ => rfl⟩
    · have hf : ctrlBit = false := Bool.eq_false_iff.mpr hct
      have hnot : ¬ (r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ) := fun hc =>
        hct (decide_eq_true hc)
      have hr1'_kind : r1'.kind = r1.kind := by
        dsimp only [r1', L']; rw [hbNeighborStep_getElem_neg L p (by omega) hnot]
      rw [hr1'_kind, hf]
      exact ⟨fun h => absurd (by
        have he := congrArg bitsToNat h
        rw [comb.bitsToNat_natToBits (by omega), comb.bitsToNat_natToBits (by norm_num)] at he
        exact he) hk1_ne, fun h => by cases h⟩
  rw [hctrl_post, hdec_k1_2, xor_self_cancel, updateOn_idem]
  apply congrArg ket; apply updateOn_noop; dsimp only [zTarget]
  rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_eSeqCtrl as n K d)]
  exact hzCtrl

lemma hbSeqPassCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) :
    (hbSeqPassCirc as arith n K d h1K).size ≤ (arity (dHbOf K + 1) - 1) * (61 * wOf K + 321) := by
  dsimp [hbSeqPassCirc]
  have h := LayeredCircuit_seqList_size_le
    ((List.range (arity (dHbOf K + 1) - 1)).map fun p =>
      if hp : p + 1 < arity (dHbOf K + 1) then hbSeqStepCirc as arith n K d h1K p hp else LayeredCircuit.id _)
    (61 * wOf K + 321)
    (by
      intro lc hlc; simp only [List.mem_map] at hlc; rcases hlc with ⟨p, _, rfl⟩
      split_ifs with hp
      · exact hbSeqStepCirc_size as arith n K d h1K p hp
      · simp)
  simpa using h

lemma act_hbSeqPassCirc (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (h1K : 1 ≤ K) (z : Qubits (totWiresDef as n K d))
    (s1 : List HBRec) (hs1_len : s1.length = arity (dHbOf K + 1))
    (hs1_bnd : ∀ r ∈ s1, r.kind ≤ 3 ∧ r.kind ≠ 2 ∧ (r.kind = 0 → r.dest = 0) ∧
      r.m < 2 ^ wOf K ∧ r.occ < 2 ^ wOf K ∧ r.dest < 2 ^ wOf K ∧ r.orig < 2 ^ wOf K)
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hzRec : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K s1 hs1_len d_arr))
    (hzSeqB : z ∘ eSeqB as n K d = fun _ => false)
    (hzCtrl : z ∘ eSeqCtrl as n K d = fun _ => false)
    (hzAnc22 : z ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false) :
    act (hbSeqPassCirc as arith n K d h1K).unitary (ket z) =
      ket (updateOn (eRec2 as n K d) z
        (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
          (hb1ArrOfList K (hbSeqPass s1) (by rw [hbSeqPass_length]; exact hs1_len) d_arr))) := by
  let st (k : ℕ) : Qubits (totWiresDef as n K d) :=
    updateOn (eRec2 as n K d) z
      (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
        (hb1ArrOfList K (hbSeqState s1 k) (by rw [hbSeqState_length]; exact hs1_len) d_arr))
  have h0 : st 0 = z := by
    apply updateOn_noop; exact hzRec
  conv_lhs => rw [← h0]
  dsimp only [hbSeqPassCirc]
  have hinv := hbSeqState_inv s1 (wOf K) hs1_bnd
  have hloop := act_seqList_range st
    (fun p => if hp : p + 1 < arity (dHbOf K + 1) then hbSeqStepCirc as arith n K d h1K p hp else LayeredCircuit.id _)
    (arity (dHbOf K + 1) - 1)
    (fun p hp => by
      have hp' : p + 1 < arity (dHbOf K + 1) := by omega
      rw [dif_pos hp']
      have hst_rec : st p ∘ eRec2 as n K d =
          flatReg (arity (dHbOf K + 1)) (wR1Hb K)
            (hb1ArrOfList K (hbSeqState s1 p) (by rw [hbSeqState_length]; exact hs1_len) d_arr) :=
        updateOn_comp_emb _ _ _
      have hst_seqB : st p ∘ eSeqB as n K d = fun _ => false := by
        dsimp only [st]; rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_eSeqB as n K d)]; exact hzSeqB
      have hst_ctrl : st p ∘ eSeqCtrl as n K d = fun _ => false := by
        dsimp only [st]; rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_eSeqCtrl as n K d)]; exact hzCtrl
      have hst_22 : st p ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false := by
        dsimp only [st]; rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide))]; exact hzAnc22
      obtain ⟨h_mem, h_d0, _, h_ne⟩ := hinv p
      have hlen_p : (hbSeqState s1 p).length = arity (dHbOf K + 1) := by rw [hbSeqState_length]; exact hs1_len
      have hr0 := h_mem ((hbSeqState s1 p)[p]'(by rw [hlen_p]; omega)) (List.getElem_mem (by rw [hlen_p]; omega))
      have hr1 := h_mem ((hbSeqState s1 p)[p + 1]'(by rw [hlen_p]; exact hp')) (List.getElem_mem (by rw [hlen_p]; exact hp'))
      have hr1_ne := h_ne (p + 1) (by omega) (by omega)
      have hr0_d0 := h_d0 p (by omega) (le_refl p)
      have hstep := act_hbSeqStepCirc comb as arith n K d h1K p hp' (st p) (hbSeqState s1 p) hlen_p d_arr
        hst_rec hst_seqB hst_ctrl hst_22 hr0.1 hr1.1 hr1_ne hr0_d0
        hr0.2.1 hr1.2.1 hr0.2.2.1 hr1.2.2.1 hr0.2.2.2.1 hr1.2.2.2.1
      rw [hstep]
      dsimp only [st]
      rw [updateOn_idem]
      apply congrArg ket; apply congrArg (updateOn (eRec2 as n K d) z)
      apply congrArg (flatReg (arity (dHbOf K + 1)) (wR1Hb K))
      exact hb1ArrOfList_congr (hbSeqState_succ s1 p).symm _ _ d_arr)
  rw [hloop]
  dsimp only [st]
  have h1pos : 1 ≤ s1.length := by rw [hs1_len]; have := Nat.two_pow_pos (dHbOf K + 1); rw [arity_eq_two_pow]; omega
  have hpass_eq : hbSeqPass s1 = hbSeqState s1 (arity (dHbOf K + 1) - 1) := by
    rw [hbSeqPass_eq_hbSeqState s1 h1pos, hs1_len]
  apply congrArg ket; apply congrArg (updateOn (eRec2 as n K d) z)
  apply congrArg (flatReg (arity (dHbOf K + 1)) (wR1Hb K))
  exact hb1ArrOfList_congr hpass_eq.symm _ _ d_arr

/-! #### 7.6 Copy Active/Bucket Payload Metadata to `eRec3` (`copyToRec3Circ`) -/


end HarmBucketWork54

open QuantumLTF.Membership.Supplement HarmBucketWork54 in
theorem solution : Nonempty QuantumLTF.Membership.Supplement.HarmBucketRouteA54 :=
  ⟨{
    hbInitCirc_size := fun as arith n K d => hbInitCirc_size as arith n K d
    sortHb1Circ_size := fun as br n K d => sortHb1Circ_size as br n K d
    hbSeqPassCirc_size := fun as arith n K d h1K => hbSeqPassCirc_size as arith n K d h1K
    rec2SortedArr_eq_hb1Spec := fun comb br {_n _K} h1K l => rec2SortedArr_eq_hb1Spec comb br h1K l
    act_hbInitCirc := fun comb as arith n K d {_l} z h1 h2 h3 h4 => act_hbInitCirc comb as arith n K d z h1 h2 h3 h4
    act_sortHb1Circ := fun as br n K d {_l} z h1 h2 h3 => act_sortHb1Circ as br n K d z h1 h2 h3
    act_hbSeqPassCirc := fun comb as arith n K d h1K z s1 hs1 hb d_arr h1 h2 h3 h4 =>
      act_hbSeqPassCirc comb as arith n K d h1K z s1 hs1 hb d_arr h1 h2 h3 h4
  }⟩
