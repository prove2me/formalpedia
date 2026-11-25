-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.harm_bucket_route_b_54
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T08:10:43.409017+00:00
-- url     : https://prove2.me/submissions/b4ca5e75-26fd-4f19-a27e-2f0ec738fffe

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
import Theorems.Thm_QuantumLTF_Membership_Supplement_harm_bucket_route_a_54

set_option autoImplicit false

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

lemma copyToRec3SlotCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    (copyToRec3SlotCirc as arith n K d q).size ≤ 2 * wOf K + 3 := by
  dsimp [copyToRec3SlotCirc]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, LayeredCircuit.mapWires_size]
  rw [arith.copyRegCircuit_size 1, arith.copyRegCircuit_size (wOf K), arith.copyRegCircuit_size 2]
  omega

lemma act_copyToRec3SlotCirc (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (z : Qubits (totWiresDef as n K d))
    (L : List HBRec) (hL : L.length = arity (dHbOf K + 1)) (hL_kind : ∀ r ∈ L, r.kind ≤ 3)
    (d2_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (arr3 : Fin (arity (dHbOf K + 1)) → Qubits (wR2Hb K))
    (hz2 : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d2_arr))
    (hz3 : z ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K) arr3)
    (q : Fin (arity (dHbOf K + 1))) (hq0 : arr3 q = fun _ => false) :
    act (copyToRec3SlotCirc as arith n K d q).unitary (ket z) =
      ket (updateOn (eRec3 as n K d) z
        (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
          (Function.update arr3 q (hbRecToRec3Bits (wOf K) (L[q.1]'(by omega)) (fun _ => false))))) := by
  let w := wOf K
  let r := L[q.1]'(by omega)
  let eSlot3 := ancRegSlot as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) q
  let slot3 := rec3SlotFn w (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
  let slot3_1 := rec3SlotFn w (natToBits 1 (hbGroup r)) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
  let slot3_2 := rec3SlotFn w (natToBits 1 (hbGroup r)) (natToBits w r.dest) (fun _ => false) (fun _ => false) (fun _ => false)
  let slot3_3 := rec3SlotFn w (natToBits 1 (hbGroup r)) (natToBits w r.dest) (natToBits w r.orig) (fun _ => false) (fun _ => false)
  have hslot2 := comp_ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _)
    z (hb1ArrOfList K L hL d2_arr) hz2 q
  have hz_slot3 : z = updateOn eSlot3 z slot3 := by
    symm; apply updateOn_noop
    rw [comp_ancRegSlot as n K d ⟨13, by decide⟩ _ _ (ancLen_13 n K d _) z arr3 hz3 q, hq0]
    dsimp only [slot3]; rw [rec3SlotFn_zero]
  have hrk : r.kind ≤ 3 := hL_kind r (List.getElem_mem (by omega))
  dsimp only [copyToRec3SlotCirc]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, LayeredCircuit.id_unitary, act_one]
  conv_lhs => rw [hz_slot3]
  -- c0: copy eRec2KindMsb -> eRec3Group
  rw [act_copyRegOn arith]
  have hc0_in : updateOn eSlot3 z slot3 ∘ eRec3Group as n K d q = fun _ => false := by
    dsimp only [eSlot3, eRec3Group]; rw [comp_ancRegField_of_eq_slot]; exact rec3SlotFn_comp_0 ..
  have hc0_src : updateOn eSlot3 z slot3 ∘ eRec2KindMsb as n K d q = natToBits 1 (hbGroup r) := by
    dsimp only [eSlot3]; rw [updateOn_comp_disjoint _ _ (eRec3Slot_disjoint_eRec2KindMsb as n K d q)]
    have hk2 : z ∘ eRec2Kind as n K d q = natToBits 2 r.kind := by
      change (z ∘ ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q) ∘
        sliceEmb (wK1Hb K) 2 _ = natToBits 2 r.kind
      rw [hslot2]; exact rec2SlotFn_comp_5 ..
    rw [← natToBits_two_zero_eq_hbGroup comb r hrk]
    funext j; have hj0 : j = 0 := Fin.ext (by omega); subst hj0
    exact congrFun hk2 ⟨0, by decide⟩
  have hv0 : (fun j => xor (updateOn eSlot3 z slot3 (eRec3Group as n K d q j))
      (updateOn eSlot3 z slot3 (eRec2KindMsb as n K d q j))) = natToBits 1 (hbGroup r) := by
    funext j
    change xor ((updateOn eSlot3 z slot3 ∘ eRec3Group as n K d q) j)
      ((updateOn eSlot3 z slot3 ∘ eRec2KindMsb as n K d q) j) = natToBits 1 (hbGroup r) j
    rw [hc0_in, hc0_src, xor_false_left]
  rw [hv0]
  have hupd3_0 : updateOn (eRec3Group as n K d q) (updateOn eSlot3 z slot3) (natToBits 1 (hbGroup r)) =
      updateOn eSlot3 z slot3_1 := by
    dsimp only [eRec3Group, eSlot3, slot3, slot3_1, w]
    rw [updateOn_ancRegField_on_slot, updateOn_rec3SlotFn_0]
  rw [hupd3_0]
  change act _ (act _ (act _ (ket (updateOn eSlot3 z slot3_1)))) = _
  -- c1: copy eRec2Dest -> eRec3Dest
  rw [act_copyRegOn arith]
  have hc1_in : updateOn eSlot3 z slot3_1 ∘ eRec3Dest as n K d q = fun _ => false := by
    dsimp only [eSlot3, eRec3Dest]; rw [comp_ancRegField_of_eq_slot]; exact rec3SlotFn_comp_1 ..
  have hc1_src : updateOn eSlot3 z slot3_1 ∘ eRec2Dest as n K d q = natToBits w r.dest := by
    dsimp only [eSlot3]; rw [updateOn_comp_disjoint _ _ (eRec3Slot_disjoint_eRec2Dest as n K d q)]
    change (z ∘ ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q) ∘
      sliceEmb (wK1Hb K + 2) w _ = natToBits w r.dest
    rw [hslot2]; exact rec2SlotFn_comp_6 ..
  have hv1 : (fun j => xor (updateOn eSlot3 z slot3_1 (eRec3Dest as n K d q j))
      (updateOn eSlot3 z slot3_1 (eRec2Dest as n K d q j))) = natToBits w r.dest := by
    funext j
    change xor ((updateOn eSlot3 z slot3_1 ∘ eRec3Dest as n K d q) j)
      ((updateOn eSlot3 z slot3_1 ∘ eRec2Dest as n K d q) j) = natToBits w r.dest j
    rw [hc1_in, hc1_src, xor_false_left]
  rw [hv1]
  have hupd3_1 : updateOn (eRec3Dest as n K d q) (updateOn eSlot3 z slot3_1) (natToBits w r.dest) =
      updateOn eSlot3 z slot3_2 := by
    dsimp only [eRec3Dest, eSlot3, slot3_1, slot3_2, w]
    rw [updateOn_ancRegField_on_slot, updateOn_rec3SlotFn_1]
  rw [hupd3_1]
  change act _ (act _ (ket (updateOn eSlot3 z slot3_2))) = _
  -- c2: copy eRec2Orig -> eRec3Orig
  rw [act_copyRegOn arith]
  have hc2_in : updateOn eSlot3 z slot3_2 ∘ eRec3Orig as n K d q = fun _ => false := by
    dsimp only [eSlot3, eRec3Orig]; rw [comp_ancRegField_of_eq_slot]; exact rec3SlotFn_comp_2 ..
  have hc2_src : updateOn eSlot3 z slot3_2 ∘ eRec2Orig as n K d q = natToBits w r.orig := by
    dsimp only [eSlot3]; rw [updateOn_comp_disjoint _ _ (eRec3Slot_disjoint_eRec2Orig as n K d q)]
    change (z ∘ ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q) ∘
      sliceEmb (1 + w + w + 2) w _ = natToBits w r.orig
    rw [hslot2]; exact rec2SlotFn_comp_4 ..
  have hv2 : (fun j => xor (updateOn eSlot3 z slot3_2 (eRec3Orig as n K d q j))
      (updateOn eSlot3 z slot3_2 (eRec2Orig as n K d q j))) = natToBits w r.orig := by
    funext j
    change xor ((updateOn eSlot3 z slot3_2 ∘ eRec3Orig as n K d q) j)
      ((updateOn eSlot3 z slot3_2 ∘ eRec2Orig as n K d q) j) = natToBits w r.orig j
    rw [hc2_in, hc2_src, xor_false_left]
  rw [hv2]
  have hupd3_2 : updateOn (eRec3Orig as n K d q) (updateOn eSlot3 z slot3_2) (natToBits w r.orig) =
      updateOn eSlot3 z slot3_3 := by
    dsimp only [eRec3Orig, eSlot3, slot3_2, slot3_3, w]
    rw [updateOn_ancRegField_on_slot, updateOn_rec3SlotFn_2]
  rw [hupd3_2]
  change act _ (ket (updateOn eSlot3 z slot3_3)) = _
  -- c3: copy eRec2Kind -> eRec3Kind
  rw [act_copyRegOn arith]
  have hc3_in : updateOn eSlot3 z slot3_3 ∘ eRec3Kind as n K d q = fun _ => false := by
    dsimp only [eSlot3, eRec3Kind]; rw [comp_ancRegField_of_eq_slot]; exact rec3SlotFn_comp_3 ..
  have hc3_src : updateOn eSlot3 z slot3_3 ∘ eRec2Kind as n K d q = natToBits 2 r.kind := by
    dsimp only [eSlot3]; rw [updateOn_comp_disjoint _ _ (eRec3Slot_disjoint_eRec2Kind as n K d q)]
    change (z ∘ ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q) ∘
      sliceEmb (wK1Hb K) 2 _ = natToBits 2 r.kind
    rw [hslot2]; exact rec2SlotFn_comp_5 ..
  have hv3 : (fun j => xor (updateOn eSlot3 z slot3_3 (eRec3Kind as n K d q j))
      (updateOn eSlot3 z slot3_3 (eRec2Kind as n K d q j))) = natToBits 2 r.kind := by
    funext j
    change xor ((updateOn eSlot3 z slot3_3 ∘ eRec3Kind as n K d q) j)
      ((updateOn eSlot3 z slot3_3 ∘ eRec2Kind as n K d q) j) = natToBits 2 r.kind j
    rw [hc3_in, hc3_src, xor_false_left]
  rw [hv3]
  dsimp only [eRec3Kind, eSlot3, slot3_3, w]
  rw [updateOn_ancRegField_on_slot, updateOn_rec3SlotFn_3]
  rw [updateOn_ancRegSlot_eq as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) z arr3 hz3 q]
  rfl

lemma copyToRec3Circ_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) :
    (copyToRec3Circ as arith n K d).size ≤ arity (dHbOf K + 1) * (2 * wOf K + 3) := by
  dsimp [copyToRec3Circ]
  have h := LayeredCircuit_seqList_size_le
    ((List.range (arity (dHbOf K + 1))).map fun q =>
      if hq : q < arity (dHbOf K + 1) then copyToRec3SlotCirc as arith n K d ⟨q, hq⟩ else LayeredCircuit.id _)
    (2 * wOf K + 3)
    (by
      intro lc hlc; simp only [List.mem_map] at hlc; rcases hlc with ⟨q, _, rfl⟩
      split_ifs with hq
      · exact copyToRec3SlotCirc_size as arith n K d ⟨q, hq⟩
      · simp)
  simpa using h

lemma act_copyToRec3Circ (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (z : Qubits (totWiresDef as n K d))
    (L : List HBRec) (hL : L.length = arity (dHbOf K + 1)) (hL_kind : ∀ r ∈ L, r.kind ≤ 3)
    (d2_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz2 : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d2_arr))
    (hz3 : z ∘ ancEmb as n K d ⟨13, by decide⟩ = fun _ => false) :
    act (copyToRec3Circ as arith n K d).unitary (ket z) =
      ket (updateOn (eRec3 as n K d) z
        (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K L hL (fun _ _ => false)))) := by
  let arrP (p : ℕ) (q : Fin (arity (dHbOf K + 1))) : Qubits (wR2Hb K) :=
    if q.1 < p then hb3ArrOfList K L hL (fun _ _ => false) q else fun _ => false
  let st (p : ℕ) : Qubits (totWiresDef as n K d) :=
    updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (arrP p))
  have h0 : st 0 = z := by
    apply updateOn_noop; funext idx
    rcases finProdFinEquiv.surjective idx with ⟨⟨q, b⟩, rfl⟩
    have hzr : z (eRec3 as n K d (finProdFinEquiv (q, b))) = false := congrFun hz3 _
    simp [hzr, arrP, flatReg]
  conv_lhs => rw [← h0]
  dsimp [copyToRec3Circ]
  have hloop := act_seqList_range st
    (fun q => if hq : q < arity (dHbOf K + 1) then copyToRec3SlotCirc as arith n K d ⟨q, hq⟩ else LayeredCircuit.id _)
    (arity (dHbOf K + 1))
    (fun q hq => by
      rw [dif_pos hq]
      have hst2 : st q ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d2_arr) := by
        dsimp only [st]; rw [updateOn_comp_disjoint _ _ (eRec3_disjoint_eRec2 as n K d)]
        exact hz2
      have hst3 : st q ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K) (arrP q) :=
        updateOn_comp_emb _ _ _
      have hq0 : arrP q ⟨q, hq⟩ = fun _ => false := by dsimp [arrP]; simp
      have hstep := act_copyToRec3SlotCirc comb as arith n K d (st q) L hL hL_kind d2_arr (arrP q) hst2 hst3 ⟨q, hq⟩ hq0
      rw [hstep]
      dsimp only [st]
      rw [updateOn_idem]
      apply congrArg ket; apply congrArg (updateOn (eRec3 as n K d) z)
      apply congrArg (flatReg (arity (dHbOf K + 1)) (wR2Hb K)); funext r
      by_cases hr : r = ⟨q, hq⟩
      · subst hr; simp [arrP, hb3ArrOfList]
      · rw [Function.update_of_ne hr]
        have hne : r.1 ≠ q := fun hv => hr (Fin.ext hv)
        by_cases hlt : r.1 < q
        · simp [arrP, hlt, Nat.lt_trans hlt (Nat.lt_succ_self _)]
        · simp [arrP, hlt, show ¬ r.1 < q + 1 by omega])
  rw [hloop]
  dsimp only [st]
  have harr : arrP (arity (dHbOf K + 1)) = hb3ArrOfList K L hL (fun _ _ => false) := funext fun q => by
    dsimp only [arrP]; rw [if_pos q.isLt]
  rw [harr]

/-! #### 7.7 Sorting 2 (`sortHb2Circ`, `hb2SortedList`, `step3Circ`) -/

lemma sortHb2Circ_size (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ) :
    ((sortHb2Circ as br n K d).size : ℝ) ≤
      br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR2Hb K : ℝ) + 1) := by
  dsimp [sortHb2Circ]
  rw [LayeredCircuit.mapWires_size]
  simpa [wR2Hb, add_assoc] using br.bitonicSortKeyCircuit_size (dHbOf K + 1) (wK2Hb K) (wP2Hb K) true

lemma act_sortHb2Circ (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ)
    {l : Fin (2 * K) → Fin (n + 1)} (z : Qubits (totWiresDef as n K d))
    (hzRec : z ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K) (rec3InitArr K l))
    (hzTr : z ∘ ancEmb as n K d ⟨14, by decide⟩ = fun _ => false)
    (hzAnc : z ∘ ancEmb as n K d ⟨18, by decide⟩ = fun _ => false) :
    act (sortHb2Circ as br n K d).unitary (ket z) =
      ket (updateOn (eTr2b as n K d)
        (updateOn (eRec3 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (rec3SortedArr K l)))
        (rec3SortTr K l)) := by
  dsimp only [sortHb2Circ]
  have htr : z ∘ eTr2b as n K d = fun _ => false := funext fun j => congrFun hzTr _
  have hanc : z ∘ eSort2bAnc as n K d = fun _ => false := funext fun k => congrFun hzAnc _
  have hcomp := comp_packDTA54Emb (eRec3 as n K d) (eTr2b as n K d) (eSort2bAnc as n K d)
    (eRec3_disjoint_eTr2b as n K d) (eRec3_disjoint_eSort2bAnc as n K d) (eTr2b_disjoint_eSort2bAnc as n K d)
    z (rec3InitArr K l) (fun _ => false) hzRec htr hanc
  have hact := act_mapWires_ket_singleton _ _ z _ (by
    rw [hcomp]
    exact br.act_bitonicSortKeyCircuit_ket (dHbOf K + 1) (wK2Hb K) (wP2Hb K) true (rec3InitArr K l))
  rw [hact]; congr 1
  exact updateOn_packDTA54_eq_two (eRec3 as n K d) (eTr2b as n K d) (eSort2bAnc as n K d)
    (eRec3_disjoint_eTr2b as n K d) (eRec3_disjoint_eSort2bAnc as n K d) (eTr2b_disjoint_eSort2bAnc as n K d)
    z hanc (rec3SortedArr K l) (rec3SortTr K l)

lemma rec3SortedArr_eq_hb2Spec (comb : LcgSym54Comb) (br : BitonicRouting54) {n K : ℕ} (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) :
    rec3SortedArr K l =
      hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (fun _ _ => false) := by
  let key : Qubits (wR2Hb K) → ℕ := fun r => bitsToNat (recKey54 r)
  let L₁ : List (Qubits (wR2Hb K)) := List.ofFn (rec3SortedArr K l)
  let L₂ : List (Qubits (wR2Hb K)) := (hb2SortedList K l).map (fun r => hbRecToRec3Bits (wOf K) r (fun _ => false))
  have hofFn_init : List.ofFn (rec3InitArr K l) =
      (hbSeqPass (hb1SortedList K l)).map (fun r => hbRecToRec3Bits (wOf K) r (fun _ => false)) := by
    apply List.ext_getElem
    · simp [hbSeqPass_length, hb1SortedList_length]
    · intro idx h1 h2
      rw [List.length_ofFn] at h1
      simp only [List.getElem_ofFn, List.getElem_map, rec3InitArr, hb3ArrOfList]
  have hperm12 : L₁.Perm L₂ := by
    have hp1 : L₁.Perm (List.ofFn (rec3InitArr K l)) :=
      br.sort_perm key (dHbOf K + 1) true (rec3InitArr K l)
    rw [hofFn_init] at hp1
    exact hp1.trans ((List.mergeSort_perm _ _).symm.map _)
  have hp1 : L₁.Pairwise (fun x y => key x ≤ key y) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_ofFn] at hi hj
    simp only [L₁, List.getElem_ofFn]
    exact br.monotone_sort key (dHbOf K + 1) (rec3InitArr K l) (Nat.le_of_lt hij)
  have hpw_s2 : (hb2SortedList K l).Pairwise (fun a b => hbKey2 a ≤ hbKey2 b) := by
    have hpw : (hb2SortedList K l).Pairwise (fun a b => decide (hbKey2 a ≤ hbKey2 b) = true) := by
      dsimp [hb2SortedList]
      exact List.pairwise_mergeSort
        (fun a b c => by simp only [decide_eq_true_eq]; exact le_trans)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
        (hbSeqPass (hb1SortedList K l))
    exact hpw.imp (fun {a b} h => decide_eq_true_eq.mp h)
  have hbnd : ∀ r ∈ hb2SortedList K l, r.dest < 2 ^ wOf K ∧ r.orig < 2 ^ wOf K := by
    intro r hr
    have hr' := (List.mergeSort_perm _ _).mem_iff.mp hr
    have h := hbSeqPass_hb1_bounds comb h1K l r hr'
    exact ⟨h.2.2.2.1, h.2.2.2.2⟩
  have hp2 : L₂.Pairwise (fun x y => key x ≤ key y) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_map] at hi hj
    simp only [L₂, List.getElem_map]
    have ha := hbnd _ (List.getElem_mem hi)
    have hb := hbnd _ (List.getElem_mem hj)
    dsimp [key]
    rw [hbKey2_bitsToNat_le_iff comb (wOf K) _ _ _ _ ha.1 hb.1 ha.2 hb.2]
    exact List.pairwise_iff_getElem.mp hpw_s2 i j hi hj hij
  have hinj : ∀ x ∈ L₂, ∀ y ∈ L₂, key x = key y → x = y := by
    intro x hx y hy hxy
    simp only [L₂, List.mem_map] at hx hy
    rcases hx with ⟨rx, hrx, rfl⟩
    rcases hy with ⟨ry, hry, rfl⟩
    have bx := hbnd rx hrx
    have byy := hbnd ry hry
    dsimp [key] at hxy
    rw [hbKey2_bitsToNat_eq_iff comb (wOf K) rx ry _ _ bx.1 byy.1 bx.2 byy.2] at hxy
    have horig := comb.hbKey2_orig_inj rx ry hxy
    have hreq := eq_of_mem_of_nodup_map (·.orig) (hb2SortedList_orig_nodup K l) hrx hry horig
    subst hreq; rfl
  have heq : L₁ = L₂ := comb.perm_eq_of_sorted_of_inj key L₁ L₂ hperm12 hp1 hp2 hinj
  funext q
  have hget := congrArg (fun xs : List (Qubits (wR2Hb K)) => xs[q.1]?.getD (fun _ => false)) heq
  have hlen₂ : L₂.length = arity (dHbOf K + 1) := by simp [L₂, hb2SortedList_length]
  have hL1 : L₁[q.1]? = some (rec3SortedArr K l q) := by
    rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact q.isLt)]
    simp [L₁]
  have hL2 : L₂[q.1]? = some (hbRecToRec3Bits (wOf K) ((hb2SortedList K l)[q.1]'(by rw [hb2SortedList_length]; exact q.isLt)) (fun _ => false)) := by
    rw [List.getElem?_eq_getElem (by rw [hlen₂]; exact q.isLt)]
    simp [L₂]
  rw [hL1, hL2] at hget
  exact hget

lemma step3Circ_size (as : AlonsoSchottSil54) (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (routeA : HarmBucketRouteA54) (n K d : ℕ) (h1K : 1 ≤ K) :
    ((step3Circ as br arith n K d h1K).size : ℝ) ≤
      ((arity (dHbOf K + 1) : ℕ) : ℝ) * (74 * (wOf K : ℝ) + 336 +
        br.C_sort * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + (wR2Hb K : ℝ) + 2)) := by
  dsimp [step3Circ]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Nat.cast_add]
  have h1 : ((hbInitCirc as arith n K d).size : ℝ) ≤
      (arity (dHbOf K + 1) : ℝ) * (11 * (wOf K : ℝ) + 12) := by
    exact_mod_cast routeA.hbInitCirc_size as arith n K d
  have h2 := routeA.sortHb1Circ_size as br n K d
  have h3 : ((hbSeqPassCirc as arith n K d h1K).size : ℝ) ≤
      (arity (dHbOf K + 1) : ℝ) * (61 * (wOf K : ℝ) + 321) := by
    have hnat : (hbSeqPassCirc as arith n K d h1K).size ≤ arity (dHbOf K + 1) * (61 * wOf K + 321) :=
      Nat.le_trans (routeA.hbSeqPassCirc_size as arith n K d h1K) (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    exact_mod_cast hnat
  have h4 : ((copyToRec3Circ as arith n K d).size : ℝ) ≤
      (arity (dHbOf K + 1) : ℝ) * (2 * (wOf K : ℝ) + 3) := by
    exact_mod_cast copyToRec3Circ_size as arith n K d
  have h5 := sortHb2Circ_size as br n K d
  have har : (arity (dHbOf K + 1) : ℝ) = (2 ^ (dHbOf K + 1) : ℝ) := by
    rw [arity_eq_two_pow]; push_cast; rfl
  rw [← har] at h2 h5
  dsimp only [wR1Hb, wK1Hb, wP1Hb, wR2Hb, wK2Hb, wP2Hb] at *
  push_cast at *
  nlinarith [br.hC_sort_pos]

lemma act_step3Circ (comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (routeA : HarmBucketRouteA54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) {l : Fin (2 * K) → Fin (n + 1)}
    (z : Qubits (totWiresDef as n K d))
    (hzAct : z ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l))
    (hzM : z ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l))
    (hzOcc : z ∘ eOccReg as n K d = flatReg (2 * K) (wOf K) (occBitsFn K l))
    (hz11 : z ∘ ancEmb as n K d ⟨11, by decide⟩ = fun _ => false)
    (hz12 : z ∘ ancEmb as n K d ⟨12, by decide⟩ = fun _ => false)
    (hz13 : z ∘ ancEmb as n K d ⟨13, by decide⟩ = fun _ => false)
    (hz14 : z ∘ ancEmb as n K d ⟨14, by decide⟩ = fun _ => false)
    (hz17 : z ∘ ancEmb as n K d ⟨17, by decide⟩ = fun _ => false)
    (hz18 : z ∘ ancEmb as n K d ⟨18, by decide⟩ = fun _ => false)
    (hz19 : z ∘ ancEmb as n K d ⟨19, by decide⟩ = fun _ => false)
    (hz20 : z ∘ ancEmb as n K d ⟨20, by decide⟩ = fun _ => false)
    (hz22 : z ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false) :
    act (step3Circ as br arith n K d h1K).unitary (ket z) =
      ket (updateOn (eTr2b as n K d)
        (updateOn (eRec3 as n K d)
          (updateOn (eTr2a as n K d)
            (updateOn (eRec2 as n K d) z
              (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
                (hb1ArrOfList K (hbSeqPass (hb1SortedList K l))
                  (by rw [hbSeqPass_length, hb1SortedList_length]) (fun _ _ => false))))
            (rec2SortTr K l))
          (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (rec3SortedArr K l)))
        (rec3SortTr K l)) := by
  dsimp [step3Circ]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, LayeredCircuit.id_unitary, act_one]
  -- 1. hbInitCirc
  rw [routeA.act_hbInitCirc comb as arith n K d z hzAct hzM hzOcc hz11]
  let z1 := updateOn (eRec2 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hbInitArr K l))
  -- 2. sortHb1Circ
  have hz1_rec : z1 ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hbInitArr K l) :=
    updateOn_comp_emb _ _ _
  have hz1_tr : z1 ∘ ancEmb as n K d ⟨12, by decide⟩ = fun _ => false := by
    dsimp only [z1]; rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨12, by decide⟩ (by decide))]; exact hz12
  have hz1_anc : z1 ∘ ancEmb as n K d ⟨17, by decide⟩ = fun _ => false := by
    dsimp only [z1]; rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨17, by decide⟩ (by decide))]; exact hz17
  rw [routeA.act_sortHb1Circ as br n K d z1 hz1_rec hz1_tr hz1_anc]
  let z2 := updateOn (eTr2a as n K d)
    (updateOn (eRec2 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (rec2SortedArr K l)))
    (rec2SortTr K l)
  have hz2_eq : updateOn (eTr2a as n K d) (updateOn (eRec2 as n K d) z1
      (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (rec2SortedArr K l))) (rec2SortTr K l) = z2 := by
    dsimp only [z1, z2]; rw [updateOn_idem]
  rw [hz2_eq]
  -- 3. hbSeqPassCirc
  have hs1_len := hb1SortedList_length K l
  have hz2_rec : z2 ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K)
      (hb1ArrOfList K (hb1SortedList K l) hs1_len (fun _ _ => false)) := by
    dsimp only [z2]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_eRec2 as n K d)]
    rw [updateOn_comp_emb, ← routeA.rec2SortedArr_eq_hb1Spec comb br h1K l]
  have hz2_seqB : z2 ∘ eSeqB as n K d = fun _ => false := by
    dsimp only [z2]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_eSeqB as n K d)]
    rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_eSeqB as n K d)]
    exact funext fun j => congrFun hz19 _
  have hz2_ctrl : z2 ∘ eSeqCtrl as n K d = fun _ => false := by
    dsimp only [z2]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_eSeqCtrl as n K d)]
    rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_eSeqCtrl as n K d)]
    exact funext fun j => congrFun hz20 _
  have hz2_22 : z2 ∘ ancEmb as n K d ⟨22, by decide⟩ = fun _ => false := by
    dsimp only [z2]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide))]
    rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨22, by decide⟩ (by decide))]
    exact hz22
  have hs1_bnd : ∀ r ∈ hb1SortedList K l, r.kind ≤ 3 ∧ r.kind ≠ 2 ∧ (r.kind = 0 → r.dest = 0) ∧
      r.m < 2 ^ wOf K ∧ r.occ < 2 ^ wOf K ∧ r.dest < 2 ^ wOf K ∧ r.orig < 2 ^ wOf K := fun r hr =>
    hbInit_bounds comb h1K l r ((hb1SortedList_mem_iff K l r).mp hr)
  rw [routeA.act_hbSeqPassCirc comb as arith n K d h1K z2 (hb1SortedList K l) hs1_len hs1_bnd (fun _ _ => false)
    hz2_rec hz2_seqB hz2_ctrl hz2_22]
  let z3 := updateOn (eTr2a as n K d)
    (updateOn (eRec2 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
      (hb1ArrOfList K (hbSeqPass (hb1SortedList K l))
        (by rw [hbSeqPass_length]; exact hs1_len) (fun _ _ => false))))
    (rec2SortTr K l)
  have hz3_eq : updateOn (eRec2 as n K d) z2
      (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
        (hb1ArrOfList K (hbSeqPass (hb1SortedList K l))
          (by rw [hbSeqPass_length]; exact hs1_len) (fun _ _ => false))) = z3 := by
    dsimp only [z2, z3]
    rw [updateOn_comm (eRec2 as n K d) (eTr2a as n K d) (eRec2_disjoint_eTr2a as n K d), updateOn_idem]
  rw [hz3_eq]
  -- 4. copyToRec3Circ
  have hpass_len : (hbSeqPass (hb1SortedList K l)).length = arity (dHbOf K + 1) := by
    rw [hbSeqPass_length]; exact hs1_len
  have hpass_kind : ∀ r ∈ hbSeqPass (hb1SortedList K l), r.kind ≤ 3 := fun r hr =>
    (hbSeqPass_hb1_bounds comb h1K l r hr).1
  have hz3_rec2 : z3 ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K)
      (hb1ArrOfList K (hbSeqPass (hb1SortedList K l)) hpass_len (fun _ _ => false)) := by
    dsimp only [z3]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_eRec2 as n K d)]
    exact updateOn_comp_emb _ _ _
  have hz3_13 : z3 ∘ ancEmb as n K d ⟨13, by decide⟩ = fun _ => false := by
    dsimp only [z3]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_anc_other as n K d ⟨13, by decide⟩ (by decide))]
    rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨13, by decide⟩ (by decide))]
    exact hz13
  rw [act_copyToRec3Circ comb as arith n K d z3 (hbSeqPass (hb1SortedList K l)) hpass_len hpass_kind
    (fun _ _ => false) hz3_rec2 hz3_13]
  -- 5. sortHb2Circ
  let z4 := updateOn (eRec3 as n K d) z3 (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (rec3InitArr K l))
  have hz4_rec3 : z4 ∘ eRec3 as n K d = flatReg (arity (dHbOf K + 1)) (wR2Hb K) (rec3InitArr K l) :=
    updateOn_comp_emb _ _ _
  have hz4_14 : z4 ∘ ancEmb as n K d ⟨14, by decide⟩ = fun _ => false := by
    dsimp only [z4, z3]
    rw [updateOn_comp_disjoint _ _ (eRec3_disjoint_anc_other as n K d ⟨14, by decide⟩ (by decide))]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_anc_other as n K d ⟨14, by decide⟩ (by decide))]
    rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨14, by decide⟩ (by decide))]
    exact hz14
  have hz4_18 : z4 ∘ ancEmb as n K d ⟨18, by decide⟩ = fun _ => false := by
    dsimp only [z4, z3]
    rw [updateOn_comp_disjoint _ _ (eRec3_disjoint_anc_other as n K d ⟨18, by decide⟩ (by decide))]
    rw [updateOn_comp_disjoint _ _ (eTr2a_disjoint_anc_other as n K d ⟨18, by decide⟩ (by decide))]
    rw [updateOn_comp_disjoint _ _ (eRec2_disjoint_anc_other as n K d ⟨18, by decide⟩ (by decide))]
    exact hz18
  have hz4_eq : updateOn (eRec3 as n K d) z3
      (flatReg (arity (dHbOf K + 1)) (wR2Hb K)
        (hb3ArrOfList K (hbSeqPass (hb1SortedList K l)) hpass_len (fun _ _ => false))) = z4 := rfl
  rw [hz4_eq]
  rw [act_sortHb2Circ as br n K d z4 hz4_rec3 hz4_14 hz4_18]
  dsimp only [z4, z3]; rw [updateOn_idem]

lemma buildRouteB (routeA : HarmBucketRouteA54) : QuantumLTF.Membership.Supplement.HarmBucketRouteB54 :=
  {
    copyToRec3Circ_size := fun as arith n K d => copyToRec3Circ_size as arith n K d
    sortHb2Circ_size := fun as br n K d => sortHb2Circ_size as br n K d
    step3Circ_size := fun as br arith n K d h1K => step3Circ_size as br arith routeA n K d h1K
    rec3SortedArr_eq_hb2Spec := fun comb br {_n _K} h1K l => rec3SortedArr_eq_hb2Spec comb br h1K l
    act_copyToRec3Circ := fun comb as arith n K d z s2 hs2 hk d2 h1 h2 =>
      act_copyToRec3Circ comb as arith n K d z s2 hs2 hk d2 h1 h2
    act_step3Circ := fun comb br as arith n K d h1K {_l} z h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      act_step3Circ comb br as routeA arith n K d h1K z h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  }

end HarmBucketWork54

open QuantumLTF.Membership.Supplement HarmBucketWork54 in
theorem solution : Nonempty QuantumLTF.Membership.Supplement.HarmBucketRouteB54 :=
  let ⟨routeA⟩ := QuantumLTF.Membership.Supplement.harm_bucket_route_a_54
  ⟨buildRouteB routeA⟩
