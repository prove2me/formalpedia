-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.harm_bucket_occ_54
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T07:31:18.029721+00:00
-- url     : https://prove2.me/submissions/72782b43-2599-4218-80b1-274232b250d9

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

lemma step1StepCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (k : ℕ) (hk : k + 1 < 2 * K) :
    (step1StepCirc as arith n K d k hk).size ≤ 28 * sOf n + 42 * wOf K + 28 := by
  dsimp [step1StepCirc]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, LayeredCircuit.mapWires_size]
  have h1 := arith.eqRegCircuit_size (sOf n)
  have h2 := arith.ctrlCopyRegCircuit_size (wOf K)
  have h3 := arith.setConstMSBCircuit_size 1 1
  have h4 := arith.ctrlAddConstInPlaceMSBCircuit_size (wOf K) 1
  have h7 := arith.ltConstMSBCircuit_size (wOf K) 2
  omega

noncomputable def step1State (as : AlonsoSchottSil54) (n K d : ℕ) (l : Fin (2 * K) → Fin (n + 1))
    (z : Qubits (totWiresDef as n K d)) (p : ℕ) : Qubits (totWiresDef as n K d) :=
  updateOn (eActReg as n K d)
    (updateOn (eMReg as n K d) z
      (flatReg (2 * K) (wOf K) fun i => if i.1 < p then mBitsFn K l i else fun _ => false))
    (flatReg (2 * K) 1 fun i => if i.1 < p then actBitsFn K l i else fun _ => false)

lemma step1State_comp_eL (as : AlonsoSchottSil54) (n K d : ℕ) (l : Fin (2 * K) → Fin (n + 1))
    (z : Qubits (totWiresDef as n K d)) (p : ℕ) :
    step1State as n K d l z p ∘ eL as n K d = z ∘ eL as n K d := by
  dsimp only [step1State]
  rw [updateOn_comp_disjoint _ _ (eActReg_disjoint_eL as n K d),
    updateOn_comp_disjoint _ _ (eMReg_disjoint_eL as n K d)]

lemma step1State_comp_anc_other (as : AlonsoSchottSil54) (n K d : ℕ) (l : Fin (2 * K) → Fin (n + 1))
    (z : Qubits (totWiresDef as n K d)) (p : ℕ) (k : Fin 24)
    (hk0 : k ≠ ⟨0, by decide⟩) (hk1 : k ≠ ⟨1, by decide⟩) :
    step1State as n K d l z p ∘ ancEmb as n K d k = z ∘ ancEmb as n K d k := by
  dsimp only [step1State]
  rw [updateOn_comp_disjoint _ _ (eActReg_disjoint_anc_other as n K d k hk1),
    updateOn_comp_disjoint _ _ (eMReg_disjoint_anc_other as n K d k hk0)]

lemma step1State_comp_eMReg (as : AlonsoSchottSil54) (n K d : ℕ) (l : Fin (2 * K) → Fin (n + 1))
    (z : Qubits (totWiresDef as n K d)) (p : ℕ) :
    step1State as n K d l z p ∘ eMReg as n K d =
      flatReg (2 * K) (wOf K) fun i => if i.1 < p then mBitsFn K l i else fun _ => false := by
  dsimp only [step1State]
  rw [updateOn_comp_disjoint _ _ (fun a b h => eMReg_disjoint_eActReg as n K d b a h.symm),
    updateOn_comp_emb]

lemma step1State_comp_eActReg (as : AlonsoSchottSil54) (n K d : ℕ) (l : Fin (2 * K) → Fin (n + 1))
    (z : Qubits (totWiresDef as n K d)) (p : ℕ) :
    step1State as n K d l z p ∘ eActReg as n K d =
      flatReg (2 * K) 1 fun i => if i.1 < p then actBitsFn K l i else fun _ => false := by
  dsimp only [step1State]
  rw [updateOn_comp_emb]

lemma act_step1StepCirc (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (h1K : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l)
    (z : Qubits (totWiresDef as n K d))
    (hzL : z ∘ eL as n K d = flatReg (2 * K) (sOf n) fun p => particleSym54 n (sOf n) (l p))
    (hz5 : z ∘ ancEmb as n K d ⟨5, by decide⟩ = fun _ => false)
    (hz6 : z ∘ ancEmb as n K d ⟨6, by decide⟩ = fun _ => false)
    (hz10 : z ∘ ancEmb as n K d ⟨10, by decide⟩ = fun _ => false)
    (k : ℕ) (hk : k + 1 < 2 * K) :
    act (step1StepCirc as arith n K d k hk).unitary (ket (step1State as n K d l z (k + 1))) =
      ket (step1State as n K d l z (k + 2)) := by
  dsimp only [step1StepCirc, comb4, comb3]
  set z0 := step1State as n K d l z (k + 1)
  have hz0L : z0 ∘ eL as n K d = flatReg (2 * K) (sOf n) fun p => particleSym54 n (sOf n) (l p) := by
    change step1State as n K d l z (k + 1) ∘ eL as n K d = _
    rw [step1State_comp_eL, hzL]
  have hz05 : z0 ∘ eEqFlag as n K d = fun _ => false := by
    funext i
    have hcomp := step1State_comp_anc_other as n K d l z (k + 1) ⟨5, by decide⟩ (by decide) (by decide)
    exact congrFun (hcomp.trans hz5) _
  have hz06 : z0 ∘ eOne12 as n K d = fun _ => false := by
    funext i
    have hcomp := step1State_comp_anc_other as n K d l z (k + 1) ⟨6, by decide⟩ (by decide) (by decide)
    exact congrFun (hcomp.trans hz6) _
  have hz010 : z0 ∘ ancEmb as n K d ⟨10, by decide⟩ = fun _ => false := by
    change step1State as n K d l z (k + 1) ∘ ancEmb as n K d ⟨10, by decide⟩ = _
    rw [step1State_comp_anc_other as n K d l z (k + 1) ⟨10, by decide⟩ (by decide) (by decide), hz10]
  have hz0M : z0 ∘ eMReg as n K d =
      flatReg (2 * K) (wOf K) fun i => if i.1 < k + 1 then mBitsFn K l i else fun _ => false :=
    step1State_comp_eMReg as n K d l z (k + 1)
  have hz0A : z0 ∘ eActReg as n K d =
      flatReg (2 * K) 1 fun i => if i.1 < k + 1 then actBitsFn K l i else fun _ => false :=
    step1State_comp_eActReg as n K d l z (k + 1)
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul,
    LayeredCircuit.id_unitary, act_one]
  set eqF := eEqFlag as n K d
  set oneW := eOne12 as n K d
  set mk := eMSlot as n K d ⟨k, by omega⟩
  set mk1 := eMSlot as n K d ⟨k + 1, hk⟩
  set ak1 := eActSlot as n K d ⟨k + 1, hk⟩
  let eqB : Bool := decide (l ⟨k, by omega⟩ = l ⟨k + 1, hk⟩)
  -- c1: eqReg
  have hc1_anc : z0 ∘ eArith12Pref as n K d (sOf n) (le_max_left _ _) = fun _ => false := by
    funext i; exact congrFun hz010 _
  rw [act_eqRegOn (arith := arith)
    (hAB := eLSlot_disjoint_slot as n K d (by simp [Fin.ext_iff]))
    (hAO := eLSlot_disjoint_eEqFlag as n K d _)
    (hBO := eLSlot_disjoint_eEqFlag as n K d _)
    (hAA := eLSlot_disjoint_eArith12 as n K d _ _ _)
    (hBA := eLSlot_disjoint_eArith12 as n K d _ _ _)
    (hOA := eEqFlag_disjoint_eArith12 as n K d _ _)
    (z := z0) (hzAnc := hc1_anc)]
  have hlk : z0 ∘ eLSlot as n K d ⟨k, by omega⟩ = particleSym54 n (sOf n) (l ⟨k, by omega⟩) :=
    comp_eLSlot as n K d z0 _ hz0L ⟨k, by omega⟩
  have hlk1 : z0 ∘ eLSlot as n K d ⟨k + 1, hk⟩ = particleSym54 n (sOf n) (l ⟨k + 1, hk⟩) :=
    comp_eLSlot as n K d z0 _ hz0L ⟨k + 1, hk⟩
  have heqF0 : z0 (eqF 0) = false := congrFun hz05 0
  have heq_val : (fun _ : Fin 1 => xor (z0 (eqF 0))
      (decide (z0 ∘ eLSlot as n K d ⟨k, by omega⟩ = z0 ∘ eLSlot as n K d ⟨k + 1, hk⟩))) =
      fun _ => eqB := by
    funext _
    rw [heqF0, xor_false_left, hlk, hlk1]
    simp only [eqB, particleSym54_eq_iff comb]
  set z1 := updateOn eqF z0 (fun _ => eqB)
  have hz1_def : updateOn eqF z0 (fun _ => xor (z0 (eqF 0))
      (decide (z0 ∘ eLSlot as n K d ⟨k, by omega⟩ = z0 ∘ eLSlot as n K d ⟨k + 1, hk⟩))) = z1 := by
    rw [heq_val]
  rw [hz1_def]
  -- c2: ctrlCopyReg eqF mk -> mk1
  rw [act_ctrlCopyRegOn arith
    (hCS := eEqFlag_disjoint_eMSlot as n K d _)
    (hCD := eEqFlag_disjoint_eMSlot as n K d _)
    (hSD := eMSlot_disjoint_slot as n K d (by simp [Fin.ext_iff]))]
  have hz1_eqF : z1 (eqF 0) = eqB := by simp [z1, updateOn_apply_emb]
  have hz1_mk : z1 ∘ mk = mBitsFn K l ⟨k, by omega⟩ := by
    rw [updateOn_comp_disjoint _ _ (eEqFlag_disjoint_eMSlot as n K d _)]
    funext b
    have hslot := congrFun hz0M (finProdFinEquiv (⟨k, by omega⟩, b))
    simpa [mk, eMSlot, flatReg, if_pos (Nat.lt_succ_self k)] using hslot
  have hz1_mk1 : z1 ∘ mk1 = fun _ => false := by
    rw [updateOn_comp_disjoint _ _ (eEqFlag_disjoint_eMSlot as n K d _)]
    funext b
    have hslot := congrFun hz0M (finProdFinEquiv (⟨k + 1, hk⟩, b))
    simpa [mk1, eMSlot, flatReg, if_neg (Nat.lt_irrefl (k + 1))] using hslot
  have hmk1_val : (if z1 (eqF 0) then fun j => xor (z1 (mk1 j)) (z1 (mk j)) else z1 ∘ mk1) =
      if eqB then mBitsFn K l ⟨k, by omega⟩ else fun _ => false := by
    rw [hz1_eqF]
    split_ifs with h
    · funext j
      have h0 : z1 (mk1 j) = false := congrFun hz1_mk1 j
      have hm : z1 (mk j) = mBitsFn K l ⟨k, by omega⟩ j := congrFun hz1_mk j
      rw [h0, hm, xor_false_left]
    · exact hz1_mk1
  set z2 := updateOn mk1 z1 (if eqB then mBitsFn K l ⟨k, by omega⟩ else fun _ => false)
  have hz2_def : updateOn mk1 z1 (if z1 (eqF 0) then fun j => xor (z1 (mk1 j)) (z1 (mk j)) else z1 ∘ mk1) = z2 := by
    rw [hmk1_val]
  rw [hz2_def]
  -- c3: setConst 1 1 on oneW
  rw [act_setConstOn arith]
  have hz2_oneW : z2 ∘ oneW = fun _ => false := by
    rw [updateOn_comp_disjoint _ _ (eMSlot_disjoint_eOne12 as n K d _)]
    rw [updateOn_comp_disjoint _ _ (eEqFlag_disjoint_eOne12 as n K d)]
    exact hz06
  have honeW_val : (fun i : Fin 1 => xor (z2 (oneW i)) (natToBits 1 1 i)) = fun _ => true := by
    funext i
    have hz2i : z2 (oneW i) = false := congrFun hz2_oneW i
    rw [hz2i, natToBits_one_one comb, xor_false_left]
  set z3 := updateOn oneW z2 (fun _ => true)
  have hz3_def : updateOn oneW z2 (fun i => xor (z2 (oneW i)) (natToBits 1 1 i)) = z3 := by
    rw [honeW_val]
  rw [hz3_def]
  -- c4: ctrlAddConst w 1 on oneW -> mk1
  have hz3_ancW1 : z3 ∘ eArith12Pref as n K d (wOf K + 1) (le_max_right _ _) = fun _ => false := by
    funext i
    rw [updateOn_comp_disjoint _ _ (eOne12_disjoint_eArith12 as n K d _ _)]
    rw [updateOn_comp_disjoint _ _ (eMSlot_disjoint_eArith12 as n K d _ _ _)]
    rw [updateOn_comp_disjoint _ _ (eEqFlag_disjoint_eArith12 as n K d _ _)]
    exact congrFun hz010 _
  rw [act_ctrlAddConstOn (arith := arith)
    (hCB := eOne12_disjoint_eMSlot as n K d _)
    (hCA := eOne12_disjoint_eArith12 as n K d _ _)
    (hBA := eMSlot_disjoint_eArith12 as n K d _ _ _)
    (z := z3) (hzAnc := hz3_ancW1)]
  have hz3_oneW0 : z3 (oneW 0) = true := by simp [z3, updateOn_apply_emb]
  have hz3_mk1 : z3 ∘ mk1 = if eqB then mBitsFn K l ⟨k, by omega⟩ else fun _ => false := by
    dsimp only [z3, oneW, mk1]
    rw [updateOn_comp_disjoint _ _ (eOne12_disjoint_eMSlot as n K d _)]
    exact updateOn_comp_emb _ _ _
  have hlt_pow : 1 < 2 ^ wOf K := by
    have := five_le_wOf h1K
    calc 1 < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ wOf K := Nat.pow_le_pow_right (by norm_num) this
  have hmk_lt_pow : runOffset l ⟨k, by omega⟩ < 2 ^ wOf K := by
    have h1 := comb.runOffset_le_N l ⟨k, by omega⟩
    have h2 := two_K_lt_B2 h1K
    have h3 := two_mul_B2_add_one_lt_two_pow_wOf h1K
    omega
  have hmk1_add : (if z3 (oneW 0) then natToBits (wOf K) (1 % 2 ^ wOf K + bitsToNat (z3 ∘ mk1)) else z3 ∘ mk1) =
      mBitsFn K l ⟨k + 1, hk⟩ := by
    rw [hz3_oneW0, if_pos rfl, Nat.mod_eq_of_lt hlt_pow, hz3_mk1]
    have hrun := comb.runOffset_succ l hl k hk
    dsimp [mBitsFn]
    rw [hrun]
    by_cases heq : l ⟨k, by omega⟩ = l ⟨k + 1, hk⟩
    · have heqB : eqB = true := by simp [eqB, heq]
      rw [if_pos heqB, if_pos heq, comb.bitsToNat_natToBits hmk_lt_pow, add_comm]
    · have heqB : eqB = false := by simp [eqB, heq]
      rw [if_neg (by simp [heqB]), if_neg heq]
      have hz0bits : bitsToNat (fun _ : Fin (wOf K) => false) = 0 := by simp [bitsToNat]
      rw [hz0bits, add_zero]
  set z4 := updateOn mk1 z3 (mBitsFn K l ⟨k + 1, hk⟩)
  have hz4_def : updateOn mk1 z3
      (if z3 (oneW 0) then natToBits (wOf K) (1 % 2 ^ wOf K + bitsToNat (z3 ∘ mk1)) else z3 ∘ mk1) = z4 := by
    rw [hmk1_add]
  rw [hz4_def]
  -- c5: setConst 1 1 on oneW -> back to false
  rw [act_setConstOn arith]
  have hz4_oneW : z4 ∘ oneW = fun _ => true := by
    dsimp only [z4, mk1, z3, oneW]
    rw [updateOn_comp_disjoint _ _ (eMSlot_disjoint_eOne12 as n K d _)]
    exact updateOn_comp_emb _ _ _
  have honeW_back : (fun i : Fin 1 => xor (z4 (oneW i)) (natToBits 1 1 i)) = fun _ => false := by
    funext i
    have hzi : z4 (oneW i) = true := congrFun hz4_oneW i
    rw [hzi, natToBits_one_one comb, xor_self_cancel]
  set z5 := updateOn oneW z4 (fun _ => false)
  have hz5_def : updateOn oneW z4 (fun i : Fin 1 => xor (z4 (oneW i)) (natToBits 1 1 i)) = z5 := by
    rw [honeW_back]
  rw [hz5_def]
  -- c6: eqReg -> uncompute eqF back to false
  have hz5_ancS : z5 ∘ eArith12Pref as n K d (sOf n) (le_max_left _ _) = fun _ => false := by
    funext i
    dsimp only [z5, z4, z3, z2, z1, oneW, mk1, eqF]
    rw [updateOn_comp_disjoint _ _ (eOne12_disjoint_eArith12 as n K d _ _)]
    rw [updateOn_comp_disjoint _ _ (eMSlot_disjoint_eArith12 as n K d _ _ _)]
    rw [updateOn_comp_disjoint _ _ (eOne12_disjoint_eArith12 as n K d _ _)]
    rw [updateOn_comp_disjoint _ _ (eMSlot_disjoint_eArith12 as n K d _ _ _)]
    rw [updateOn_comp_disjoint _ _ (eEqFlag_disjoint_eArith12 as n K d _ _)]
    exact congrFun hz010 _
  rw [act_eqRegOn (arith := arith)
    (hAB := eLSlot_disjoint_slot as n K d (by simp [Fin.ext_iff]))
    (hAO := eLSlot_disjoint_eEqFlag as n K d _)
    (hBO := eLSlot_disjoint_eEqFlag as n K d _)
    (hAA := eLSlot_disjoint_eArith12 as n K d _ _ _)
    (hBA := eLSlot_disjoint_eArith12 as n K d _ _ _)
    (hOA := eEqFlag_disjoint_eArith12 as n K d _ _)
    (z := z5) (hzAnc := hz5_ancS)]
  have h12L : ∀ (idx : Fin (2 * K)) a b, eOne12 as n K d a ≠ eLSlot as n K d idx b :=
    fun idx a b h => eLSlot_disjoint_ancPrefix as n K d idx ⟨6, by decide⟩ 1 _ b a h.symm
  have hz5_lk : z5 ∘ eLSlot as n K d ⟨k, by omega⟩ = particleSym54 n (sOf n) (l ⟨k, by omega⟩) := by
    dsimp only [z5, z4, z3, z2, z1, oneW, mk1, eqF]
    rw [updateOn_comp_disjoint _ _ (h12L ⟨k, by omega⟩)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eLSlot_disjoint_eMSlot as n K d ⟨k, by omega⟩ ⟨k + 1, hk⟩ b a h.symm)]
    rw [updateOn_comp_disjoint _ _ (h12L ⟨k, by omega⟩)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eLSlot_disjoint_eMSlot as n K d ⟨k, by omega⟩ ⟨k + 1, hk⟩ b a h.symm)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eLSlot_disjoint_eEqFlag as n K d ⟨k, by omega⟩ b a h.symm)]
    exact hlk
  have hz5_lk1 : z5 ∘ eLSlot as n K d ⟨k + 1, hk⟩ = particleSym54 n (sOf n) (l ⟨k + 1, hk⟩) := by
    dsimp only [z5, z4, z3, z2, z1, oneW, mk1, eqF]
    rw [updateOn_comp_disjoint _ _ (h12L ⟨k + 1, hk⟩)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eLSlot_disjoint_eMSlot as n K d ⟨k + 1, hk⟩ ⟨k + 1, hk⟩ b a h.symm)]
    rw [updateOn_comp_disjoint _ _ (h12L ⟨k + 1, hk⟩)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eLSlot_disjoint_eMSlot as n K d ⟨k + 1, hk⟩ ⟨k + 1, hk⟩ b a h.symm)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eLSlot_disjoint_eEqFlag as n K d ⟨k + 1, hk⟩ b a h.symm)]
    exact hlk1
  have hz5_eqF0 : z5 (eqF 0) = eqB := by
    have h4 : z5 ∘ eqF = z1 ∘ eqF := by
      dsimp only [z5, z4, z3, z2, oneW, mk1, eqF]
      rw [updateOn_comp_disjoint _ _ (fun a b h => eEqFlag_disjoint_eOne12 as n K d b a h.symm)]
      rw [updateOn_comp_disjoint _ _ (eMSlot_disjoint_eEqFlag as n K d _)]
      rw [updateOn_comp_disjoint _ _ (fun a b h => eEqFlag_disjoint_eOne12 as n K d b a h.symm)]
      rw [updateOn_comp_disjoint _ _ (eMSlot_disjoint_eEqFlag as n K d _)]
    exact (congrFun h4 0).trans hz1_eqF
  have heqF_back : (fun _ : Fin 1 => xor (z5 (eqF 0))
      (decide (z5 ∘ eLSlot as n K d ⟨k, by omega⟩ = z5 ∘ eLSlot as n K d ⟨k + 1, hk⟩))) = fun _ => false := by
    funext _
    rw [hz5_eqF0, hz5_lk, hz5_lk1]
    simp only [eqB, particleSym54_eq_iff comb, xor_self_cancel]
  set z6 := updateOn eqF z5 (fun _ => false)
  have hz6_def : updateOn eqF z5
      (fun _ : Fin 1 => xor (z5 (eqF 0))
        (decide (z5 ∘ eLSlot as n K d ⟨k, by omega⟩ = z5 ∘ eLSlot as n K d ⟨k + 1, hk⟩))) = z6 := by
    rw [heqF_back]
  rw [hz6_def]
  -- c7: ltConst w 2 on mk1 -> ak1
  have hz6_ancW : z6 ∘ eArith12Pref as n K d (wOf K)
      (Nat.le_trans (Nat.le_succ (wOf K)) (le_max_right _ _)) = fun _ => false := by
    funext i
    dsimp only [z6, z5, z4, oneW, mk1, eqF]
    rw [updateOn_comp_disjoint _ _ (eEqFlag_disjoint_eArith12 as n K d _ _)]
    rw [updateOn_comp_disjoint _ _ (eOne12_disjoint_eArith12 as n K d _ _)]
    rw [updateOn_comp_disjoint _ _ (eMSlot_disjoint_eArith12 as n K d _ _ _)]
    exact congrFun hz3_ancW1 ⟨i.1, Nat.lt_succ_of_lt i.isLt⟩
  rw [act_ltConstOn (arith := arith)
    (hIO := eMSlot_disjoint_eActSlot as n K d _ _)
    (hIA := eMSlot_disjoint_eArith12 as n K d _ _ _)
    (hOA := eActSlot_disjoint_eArith12 as n K d _ _ _)
    (z := z6) (hzAnc := hz6_ancW)]
  have hz6_mk1 : z6 ∘ mk1 = mBitsFn K l ⟨k + 1, hk⟩ := by
    dsimp only [z6, z5, z4, eqF, oneW, mk1]
    rw [updateOn_comp_disjoint _ _ (eEqFlag_disjoint_eMSlot as n K d _)]
    rw [updateOn_comp_disjoint _ _ (eOne12_disjoint_eMSlot as n K d _)]
    exact updateOn_comp_emb _ _ _
  have hz6_ak1 : z6 (ak1 0) = false := by
    have h0 : z6 ∘ ak1 = z0 ∘ ak1 := by
      dsimp only [z6, z5, z4, z3, z2, z1, eqF, oneW, mk1, ak1]
      rw [updateOn_comp_disjoint _ _ (fun a b h => eActSlot_disjoint_eEqFlag as n K d _ b a h.symm)]
      rw [updateOn_comp_disjoint _ _ (fun a b h => eActSlot_disjoint_eOne12 as n K d _ b a h.symm)]
      rw [updateOn_comp_disjoint _ _ (eMSlot_disjoint_eActSlot as n K d _ _)]
      rw [updateOn_comp_disjoint _ _ (fun a b h => eActSlot_disjoint_eOne12 as n K d _ b a h.symm)]
      rw [updateOn_comp_disjoint _ _ (eMSlot_disjoint_eActSlot as n K d _ _)]
      rw [updateOn_comp_disjoint _ _ (fun a b h => eActSlot_disjoint_eEqFlag as n K d _ b a h.symm)]
    have := congrFun hz0A (finProdFinEquiv (⟨k + 1, hk⟩, 0))
    simpa [ak1, eActSlot, flatReg, if_neg (Nat.lt_irrefl (k + 1))] using (congrFun h0 0).trans this
  have hmk1_lt_pow : runOffset l ⟨k + 1, hk⟩ < 2 ^ wOf K := by
    have h1 := comb.runOffset_le_N l ⟨k + 1, hk⟩
    have h2 := two_K_lt_B2 h1K
    have h3 := two_mul_B2_add_one_lt_two_pow_wOf h1K
    omega
  have hak1_lt : (fun _ : Fin 1 => xor (z6 (ak1 0)) (decide (bitsToNat (z6 ∘ mk1) < 2))) =
      fun _ => decide (runOffset l ⟨k + 1, hk⟩ < 2) := by
    funext _
    rw [hz6_ak1, xor_false_left, hz6_mk1, mBitsFn, comb.bitsToNat_natToBits hmk1_lt_pow]
  set z7 := updateOn ak1 z6 (fun _ => decide (runOffset l ⟨k + 1, hk⟩ < 2))
  have hz7_def : updateOn ak1 z6
      (fun _ : Fin 1 => xor (z6 (ak1 0)) (decide (bitsToNat (z6 ∘ mk1) < 2))) = z7 := by
    rw [hak1_lt]
  rw [hz7_def]
  -- c8: setConst 1 1 on ak1 -> actBitsFn K l ⟨k + 1, hk⟩
  rw [act_setConstOn arith]
  have hz7_ak1 : z7 ∘ ak1 = fun _ => decide (runOffset l ⟨k + 1, hk⟩ < 2) := by
    dsimp only [z7, ak1]; exact updateOn_comp_emb _ _ _
  have hak1_final : (fun i : Fin 1 => xor (z7 (ak1 i)) (natToBits 1 1 i)) =
      actBitsFn K l ⟨k + 1, hk⟩ := by
    funext i
    have hzi : z7 (ak1 i) = decide (runOffset l ⟨k + 1, hk⟩ < 2) := congrFun hz7_ak1 i
    rw [hzi, natToBits_one_one comb]
    dsimp [actBitsFn]
    by_cases hlt : runOffset l ⟨k + 1, hk⟩ < 2
    · simp [hlt, show ¬ 2 ≤ runOffset l ⟨k + 1, hk⟩ by omega]
    · simp [hlt, show 2 ≤ runOffset l ⟨k + 1, hk⟩ by omega]
  set z8 := updateOn ak1 z7 (actBitsFn K l ⟨k + 1, hk⟩)
  have hz8_def : updateOn ak1 z7 (fun i : Fin 1 => xor (z7 (ak1 i)) (natToBits 1 1 i)) = z8 := by
    rw [hak1_final]
  rw [hz8_def]
  congr 1
  dsimp [z8, z7, z6, z5, z4, z3, z2, z1]
  rw [updateOn_idem]
  rw [updateOn_comm eqF oneW (eEqFlag_disjoint_eOne12 as n K d)]
  rw [updateOn_comm eqF mk1 (eEqFlag_disjoint_eMSlot as n K d _)]
  rw [updateOn_comm eqF oneW (eEqFlag_disjoint_eOne12 as n K d)]
  rw [updateOn_comm eqF mk1 (eEqFlag_disjoint_eMSlot as n K d _)]
  rw [updateOn_idem, updateOn_noop eqF z0 _ hz05]
  rw [updateOn_comm oneW mk1 (eOne12_disjoint_eMSlot as n K d _)]
  rw [updateOn_idem]
  rw [updateOn_comm oneW mk1 (eOne12_disjoint_eMSlot as n K d _)]
  rw [updateOn_noop oneW z0 _ hz06]
  rw [updateOn_idem]
  dsimp only [z0, step1State]
  rw [updateOn_comm mk1 (eActReg as n K d) (eMSlot_disjoint_eActReg as n K d _)]
  change updateOn ((slotInReg (2 * K) 1 ⟨k + 1, hk⟩).trans (eActReg as n K d))
      (updateOn (eActReg as n K d)
        (updateOn ((slotInReg (2 * K) (wOf K) ⟨k + 1, hk⟩).trans (eMReg as n K d))
          (updateOn (eMReg as n K d) z _) _) _) _ = _
  rw [updateOn_slot_absorb (eMReg as n K d) z _ ⟨k + 1, hk⟩ (mBitsFn K l ⟨k + 1, hk⟩)]
  rw [updateOn_slot_absorb (eActReg as n K d) _ _ ⟨k + 1, hk⟩ (actBitsFn K l ⟨k + 1, hk⟩)]
  have hm_upd : (Function.update (fun i : Fin (2 * K) => if i.1 < k + 1 then mBitsFn K l i else fun _ => false)
      ⟨k + 1, hk⟩ (mBitsFn K l ⟨k + 1, hk⟩)) =
      fun i : Fin (2 * K) => if i.1 < k + 2 then mBitsFn K l i else fun _ => false := by
    funext i
    by_cases hi : i = ⟨k + 1, hk⟩
    · subst hi; simp
    · rw [Function.update_of_ne hi]
      have hval : i.1 ≠ k + 1 := fun hv => hi (Fin.ext hv)
      by_cases hlt : i.1 < k + 1
      · simp [hlt, Nat.lt_trans hlt (Nat.lt_succ_self _)]
      · simp [hlt, show ¬ i.1 < k + 2 by omega]
  have ha_upd : (Function.update (fun i : Fin (2 * K) => if i.1 < k + 1 then actBitsFn K l i else fun _ => false)
      ⟨k + 1, hk⟩ (actBitsFn K l ⟨k + 1, hk⟩)) =
      fun i : Fin (2 * K) => if i.1 < k + 2 then actBitsFn K l i else fun _ => false := by
    funext i
    by_cases hi : i = ⟨k + 1, hk⟩
    · subst hi; simp
    · rw [Function.update_of_ne hi]
      have hval : i.1 ≠ k + 1 := fun hv => hi (Fin.ext hv)
      by_cases hlt : i.1 < k + 1
      · simp [hlt, Nat.lt_trans hlt (Nat.lt_succ_self _)]
      · simp [hlt, show ¬ i.1 < k + 2 by omega]
  rw [hm_upd, ha_upd]

lemma step1Circ_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) :
    (step1Circ as arith n K d h1K).size ≤ wOf K + (2 * K - 1) * (28 * sOf n + 42 * wOf K + 28) := by
  dsimp [step1Circ]
  rw [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size]
  have hinit := arith.setConstMSBCircuit_size (wOf K) 1
  have hloop : (LayeredCircuit.seqList ((List.range (2 * K - 1)).map fun k =>
      if hk : k + 1 < 2 * K then step1StepCirc as arith n K d k hk else LayeredCircuit.id _)).size ≤
      (2 * K - 1) * (28 * sOf n + 42 * wOf K + 28) := by
    have := LayeredCircuit_seqList_size_le
      ((List.range (2 * K - 1)).map fun k =>
        if hk : k + 1 < 2 * K then step1StepCirc as arith n K d k hk else LayeredCircuit.id _)
      (28 * sOf n + 42 * wOf K + 28)
      (by
        intro lc hlc
        simp only [List.mem_map] at hlc
        rcases hlc with ⟨k, _, rfl⟩
        split_ifs with hk
        · exact step1StepCirc_size as arith n K d k hk
        · simp [LayeredCircuit.id, LayeredCircuit.size, LayeredCircuit.toCircuit])
    simpa [List.length_map, List.length_range] using this
  omega

lemma act_step1Circ (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (h1K : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l)
    (z : Qubits (totWiresDef as n K d))
    (hzL : z ∘ eL as n K d = flatReg (2 * K) (sOf n) fun p => particleSym54 n (sOf n) (l p))
    (hz0 : z ∘ eMReg as n K d = fun _ => false)
    (hz1 : z ∘ eActReg as n K d = fun _ => false)
    (hz5 : z ∘ ancEmb as n K d ⟨5, by decide⟩ = fun _ => false)
    (hz6 : z ∘ ancEmb as n K d ⟨6, by decide⟩ = fun _ => false)
    (hz10 : z ∘ ancEmb as n K d ⟨10, by decide⟩ = fun _ => false) :
    act (step1Circ as arith n K d h1K).unitary (ket z) =
      ket (updateOn (eActReg as n K d)
        (updateOn (eMReg as n K d) z (flatReg (2 * K) (wOf K) (mBitsFn K l)))
        (flatReg (2 * K) 1 (actBitsFn K l))) := by
  dsimp [step1Circ]
  rw [LayeredCircuit.seq_unitary, act_mul]
  rw [act_setConstOn arith]
  have hz0_zero : z ∘ eMSlot as n K d ⟨0, by omega⟩ = fun _ => false := by
    funext b; exact congrFun hz0 _
  have hm0 : (fun i : Fin (wOf K) => xor (z (eMSlot as n K d ⟨0, by omega⟩ i)) (natToBits (wOf K) 1 i)) =
      mBitsFn K l ⟨0, by omega⟩ := by
    funext i
    have hzi : z (eMSlot as n K d ⟨0, by omega⟩ i) = false := congrFun hz0_zero i
    rw [hzi, xor_false_left, mBitsFn, runOffset_zero_two_K h1K hl]
  have hz_m0 : updateOn (eMSlot as n K d ⟨0, by omega⟩) z
      (fun i => xor (z (eMSlot as n K d ⟨0, by omega⟩ i)) (natToBits (wOf K) 1 i)) =
      step1State as n K d l z 1 := by
    rw [hm0]
    dsimp only [step1State]
    have hzeroM : (fun _ : Fin (2 * K * wOf K) => false) =
        flatReg (2 * K) (wOf K) (fun _ _ => false) := by
      funext idx; simp [flatReg]
    have hnoopM : updateOn (eMReg as n K d) z (flatReg (2 * K) (wOf K) (fun _ _ => false)) = z :=
      updateOn_noop _ _ _ (hz0.trans hzeroM)
    have hnoopA : updateOn (eActReg as n K d)
        (updateOn (eMReg as n K d) z (flatReg (2 * K) (wOf K) fun i =>
          if i.1 < 1 then mBitsFn K l i else fun _ => false))
        (flatReg (2 * K) 1 fun i => if i.1 < 1 then actBitsFn K l i else fun _ => false) =
        updateOn (eMReg as n K d) z (flatReg (2 * K) (wOf K) fun i =>
          if i.1 < 1 then mBitsFn K l i else fun _ => false) := by
      apply updateOn_noop
      rw [updateOn_comp_disjoint _ _ (eMReg_disjoint_eActReg as n K d), hz1]
      funext idx
      rcases finProdFinEquiv.surjective idx with ⟨⟨i, b⟩, rfl⟩
      simp only [flatReg, Equiv.symm_apply_apply]
      by_cases hi : i.1 < 1
      · have hi_eq : i = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
        have hrun0 : runOffset l i = 1 := by rw [hi_eq]; exact runOffset_zero_two_K h1K hl
        rw [if_pos hi]; simp [actBitsFn, hrun0]
      · simp [hi]
    rw [hnoopA]
    have hm_fn : (fun i : Fin (2 * K) => if i.1 < 1 then mBitsFn K l i else fun _ => false) =
        Function.update (fun _ _ => false) ⟨0, by omega⟩ (mBitsFn K l ⟨0, by omega⟩) := by
      funext i
      by_cases hi : i = ⟨0, by omega⟩
      · subst hi; simp
      · rw [Function.update_of_ne hi]
        have hne0 : ¬ i.1 < 1 := by intro h; exact hi (Fin.ext (by dsimp; omega))
        simp [hne0]
    rw [hm_fn, ← updateOn_slot_absorb]
    change updateOn (eMSlot as n K d ⟨0, by omega⟩) z (mBitsFn K l ⟨0, by omega⟩) =
      updateOn (eMSlot as n K d ⟨0, by omega⟩) (updateOn (eMReg as n K d) z (flatReg (2 * K) (wOf K) fun _ _ => false))
        (mBitsFn K l ⟨0, by omega⟩)
    rw [hnoopM]
  rw [hz_m0]
  have hloop := act_seqList_range
    (fun k => step1State as n K d l z (k + 1))
    (fun k => if hk : k + 1 < 2 * K then step1StepCirc as arith n K d k hk else LayeredCircuit.id _)
    (2 * K - 1)
    (fun k hk => by
      have hk' : k + 1 < 2 * K := by omega
      rw [dif_pos hk']
      exact act_step1StepCirc comb as arith n K d h1K l hl z hzL hz5 hz6 hz10 k hk')
  have heq_last : 2 * K - 1 + 1 = 2 * K := by omega
  rw [heq_last] at hloop
  rw [hloop]
  congr 1
  dsimp only [step1State]
  have hm_all : (fun i : Fin (2 * K) => if i.1 < 2 * K then mBitsFn K l i else fun _ => false) =
      mBitsFn K l := funext fun i => if_pos i.isLt
  have ha_all : (fun i : Fin (2 * K) => if i.1 < 2 * K then actBitsFn K l i else fun _ => false) =
      actBitsFn K l := funext fun i => if_pos i.isLt
  rw [hm_all, ha_all]

lemma packRec1SlotCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (q : ℕ) (hq : q < arity (dOccOf K)) :
    (packRec1SlotCirc as arith n K d q hq).size ≤ 2 * wOf K + 2 := by
  dsimp [packRec1SlotCirc]
  split_ifs
  · simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, LayeredCircuit.mapWires_size]
    have h1 := arith.copyRegCircuit_size 1
    have h2 := arith.setConstMSBCircuit_size 1 1
    have h3 := arith.copyRegCircuit_size (wOf K)
    have h4 := arith.setConstMSBCircuit_size (wOf K) q
    omega
  · simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, LayeredCircuit.mapWires_size]
    have h1 := arith.setConstMSBCircuit_size 1 1
    have h2 := arith.setConstMSBCircuit_size (wOf K) 1
    have h3 := arith.setConstMSBCircuit_size (wOf K) q
    omega

lemma act_packRec1SlotCirc (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) {l : Fin (2 * K) → Fin (n + 1)} (z : Qubits (totWiresDef as n K d))
    (arr : Fin (arity (dOccOf K)) → Qubits (wR1Occ K))
    (hzAct : z ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l))
    (hzM : z ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l))
    (hzRec : z ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) arr)
    (q : ℕ) (hq : q < arity (dOccOf K))
    (hq0 : arr ⟨q, hq⟩ = fun _ => false) :
    act (packRec1SlotCirc as arith n K d q hq).unitary (ket z) =
      ket (updateOn (eRec1Reg as n K d) z
        (flatReg (arity (dOccOf K)) (wR1Occ K) (Function.update arr ⟨q, hq⟩ (rec1InitArr K l ⟨q, hq⟩)))) := by
  let qF : Fin (arity (dOccOf K)) := ⟨q, hq⟩
  have hslot_zero : arr qF = rec1SlotFn (wOf K) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) :=
    hq0.trans (rec1SlotFn_zero (wOf K)).symm
  have hz_slot : z ∘ ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF =
      rec1SlotFn (wOf K) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) := by
    rw [comp_ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) z arr hzRec qF,
      hslot_zero]
  dsimp only [packRec1SlotCirc]
  split_ifs with hq2
  · simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul,
      LayeredCircuit.id_unitary, act_one]
    -- c1: copy eActSlot -> eRec1NotAct
    rw [act_copyRegOn arith (hSD := eActSlot_disjoint_eRec1NotAct as n K d _ _)]
    have hz_na : z ∘ eRec1NotAct as n K d qF = fun _ => false := by
      have h := comp_ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
        z arr hzRec qF 0 1 (by dsimp [wR1Occ, wK1Occ]; omega)
      change z ∘ eRec1NotAct as n K d qF = _ at h
      rw [h, hq0]; rfl
    have hz_act : z ∘ eActSlot as n K d ⟨q, hq2⟩ = actBitsFn K l ⟨q, hq2⟩ := by
      funext b
      have h := congrFun hzAct (finProdFinEquiv (⟨q, hq2⟩, b))
      simpa [eActSlot, flatReg, Function.comp_apply] using h
    have hv1 : (fun j => xor (z (eRec1NotAct as n K d qF j)) (z (eActSlot as n K d ⟨q, hq2⟩ j))) =
        actBitsFn K l ⟨q, hq2⟩ := by
      funext j
      have h1 : z (eRec1NotAct as n K d qF j) = false := congrFun hz_na j
      have h2 : z (eActSlot as n K d ⟨q, hq2⟩ j) = actBitsFn K l ⟨q, hq2⟩ j := congrFun hz_act j
      rw [h1, h2, xor_false_left]
    rw [hv1]
    set z1 := updateOn (eRec1NotAct as n K d qF) z (actBitsFn K l ⟨q, hq2⟩)
    -- c2: setConst 1 1 on eRec1NotAct
    rw [act_setConstOn arith]
    have hz1_na : z1 ∘ eRec1NotAct as n K d qF = actBitsFn K l ⟨q, hq2⟩ := updateOn_comp_emb _ _ _
    let naVal : Qubits 1 := fun _ => !(actBitsFn K l ⟨q, hq2⟩ 0)
    have hv2 : (fun i => xor (z1 (eRec1NotAct as n K d qF i)) (natToBits 1 1 i)) = naVal := by
      funext i
      have hi0 : i = 0 := Fin.ext (by omega); subst hi0
      have hzi : z1 (eRec1NotAct as n K d qF 0) = actBitsFn K l ⟨q, hq2⟩ 0 := congrFun hz1_na 0
      rw [hzi, natToBits_one_one comb]
      dsimp [naVal]
      cases actBitsFn K l ⟨q, hq2⟩ 0 <;> rfl
    rw [hv2]
    set z2 := updateOn (eRec1NotAct as n K d qF) z1 naVal
    have hz2_slot : z2 = updateOn (ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) z
        (rec1SlotFn (wOf K) naVal (fun _ => false) (fun _ => false) (fun _ => false)) := by
      dsimp only [z2, z1]
      rw [updateOn_idem]
      change updateOn (ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF
        0 1 _) z naVal = _
      rw [updateOn_ancRegField_eq_slot, hz_slot, updateOn_rec1SlotFn_0]
    -- c3: copy eMSlot -> eRec1M
    rw [act_copyRegOn arith (hSD := eMSlot_disjoint_eRec1M as n K d _ _)]
    have hz2_m : z2 ∘ eMSlot as n K d ⟨q, hq2⟩ = mBitsFn K l ⟨q, hq2⟩ := by
      dsimp only [z2, z1]; rw [updateOn_idem]
      rw [updateOn_comp_disjoint _ _ (eRec1NotAct_disjoint_eMSlot as n K d _ _)]
      funext b
      have h := congrFun hzM (finProdFinEquiv (⟨q, hq2⟩, b))
      simpa [eMSlot, flatReg, Function.comp_apply] using h
    have hz2_recM : z2 ∘ eRec1M as n K d qF = fun _ => false := by
      rw [hz2_slot]
      change (updateOn (ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) z
        (rec1SlotFn (wOf K) naVal (fun _ => false) (fun _ => false) (fun _ => false)) ∘
        ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) ∘
        sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) = _
      rw [updateOn_comp_emb, rec1SlotFn_comp_1]
    have hv3 : (fun j => xor (z2 (eRec1M as n K d qF j)) (z2 (eMSlot as n K d ⟨q, hq2⟩ j))) =
        mBitsFn K l ⟨q, hq2⟩ := by
      funext j
      have h1 : z2 (eRec1M as n K d qF j) = false := congrFun hz2_recM j
      have h2 : z2 (eMSlot as n K d ⟨q, hq2⟩ j) = mBitsFn K l ⟨q, hq2⟩ j := congrFun hz2_m j
      rw [h1, h2, xor_false_left]
    rw [hv3]
    set z3 := updateOn (eRec1M as n K d qF) z2 (mBitsFn K l ⟨q, hq2⟩)
    have hz3_slot : z3 = updateOn (ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) z
        (rec1SlotFn (wOf K) naVal (mBitsFn K l ⟨q, hq2⟩) (fun _ => false) (fun _ => false)) := by
      dsimp only [z3]
      rw [hz2_slot]
      change updateOn (ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF
        1 (wOf K) _) _ _ = _
      rw [updateOn_ancRegField_eq_slot, updateOn_comp_emb, updateOn_idem, updateOn_rec1SlotFn_1]
    -- c4: setConst q on eRec1Idx
    rw [act_setConstOn arith]
    have hz3_idx : z3 ∘ eRec1Idx as n K d qF = fun _ => false := by
      rw [hz3_slot]
      change (updateOn (ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) z
        (rec1SlotFn (wOf K) naVal (mBitsFn K l ⟨q, hq2⟩) (fun _ => false) (fun _ => false)) ∘
        ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) ∘
        sliceEmb (1 + wOf K) (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) = _
      rw [updateOn_comp_emb, rec1SlotFn_comp_2]
    have hv4 : (fun i => xor (z3 (eRec1Idx as n K d qF i)) (natToBits (wOf K) q i)) =
        natToBits (wOf K) q := by
      funext i
      have h1 : z3 (eRec1Idx as n K d qF i) = false := congrFun hz3_idx i
      rw [h1, xor_false_left]
    rw [hv4]
    congr 1
    rw [hz3_slot]
    change updateOn (ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF
      (1 + wOf K) (wOf K) _) _ _ = _
    rw [updateOn_ancRegField_eq_slot, updateOn_comp_emb, updateOn_idem, updateOn_rec1SlotFn_2]
    have hfin := updateOn_ancRegSlot_eq as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
      z arr hzRec qF (rec1InitArr K l qF)
    have hval : rec1SlotFn (wOf K) naVal (mBitsFn K l ⟨q, hq2⟩) (natToBits (wOf K) q) (fun _ => false) =
        rec1InitArr K l qF := by
      dsimp [rec1InitArr, naVal, qF]; rw [dif_pos hq2]
    rw [hval]
    exact hfin
  · simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul,
      LayeredCircuit.id_unitary, act_one]
    -- c1: setConst 1 1 on eRec1NotAct
    rw [act_setConstOn arith]
    have hz_na : z ∘ eRec1NotAct as n K d qF = fun _ => false := by
      have h := comp_ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
        z arr hzRec qF 0 1 (by dsimp [wR1Occ, wK1Occ]; omega)
      change z ∘ eRec1NotAct as n K d qF = _ at h
      rw [h, hq0]; rfl
    have hv1 : (fun i => xor (z (eRec1NotAct as n K d qF i)) (natToBits 1 1 i)) = fun _ => true := by
      funext i
      have h1 : z (eRec1NotAct as n K d qF i) = false := congrFun hz_na i
      rw [h1, natToBits_one_one comb, xor_false_left]
    rw [hv1]
    set z1 := updateOn (eRec1NotAct as n K d qF) z (fun _ => true)
    have hz1_slot : z1 = updateOn (ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) z
        (rec1SlotFn (wOf K) (fun _ => true) (fun _ => false) (fun _ => false) (fun _ => false)) := by
      dsimp only [z1]
      change updateOn (ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF
        0 1 _) z _ = _
      rw [updateOn_ancRegField_eq_slot, hz_slot, updateOn_rec1SlotFn_0]
    -- c2: setConst 1 on eRec1M
    rw [act_setConstOn arith]
    have hz1_m : z1 ∘ eRec1M as n K d qF = fun _ => false := by
      rw [hz1_slot]
      change (updateOn (ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) z
        (rec1SlotFn (wOf K) (fun _ => true) (fun _ => false) (fun _ => false) (fun _ => false)) ∘
        ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) ∘
        sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) = _
      rw [updateOn_comp_emb, rec1SlotFn_comp_1]
    have hv2 : (fun i => xor (z1 (eRec1M as n K d qF i)) (natToBits (wOf K) 1 i)) = natToBits (wOf K) 1 := by
      funext i
      have h1 : z1 (eRec1M as n K d qF i) = false := congrFun hz1_m i
      rw [h1, xor_false_left]
    rw [hv2]
    set z2 := updateOn (eRec1M as n K d qF) z1 (natToBits (wOf K) 1)
    have hz2_slot : z2 = updateOn (ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) z
        (rec1SlotFn (wOf K) (fun _ => true) (natToBits (wOf K) 1) (fun _ => false) (fun _ => false)) := by
      dsimp only [z2]; rw [hz1_slot]
      change updateOn (ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF
        1 (wOf K) _) _ _ = _
      rw [updateOn_ancRegField_eq_slot, updateOn_comp_emb, updateOn_idem, updateOn_rec1SlotFn_1]
    -- c3: setConst q on eRec1Idx
    rw [act_setConstOn arith]
    have hz2_idx : z2 ∘ eRec1Idx as n K d qF = fun _ => false := by
      rw [hz2_slot]
      change (updateOn (ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) z
        (rec1SlotFn (wOf K) (fun _ => true) (natToBits (wOf K) 1) (fun _ => false) (fun _ => false)) ∘
        ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF) ∘
        sliceEmb (1 + wOf K) (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) = _
      rw [updateOn_comp_emb, rec1SlotFn_comp_2]
    have hv3 : (fun i => xor (z2 (eRec1Idx as n K d qF i)) (natToBits (wOf K) q i)) = natToBits (wOf K) q := by
      funext i
      have h1 : z2 (eRec1Idx as n K d qF i) = false := congrFun hz2_idx i
      rw [h1, xor_false_left]
    rw [hv3]
    congr 1
    rw [hz2_slot]
    change updateOn (ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF
      (1 + wOf K) (wOf K) _) _ _ = _
    rw [updateOn_ancRegField_eq_slot, updateOn_comp_emb, updateOn_idem, updateOn_rec1SlotFn_2]
    have hfin := updateOn_ancRegSlot_eq as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
      z arr hzRec qF (rec1InitArr K l qF)
    have hval : rec1SlotFn (wOf K) (fun _ => true) (natToBits (wOf K) 1) (natToBits (wOf K) q) (fun _ => false) =
        rec1InitArr K l qF := by
      dsimp [rec1InitArr, qF]; rw [dif_neg hq2]
    rw [hval]
    exact hfin

lemma packRec1Circ_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) :
    (packRec1Circ as arith n K d).size ≤ arity (dOccOf K) * (2 * wOf K + 2) := by
  dsimp [packRec1Circ]
  have h := LayeredCircuit_seqList_size_le
    ((List.range (arity (dOccOf K))).map fun q =>
      if hq : q < arity (dOccOf K) then packRec1SlotCirc as arith n K d q hq else LayeredCircuit.id _)
    (2 * wOf K + 2)
    (by
      intro lc hlc
      simp only [List.mem_map] at hlc
      rcases hlc with ⟨q, _, rfl⟩
      split_ifs with hq
      · exact packRec1SlotCirc_size as arith n K d q hq
      · simp)
  simpa using h

lemma act_packRec1Circ (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) {l : Fin (2 * K) → Fin (n + 1)} (z : Qubits (totWiresDef as n K d))
    (hzAct : z ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l))
    (hzM : z ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l))
    (hzRec : z ∘ ancEmb as n K d ⟨3, by decide⟩ = fun _ => false) :
    act (packRec1Circ as arith n K d).unitary (ket z) =
      ket (updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1InitArr K l))) := by
  let arrP (p : ℕ) (q : Fin (arity (dOccOf K))) : Qubits (wR1Occ K) :=
    if q.1 < p then rec1InitArr K l q else fun _ => false
  let st (p : ℕ) : Qubits (totWiresDef as n K d) :=
    updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (arrP p))
  have h0 : st 0 = z := by
    apply updateOn_noop
    funext idx
    rcases finProdFinEquiv.surjective idx with ⟨⟨q, b⟩, rfl⟩
    have hzr : z (eRec1Reg as n K d (finProdFinEquiv (q, b))) = false := congrFun hzRec _
    simp [hzr, arrP, flatReg]
  conv_lhs => rw [← h0]
  dsimp [packRec1Circ]
  have hloop := act_seqList_range st
    (fun q => if hq : q < arity (dOccOf K) then packRec1SlotCirc as arith n K d q hq else LayeredCircuit.id _)
    (arity (dOccOf K))
    (fun q hq => by
      rw [dif_pos hq]
      have hzA' : st q ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l) := by
        dsimp only [st]
        rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_eActReg as n K d)]
        exact hzAct
      have hzM' : st q ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l) := by
        dsimp only [st]
        rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_eMReg as n K d)]
        exact hzM
      have hzR' : st q ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (arrP q) :=
        updateOn_comp_emb _ _ _
      have hq0 : arrP q ⟨q, hq⟩ = fun _ => false := by dsimp [arrP]; simp
      have hs := act_packRec1SlotCirc comb as arith n K d (st q) (arrP q) hzA' hzM' hzR' q hq hq0
      rw [hs]
      congr 1
      dsimp only [st]
      rw [updateOn_idem]
      congr 1; congr 1; funext r
      by_cases hr : r = ⟨q, hq⟩
      · subst hr; simp [arrP]
      · rw [Function.update_of_ne hr]
        have hne : r.1 ≠ q := fun hv => hr (Fin.ext hv)
        by_cases hlt : r.1 < q
        · simp [arrP, hlt, Nat.lt_trans hlt (Nat.lt_succ_self _)]
        · simp [arrP, hlt, show ¬ r.1 < q + 1 by omega])
  rw [hloop]
  dsimp only [st]
  have harr_all : arrP (arity (dOccOf K)) = rec1InitArr K l := funext fun q => by
    dsimp only [arrP]; rw [if_pos q.isLt]
  rw [harr_all]

/-! #### 6.8 Sorting `eRec1Reg` (`sortRec1Circ`) & Matching `occSortedList` -/

lemma sortRec1Circ_size (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ) :
    ((sortRec1Circ as br n K d).size : ℝ) ≤
      br.C_sort * (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1) := by
  dsimp [sortRec1Circ, LayeredCircuit.mapWires_size]
  rw [LayeredCircuit.mapWires_size]
  simpa [wR1Occ, add_assoc] using br.bitonicSortKeyCircuit_size (dOccOf K) (wK1Occ K) (wP1Occ K) true

lemma act_sortRec1Circ (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ)
    {l : Fin (2 * K) → Fin (n + 1)} (z : Qubits (totWiresDef as n K d))
    (hzRec : z ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (rec1InitArr K l))
    (hzTr : z ∘ ancEmb as n K d ⟨4, by decide⟩ = fun _ => false)
    (hzAnc : z ∘ ancEmb as n K d ⟨7, by decide⟩ = fun _ => false) :
    act (sortRec1Circ as br n K d).unitary (ket z) =
      ket (updateOn (eTr1 as n K d)
        (updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1SortedArr K l)))
        (rec1SortTr K l)) := by
  dsimp only [sortRec1Circ]
  have htr : z ∘ eTr1 as n K d = fun _ => false := funext fun j => congrFun hzTr _
  have hanc : z ∘ eSort1Anc as n K d = fun _ => false := funext fun k => congrFun hzAnc _
  have hcomp := comp_packDTA54Emb (eRec1Reg as n K d) (eTr1 as n K d) (eSort1Anc as n K d)
    (eRec1Reg_disjoint_eTr1 as n K d)
    (eRec1Reg_disjoint_eSort1Anc as n K d)
    (eTr1_disjoint_eSort1Anc as n K d)
    z (rec1InitArr K l) (fun _ => false) hzRec htr hanc
  have hact := act_mapWires_ket_singleton _ _ z _ (by
    rw [hcomp]
    exact br.act_bitonicSortKeyCircuit_ket (dOccOf K) (wK1Occ K) (wP1Occ K) true (rec1InitArr K l))
  rw [hact]
  congr 1
  exact updateOn_packDTA54_eq_two (eRec1Reg as n K d) (eTr1 as n K d) (eSort1Anc as n K d)
    (eRec1Reg_disjoint_eTr1 as n K d) (eRec1Reg_disjoint_eSort1Anc as n K d)
    (eTr1_disjoint_eSort1Anc as n K d) z hanc (rec1SortedArr K l) (rec1SortTr K l)

-- Pure correspondence between `rec1SortedArr` and `occSortedList`
lemma occSortedList_length {α : Type*} [LinearOrder α] (N : ℕ) (l : Fin N → α) :
    (occSortedList N l).length = N := by
  dsimp [occSortedList]
  have hp := List.mergeSort_perm ((List.finRange N).map fun i => (decide (2 ≤ runOffset l i), runOffset l i, i))
    (fun x y => decide (occSortKey x ≤ occSortKey y))
  rw [hp.length_eq, List.length_map, List.length_finRange]

lemma occSortedList_mem_fields {α : Type*} [LinearOrder α] {N : ℕ} {l : Fin N → α}
    {r : Bool × ℕ × Fin N} (hr : r ∈ occSortedList N l) :
    r.1 = decide (2 ≤ runOffset l r.2.2) ∧ r.2.1 = runOffset l r.2.2 := by
  dsimp [occSortedList] at hr
  have hp := List.mergeSort_perm ((List.finRange N).map fun i => (decide (2 ≤ runOffset l i), runOffset l i, i))
    (fun x y => decide (occSortKey x ≤ occSortKey y))
  rw [hp.mem_iff, List.mem_map] at hr
  rcases hr with ⟨i, _, rfl⟩
  exact ⟨rfl, rfl⟩

lemma rec1SortedArr_eq_occSpec (comb : LcgSym54Comb) (br : BitonicRouting54) {n K : ℕ} (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) :
    let N1 := arity (dOccOf K)
    let L_occ := occSortedList (2 * K) l
    ∀ p : Fin N1,
      rec1SortedArr K l p =
        if hp : p.1 < 2 * K then
          rec1InitArr K l ⟨(L_occ[p.1]'(by rw [occSortedList_length]; exact hp)).2.2.1,
            by have := two_K_le_arity_dOcc (K := K); omega⟩
        else
          rec1InitArr K l p := by
  intro N1 L_occ
  have h2KN1 : 2 * K ≤ N1 := two_K_le_arity_dOcc
  have hL_len : L_occ.length = 2 * K := occSortedList_length (2 * K) l
  have hN1pow : N1 < 2 ^ wOf K := by
    have ha := arity_dOcc_lt_four_K h1K
    have hb := two_K_lt_B2 h1K
    have hc := two_mul_B2_add_one_lt_two_pow_wOf h1K
    omega
  have hm_lt : ∀ i : Fin (2 * K), runOffset l i < 2 ^ wOf K := fun i => by
    have h1 := comb.runOffset_le_N l i
    omega
  have h1_lt : 1 < 2 ^ wOf K := by
    have := five_le_wOf h1K
    calc 1 < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ wOf K := Nat.pow_le_pow_right (by norm_num) this
  let key : Qubits (wR1Occ K) → ℕ := fun r => bitsToNat (recKey54 r)
  let raw : List (Bool × ℕ × Fin (2 * K)) :=
    (List.finRange (2 * K)).map fun i => (decide (2 ≤ runOffset l i), runOffset l i, i)
  let specArr (p : Fin N1) : Qubits (wR1Occ K) :=
    if hp : p.1 < 2 * K then
      rec1InitArr K l ⟨(L_occ[p.1]'(by rw [occSortedList_length]; exact hp)).2.2.1, by omega⟩
    else rec1InitArr K l p
  let L₁ : List (Qubits (wR1Occ K)) := List.ofFn (rec1SortedArr K l)
  let L₂ : List (Qubits (wR1Occ K)) :=
    L_occ.map (fun r => rec1InitArr K l ⟨r.2.2.1, by omega⟩) ++
    (List.finRange (N1 - 2 * K)).map (fun j => rec1InitArr K l ⟨2 * K + j.1, by omega⟩)
  have hL₂_eq : L₂ = List.ofFn specArr := by
    apply List.ext_getElem
    · simp only [L₂, List.length_append, List.length_map, hL_len,
        List.length_finRange, List.length_ofFn]
      omega
    · intro idx hidx1 hidx2
      rw [List.length_ofFn] at hidx2
      dsimp only [L₂, specArr]
      by_cases hlt : idx < 2 * K
      · rw [List.getElem_append_left (by simp only [List.length_map, hL_len, hlt]),
          List.getElem_map, List.getElem_ofFn, dif_pos hlt]
      · rw [List.getElem_append_right (by simp only [List.length_map, hL_len]; omega),
          List.getElem_map, List.getElem_finRange, List.getElem_ofFn, dif_neg hlt]
        simp only [List.length_map, hL_len]
        congr 1; apply Fin.ext; dsimp; omega
  have hofFn_init : List.ofFn (rec1InitArr K l) =
      raw.map (fun r => rec1InitArr K l ⟨r.2.2.1, by omega⟩) ++
      (List.finRange (N1 - 2 * K)).map (fun j => rec1InitArr K l ⟨2 * K + j.1, by omega⟩) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_append, List.length_map, raw,
        List.length_finRange]
      omega
    · intro idx hidx1 hidx2
      rw [List.length_ofFn] at hidx1
      rw [List.getElem_ofFn]
      by_cases hlt : idx < 2 * K
      · rw [List.getElem_append_left (by simp [raw, hlt]), List.getElem_map]
        dsimp [raw]
        simp only [List.getElem_map, List.getElem_finRange]
        rfl
      · rw [List.getElem_append_right (by simp [raw]; omega), List.getElem_map, List.getElem_finRange]
        simp only [raw, List.length_map, List.length_finRange]
        congr 1; apply Fin.ext; dsimp; omega
  have hperm_occ : L_occ.Perm raw := by
    dsimp [L_occ, occSortedList, raw]
    exact List.mergeSort_perm _ _
  have hperm12 : L₁.Perm L₂ := by
    have hp1 : L₁.Perm (List.ofFn (rec1InitArr K l)) := br.sort_perm key (dOccOf K) true (rec1InitArr K l)
    rw [hofFn_init] at hp1
    exact hp1.trans ((hperm_occ.symm.map _).append_right _)
  have hp1 : L₁.Pairwise (fun x y => key x ≤ key y) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_ofFn] at hi hj
    simp only [L₁, List.getElem_ofFn]
    exact br.monotone_sort key (dOccOf K) (rec1InitArr K l) (Nat.le_of_lt hij)
  have hocc_pw : L_occ.Pairwise (fun a b => occSortKey a ≤ occSortKey b) := by
    have hpw : L_occ.Pairwise (fun a b => decide (occSortKey a ≤ occSortKey b) = true) := by
      dsimp [L_occ, occSortedList]
      exact List.pairwise_mergeSort
        (fun a b c => by simp only [decide_eq_true_eq]; exact le_trans)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
        raw
    exact hpw.imp (fun {a b} h => decide_eq_true_eq.mp h)
  have hkey_lt_of_mem : ∀ r ∈ L_occ,
      key (rec1InitArr K l ⟨r.2.2.1, by omega⟩) =
        bitsToNat (rec1KeyBits (wOf K) (!r.1) r.2.1 r.2.2.1) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := occSortedList_mem_fields hr
    dsimp [key]
    rw [rec1InitArr_lt_key K l _ r.2.2.isLt, hr1, hr2]
  have hp2 : L₂.Pairwise (fun x y => key x ≤ key y) := by
    dsimp [L₂]
    refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [List.length_map] at hi hj
      simp only [List.getElem_map]
      have ha := List.getElem_mem hi
      have hb := List.getElem_mem hj
      rw [hkey_lt_of_mem _ ha, hkey_lt_of_mem _ hb]
      obtain ⟨ha1, ha2⟩ := occSortedList_mem_fields ha
      obtain ⟨hb1, hb2⟩ := occSortedList_mem_fields hb
      have hma : L_occ[i].2.1 < 2 ^ wOf K := by rw [ha2]; exact hm_lt _
      have hmb : L_occ[j].2.1 < 2 ^ wOf K := by rw [hb2]; exact hm_lt _
      rw [rec1KeyBits_le_iff comb _ _ _ hma hmb (by omega) (by omega)]
      have hab := List.pairwise_iff_getElem.mp hocc_pw i j hi hj hij
      dsimp [occSortKey] at hab
      cases h1 : L_occ[i].1 <;> cases h2 : L_occ[j].1 <;> simpa [h1, h2] using hab
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      rw [List.length_map, List.length_finRange] at hi hj
      simp only [List.getElem_map, List.getElem_finRange]
      let qi : Fin N1 := ⟨2 * K + i, by omega⟩
      let qj : Fin N1 := ⟨2 * K + j, by omega⟩
      change bitsToNat (recKey54 (rec1InitArr K l qi)) ≤ bitsToNat (recKey54 (rec1InitArr K l qj))
      rw [rec1InitArr_ge_key K l qi (by dsimp [qi]; omega),
        rec1InitArr_ge_key K l qj (by dsimp [qj]; omega),
        rec1KeyBits_le_iff comb _ _ _ h1_lt h1_lt (by dsimp [qi]; omega) (by dsimp [qj]; omega)]
      simp [Prod.Lex.le_iff, qi, qj]
      omega
    · intro x hx y hy
      simp only [List.mem_map] at hx hy
      rcases hx with ⟨r, hr, rfl⟩
      rcases hy with ⟨j, _, rfl⟩
      have h1 : key (rec1InitArr K l ⟨r.2.2.1, by omega⟩) =
          bitsToNat (rec1KeyBits (wOf K) (!r.1) r.2.1 r.2.2.1) := hkey_lt_of_mem r hr
      let qj : Fin N1 := ⟨2 * K + j.1, by omega⟩
      have h2 : key (rec1InitArr K l qj) =
          bitsToNat (rec1KeyBits (wOf K) true 1 qj.1) :=
        congrArg bitsToNat (rec1InitArr_ge_key K l qj (by dsimp [qj]; omega))
      change key (rec1InitArr K l ⟨r.2.2.1, by omega⟩) ≤ key (rec1InitArr K l qj)
      rw [h1, h2]
      obtain ⟨hr1, hr2⟩ := occSortedList_mem_fields hr
      have hrm_lt : r.2.1 < 2 ^ wOf K := by rw [hr2]; exact hm_lt r.2.2
      rw [rec1KeyBits_le_iff comb _ _ _ hrm_lt h1_lt (by omega) (by dsimp [qj]; omega)]
      by_cases hact : r.1 = true
      · simp [hact, Prod.Lex.le_iff]
      · have hr_false : r.1 = false := Bool.eq_false_iff.mpr hact
        have hrun1 : r.2.1 = 1 := by
          have h1pos := comb.runOffset_pos l r.2.2
          have hnot2 : ¬ 2 ≤ runOffset l r.2.2 := by
            intro h2; exact hact (by rw [hr1]; exact decide_eq_true h2)
          rw [hr2]; omega
        dsimp [qj]
        simp [hr_false, hrun1, Prod.Lex.le_iff]
        omega
  have hinj : ∀ x ∈ L₂, ∀ y ∈ L₂, key x = key y → x = y := by
    have hmem_L₂ : ∀ z ∈ L₂, ∃ q : Fin N1, z = rec1InitArr K l q := by
      intro z hz
      simp only [L₂, List.mem_append, List.mem_map] at hz
      rcases hz with ⟨r, _, rfl⟩ | ⟨j, _, rfl⟩
      · exact ⟨⟨r.2.2.1, by omega⟩, rfl⟩
      · exact ⟨⟨2 * K + j.1, by omega⟩, rfl⟩
    intro x hx y hy hxy
    rcases hmem_L₂ x hx with ⟨qx, rfl⟩
    rcases hmem_L₂ y hy with ⟨qy, rfl⟩
    congr 1
    by_cases hqx : qx.1 < 2 * K <;> by_cases hqy : qy.1 < 2 * K
    · dsimp [key] at hxy
      rw [rec1InitArr_lt_key K l qx hqx, rec1InitArr_lt_key K l qy hqy,
        rec1KeyBits_eq_iff comb _ _ _ (hm_lt _) (hm_lt _) (by omega) (by omega)] at hxy
      exact Fin.ext hxy.2.2
    · dsimp [key] at hxy
      rw [rec1InitArr_lt_key K l qx hqx, rec1InitArr_ge_key K l qy hqy,
        rec1KeyBits_eq_iff comb _ _ _ (hm_lt _) h1_lt (by omega) (by omega)] at hxy
      omega
    · dsimp [key] at hxy
      rw [rec1InitArr_ge_key K l qx hqx, rec1InitArr_lt_key K l qy hqy,
        rec1KeyBits_eq_iff comb _ _ _ h1_lt (hm_lt _) (by omega) (by omega)] at hxy
      omega
    · dsimp [key] at hxy
      rw [rec1InitArr_ge_key K l qx hqx, rec1InitArr_ge_key K l qy hqy,
        rec1KeyBits_eq_iff comb _ _ _ h1_lt h1_lt (by omega) (by omega)] at hxy
      exact Fin.ext hxy.2.2
  have heq : L₁ = L₂ := comb.perm_eq_of_sorted_of_inj key L₁ L₂ hperm12 hp1 hp2 hinj
  rw [hL₂_eq] at heq
  intro p
  have hp_lt : p.1 < L₁.length := by rw [List.length_ofFn]; exact p.isLt
  have hget := congrArg (fun xs : List (Qubits (wR1Occ K)) => xs[p.1]?.getD (fun _ => false)) heq
  simp only [L₁, List.getElem?_ofFn, specArr] at hget
  rw [dif_pos p.isLt, dif_pos p.isLt] at hget
  exact hget

/-! #### 6.9 Sequential `occ` Scan (`cmpScanStep`, `scanOccStep`, `scanOccCirc`) -/

lemma cmpScanStep_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K)
    (p : ℕ) (hp : p + 1 < 2 * K) :
    (cmpScanStep as arith n K d h1K p hp).size ≤ 14 * wOf K + 118 := by
  dsimp [cmpScanStep]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, LayeredCircuit.mapWires_size]
  have h1 := arith.eqConstMSBCircuit_size 1 0
  have h3 := arith.eqRegCircuit_size (wOf K)
  have h4 := arith.eqConstMSBCircuit_size 3 7
  omega

lemma act_cmpScanStep (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (h1K : 1 ≤ K) (p : ℕ) (hp : p + 1 < 2 * K)
    (z : Qubits (totWiresDef as n K d))
    (arr : Fin (arity (dOccOf K)) → Qubits (wR1Occ K))
    (hzRec : z ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) arr)
    (hzScanB : z ∘ ancEmb as n K d ⟨8, by decide⟩ = fun _ => false)
    (hzScanC : z ∘ ancEmb as n K d ⟨9, by decide⟩ = fun _ => false)
    (hz10 : z ∘ ancEmb as n K d ⟨10, by decide⟩ = fun _ => false) :
    let q0 : Fin (arity (dOccOf K)) := ⟨p, by have := two_K_le_arity_dOcc (K := K); omega⟩
    let q1 : Fin (arity (dOccOf K)) := ⟨p + 1, by have := two_K_le_arity_dOcc (K := K); omega⟩
    let b0 : Bool := !(arr q1 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0))
    let b1 : Bool := !(arr q0 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0))
    let b2 : Bool := decide (arr q1 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) =
      arr q0 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega))
    let bVec : Qubits 3 := fun j => match j.1 with | 0 => b0 | 1 => b1 | _ => b2
    act (cmpScanStep as arith n K d h1K p hp).unitary (ket z) =
      ket (updateOn (eScanCtrl as n K d) (updateOn (eScanB as n K d) z bVec) (fun _ => b0 && b1 && b2)) := by
  have h2K : 2 * K ≤ arity (dOccOf K) := two_K_le_arity_dOcc
  have h5w := five_le_wOf h1K
  intro q0 q1 b0 b1 b2 bVec
  dsimp only [cmpScanStep, comb4, comb3]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul,
    LayeredCircuit.id_unitary, act_one]
  have hzB : z ∘ eScanB as n K d = fun _ => false := funext fun j => congrFun hzScanB _
  have hzC : z ∘ eScanCtrl as n K d = fun _ => false := funext fun j => congrFun hzScanC _
  have hzA1 : z ∘ eArith12Pref as n K d 1 (by omega) = fun _ => false := funext fun j => congrFun hz10 _
  -- c1: b0 := !(arr q1)[0]
  rw [act_eqConstOn arith
    (hIO := eRec1NotAct_disjoint_eScanBSlot as n K d _ _)
    (hIA := eRec1NotAct_disjoint_eArith12 as n K d _ _ _)
    (hOA := eScanBSlot_disjoint_eArith12 as n K d _ _ _)
    (z := z) (hzAnc := hzA1)]
  have hb0_in : z ∘ eRec1NotAct as n K d q1 =
      fun _ => arr q1 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0) := by
    have h := comp_ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
      z arr hzRec q1 0 1 (by dsimp [wR1Occ, wK1Occ]; omega)
    funext i; have hi0 : i = 0 := Fin.ext (by omega); subst hi0
    exact congrFun h 0
  have hb0_old : z (eScanBSlot as n K d ⟨0, by decide⟩ 0) = false := congrFun hzB _
  have hb0_val : (fun _ : Fin 1 => xor (z (eScanBSlot as n K d ⟨0, by decide⟩ 0))
      (decide (z ∘ eRec1NotAct as n K d q1 = natToBits 1 0))) = fun _ => b0 := by
    funext _
    rw [hb0_old, xor_false_left, hb0_in, natToBits_one_zero comb, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, funext_iff, Fin.forall_fin_one]
    dsimp [b0]
    cases arr q1 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0) <;> simp
  rw [hb0_val]
  set z1 := updateOn (eScanBSlot as n K d ⟨0, by decide⟩) z (fun _ => b0)
  -- c2: b1 := !(arr q0)[0]
  have hz1A1 : z1 ∘ eArith12Pref as n K d 1 (by omega) = fun _ => false := by
    dsimp only [z1]; rw [updateOn_comp_disjoint _ _ (eScanBSlot_disjoint_eArith12 as n K d _ _ _)]; exact hzA1
  rw [act_eqConstOn arith
    (hIO := eRec1NotAct_disjoint_eScanBSlot as n K d _ _)
    (hIA := eRec1NotAct_disjoint_eArith12 as n K d _ _ _)
    (hOA := eScanBSlot_disjoint_eArith12 as n K d _ _ _)
    (z := z1) (hzAnc := hz1A1)]
  have hb1_in : z1 ∘ eRec1NotAct as n K d q0 =
      fun _ => arr q0 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0) := by
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec1NotAct_disjoint_eScanBSlot as n K d q0 _ b a h.symm)]
    have h := comp_ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
      z arr hzRec q0 0 1 (by dsimp [wR1Occ, wK1Occ]; omega)
    funext i; have hi0 : i = 0 := Fin.ext (by omega); subst hi0
    exact congrFun h 0
  have hb1_old : z1 (eScanBSlot as n K d ⟨1, by decide⟩ 0) = false := by
    dsimp only [z1]
    have hd := eScanBSlot_disjoint as n K d (j1 := ⟨0, by decide⟩) (j2 := ⟨1, by decide⟩) (by decide)
    have h1 := congrFun (updateOn_comp_disjoint _ _ hd z (fun _ => b0)) 0
    exact h1.trans (congrFun hzB _)
  have hb1_val : (fun _ : Fin 1 => xor (z1 (eScanBSlot as n K d ⟨1, by decide⟩ 0))
      (decide (z1 ∘ eRec1NotAct as n K d q0 = natToBits 1 0))) = fun _ => b1 := by
    funext _
    rw [hb1_old, xor_false_left, hb1_in, natToBits_one_zero comb, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, funext_iff, Fin.forall_fin_one]
    dsimp [b1]
    cases arr q0 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0) <;> simp
  rw [hb1_val]
  set z2 := updateOn (eScanBSlot as n K d ⟨1, by decide⟩) z1 (fun _ => b1)
  -- c3: b2 := decide (m q1 = m q0)
  have hz2AW : z2 ∘ eArith12Pref as n K d (wOf K) (Nat.le_trans (Nat.le_succ (wOf K)) (le_max_right _ _)) =
      fun _ => false := by
    dsimp only [z2, z1]
    rw [updateOn_comp_disjoint _ _ (eScanBSlot_disjoint_eArith12 as n K d _ _ _)]
    rw [updateOn_comp_disjoint _ _ (eScanBSlot_disjoint_eArith12 as n K d _ _ _)]
    funext j; exact congrFun hz10 _
  rw [act_eqRegOn (arith := arith)
    (hAB := eRec1M_disjoint_slot as n K d (by simp [Fin.ext_iff]))
    (hAO := eRec1M_disjoint_eScanBSlot as n K d _ _)
    (hBO := eRec1M_disjoint_eScanBSlot as n K d _ _)
    (hAA := eRec1M_disjoint_eArith12 as n K d _ _ _)
    (hBA := eRec1M_disjoint_eArith12 as n K d _ _ _)
    (hOA := eScanBSlot_disjoint_eArith12 as n K d _ _ _)
    (z := z2) (hzAnc := hz2AW)]
  have hm1_in : z2 ∘ eRec1M as n K d q1 = arr q1 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) := by
    dsimp only [z2, z1]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec1M_disjoint_eScanBSlot as n K d q1 _ b a h.symm)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec1M_disjoint_eScanBSlot as n K d q1 _ b a h.symm)]
    exact comp_ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
      z arr hzRec q1 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega)
  have hm0_in : z2 ∘ eRec1M as n K d q0 = arr q0 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) := by
    dsimp only [z2, z1]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec1M_disjoint_eScanBSlot as n K d q0 _ b a h.symm)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec1M_disjoint_eScanBSlot as n K d q0 _ b a h.symm)]
    exact comp_ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
      z arr hzRec q0 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega)
  have hb2_old : z2 (eScanBSlot as n K d ⟨2, by decide⟩ 0) = false := by
    dsimp only [z2, z1]
    have hd1 := eScanBSlot_disjoint as n K d (j1 := ⟨1, by decide⟩) (j2 := ⟨2, by decide⟩) (by decide)
    have hd0 := eScanBSlot_disjoint as n K d (j1 := ⟨0, by decide⟩) (j2 := ⟨2, by decide⟩) (by decide)
    have h1 := congrFun (updateOn_comp_disjoint _ _ hd1 z1 (fun _ => b1)) 0
    have h0 := congrFun (updateOn_comp_disjoint _ _ hd0 z (fun _ => b0)) 0
    exact h1.trans (h0.trans (congrFun hzB _))
  have hb2_val : (fun _ : Fin 1 => xor (z2 (eScanBSlot as n K d ⟨2, by decide⟩ 0))
      (decide (z2 ∘ eRec1M as n K d q1 = z2 ∘ eRec1M as n K d q0))) = fun _ => b2 := by
    funext _; rw [hb2_old, xor_false_left, hm1_in, hm0_in]
  rw [hb2_val]
  set z3 := updateOn (eScanBSlot as n K d ⟨2, by decide⟩) z2 (fun _ => b2)
  have hz3_eq : z3 = updateOn (eScanB as n K d) z bVec := by
    funext u
    by_cases hu : u ∈ Set.range (eScanB as n K d)
    · rcases hu with ⟨j, rfl⟩
      rw [updateOn_apply_emb]
      dsimp only [z3, z2, z1, eScanBSlot]
      fin_cases j
      · have hd1 : ∀ a b, (sliceEmb 1 1 (by omega)).trans (eScanB as n K d) a ≠
            (sliceEmb 2 1 (by omega)).trans (eScanB as n K d) b :=
          fun a b h => eScanBSlot_disjoint as n K d (j1 := ⟨1, by decide⟩) (j2 := ⟨2, by decide⟩) (by decide) a b h
        have hc2 : (eScanB as n K d ⟨0, by decide⟩) ∉ Set.range ((sliceEmb 2 1 (by omega)).trans (eScanB as n K d)) := by
          rintro ⟨b, hb⟩; exact eScanBSlot_disjoint as n K d (j1 := ⟨2, by decide⟩) (j2 := ⟨0, by decide⟩) (by decide) b 0 hb
        have hc1 : (eScanB as n K d ⟨0, by decide⟩) ∉ Set.range ((sliceEmb 1 1 (by omega)).trans (eScanB as n K d)) := by
          rintro ⟨b, hb⟩; exact eScanBSlot_disjoint as n K d (j1 := ⟨1, by decide⟩) (j2 := ⟨0, by decide⟩) (by decide) b 0 hb
        rw [updateOn_apply_not_mem _ _ _ hc2, updateOn_apply_not_mem _ _ _ hc1]
        change updateOn ((sliceEmb 0 1 (by omega)).trans (eScanB as n K d)) z (fun _ => b0)
            (((sliceEmb 0 1 (by omega)).trans (eScanB as n K d)) 0) = _
        rw [updateOn_apply_emb]; rfl
      · have hc2 : (eScanB as n K d ⟨1, by decide⟩) ∉ Set.range ((sliceEmb 2 1 (by omega)).trans (eScanB as n K d)) := by
          rintro ⟨b, hb⟩; exact eScanBSlot_disjoint as n K d (j1 := ⟨2, by decide⟩) (j2 := ⟨1, by decide⟩) (by decide) b 0 hb
        rw [updateOn_apply_not_mem _ _ _ hc2]
        change updateOn ((sliceEmb 1 1 (by omega)).trans (eScanB as n K d)) _ (fun _ => b1)
            (((sliceEmb 1 1 (by omega)).trans (eScanB as n K d)) 0) = _
        rw [updateOn_apply_emb]; rfl
      · change updateOn ((sliceEmb 2 1 (by omega)).trans (eScanB as n K d)) _ (fun _ => b2)
            (((sliceEmb 2 1 (by omega)).trans (eScanB as n K d)) 0) = _
        rw [updateOn_apply_emb]; rfl
    · have hnot : ∀ j : Fin 3, u ∉ Set.range (eScanBSlot as n K d j) := by
        intro j ⟨b, hb⟩; exact hu ⟨sliceEmb j.1 1 (by omega) b, hb⟩
      dsimp only [z3, z2, z1]
      rw [updateOn_apply_not_mem _ _ _ (hnot ⟨2, by decide⟩),
        updateOn_apply_not_mem _ _ _ (hnot ⟨1, by decide⟩),
        updateOn_apply_not_mem _ _ _ (hnot ⟨0, by decide⟩),
        updateOn_apply_not_mem _ _ _ hu]
  rw [hz3_eq]
  -- c4: eScanCtrl := b0 && b1 && b2
  have hz3A3 : updateOn (eScanB as n K d) z bVec ∘ eArith12Pref as n K d 3 (by omega) = fun _ => false := by
    rw [updateOn_comp_disjoint _ _ (eScanB_disjoint_eArith12 as n K d _ _)]
    funext j; exact congrFun hz10 _
  rw [act_allTrueAndOn comb arith
    (hIO := eScanB_disjoint_eScanCtrl as n K d)
    (hIA := eScanB_disjoint_eArith12 as n K d _ _)
    (hOA := eScanCtrl_disjoint_eArith12 as n K d _ _)
    (z := updateOn (eScanB as n K d) z bVec) (hzAnc := hz3A3)]
  congr 1; congr 1; funext _
  have hcb : updateOn (eScanB as n K d) z bVec (eScanCtrl as n K d 0) = false := by
    rw [← Function.comp_apply (f := updateOn (eScanB as n K d) z bVec),
      updateOn_comp_disjoint _ _ (eScanB_disjoint_eScanCtrl as n K d)]
    exact congrFun hzC 0
  rw [hcb, xor_false_left]
  have hcompB : updateOn (eScanB as n K d) z bVec ∘ eScanB as n K d = bVec := updateOn_comp_emb _ _ _
  have h0 : updateOn (eScanB as n K d) z bVec (eScanB as n K d (0 : Fin 3)) = b0 :=
    congrFun hcompB (0 : Fin 3)
  have h1 : updateOn (eScanB as n K d) z bVec (eScanB as n K d (1 : Fin 3)) = b1 :=
    congrFun hcompB (1 : Fin 3)
  have h2 : updateOn (eScanB as n K d) z bVec (eScanB as n K d (2 : Fin 3)) = b2 :=
    congrFun hcompB (2 : Fin 3)
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Fin.forall_fin_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, IsEmpty.forall_iff, and_true, Bool.and_eq_true, and_assoc]
  rw [h0, h1, h2]

lemma scanOccStep_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K)
    (p : ℕ) (hp : p + 1 < 2 * K) :
    (scanOccStep as arith n K d h1K p hp).size ≤ 49 * wOf K + 236 := by
  dsimp [scanOccStep]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, LayeredCircuit.mapWires_size, LayeredCircuit.adj_size]
  have hcmp := cmpScanStep_size as arith n K d h1K p hp
  have hcopy := arith.ctrlCopyRegCircuit_size (wOf K)
  have hadd := arith.ctrlAddConstInPlaceMSBCircuit_size (wOf K) 1
  omega

noncomputable def scanOccPay (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (k : ℕ)
    (p : Fin (arity (dOccOf K))) : Qubits (wOf K) :=
  if hp : p.1 < 2 * K then
    let L_occ := occSortedList (2 * K) l
    let r := L_occ[p.1]'(by rw [occSortedList_length]; exact hp)
    if p.1 ≤ k ∧ r.1 then natToBits (wOf K) (seqScanOcc L_occ p.1) else fun _ => false
  else fun _ => false

noncomputable def scanRecArr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (k : ℕ)
    (p : Fin (arity (dOccOf K))) : Qubits (wR1Occ K) :=
  updateOn (sliceEmb (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega))
    (rec1SortedArr K l p) (scanOccPay K l k p)

lemma seqScanOcc_le {N : ℕ} (L : List (Bool × ℕ × Fin N)) (p : ℕ) :
    seqScanOcc L p ≤ p := by
  induction p with
  | zero => simp [seqScanOcc]
  | succ p ih =>
    dsimp [seqScanOcc]
    cases L[p + 1]? <;> cases L[p]? <;> simp only [] <;> try exact Nat.zero_le _
    split_ifs <;> omega

lemma scanRecArr_zero (comb : LcgSym54Comb) (br : BitonicRouting54) {n K : ℕ} (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) :
    scanRecArr K l 0 = rec1SortedArr K l := by
  funext p
  dsimp [scanRecArr]
  have hpay0 : scanOccPay K l 0 p = fun _ => false := by
    dsimp [scanOccPay]
    split_ifs with hp hle
    · have hp0 : p.1 = 0 := by omega
      rw [hp0]; simp [seqScanOcc, natToBits_zero comb]
    · rfl
    · rfl
  rw [hpay0]
  have hrec := rec1SortedArr_eq_occSpec comb br h1K l p
  have h00 : recPay54 (rec1SortedArr K l p) = fun _ => false := by
    rw [hrec]
    split_ifs <;> exact recPay54_rec1InitArr K l _
  apply updateOn_noop
  funext j
  have := congrFun h00 j
  dsimp [recPay54] at this
  have hidx : sliceEmb (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega) j =
      Fin.natAdd (wK1Occ K) j := Fin.ext (by simp)
  rw [Function.comp_apply, hidx]
  exact this

lemma act_scanOccStep (comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1))
    (p : ℕ) (hp : p + 1 < 2 * K)
    (z : Qubits (totWiresDef as n K d))
    (hzRec : z ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l p))
    (hzScanB : z ∘ ancEmb as n K d ⟨8, by decide⟩ = fun _ => false)
    (hzScanC : z ∘ ancEmb as n K d ⟨9, by decide⟩ = fun _ => false)
    (hz10 : z ∘ ancEmb as n K d ⟨10, by decide⟩ = fun _ => false) :
    act (scanOccStep as arith n K d h1K p hp).unitary (ket z) =
      ket (updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l (p + 1)))) := by
  have h2K : 2 * K ≤ arity (dOccOf K) := two_K_le_arity_dOcc
  have hpow : 2 * K < 2 ^ wOf K := lt_trans (two_K_lt_B2 h1K) (by
    have := two_mul_B2_add_one_lt_two_pow_wOf h1K; omega)
  have h1_lt : 1 < 2 ^ wOf K := by
    have := five_le_wOf h1K
    calc 1 < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ wOf K := Nat.pow_le_pow_right (by norm_num) this
  let q0 : Fin (arity (dOccOf K)) := ⟨p, by omega⟩
  let q1 : Fin (arity (dOccOf K)) := ⟨p + 1, by omega⟩
  let L_occ := occSortedList (2 * K) l
  have hL_len : L_occ.length = 2 * K := occSortedList_length (2 * K) l
  let r0 := L_occ[p]'(by rw [hL_len]; omega)
  let r1 := L_occ[p + 1]'(by rw [hL_len]; exact hp)
  have hr0_f := occSortedList_mem_fields (List.getElem_mem (by rw [hL_len]; omega : p < L_occ.length))
  have hr1_f := occSortedList_mem_fields (List.getElem_mem (by rw [hL_len]; exact hp : p + 1 < L_occ.length))
  have hsr0 : rec1SortedArr K l q0 =
      rec1SlotFn (wOf K) (fun _ => !r0.1) (natToBits (wOf K) r0.2.1) (natToBits (wOf K) r0.2.2.1) (fun _ => false) := by
    rw [rec1SortedArr_eq_occSpec comb br h1K l q0, dif_pos (by dsimp [q0]; omega)]
    change rec1InitArr K l ⟨r0.2.2.1, by omega⟩ = _
    dsimp only [rec1InitArr, actBitsFn, mBitsFn]
    rw [dif_pos r0.2.2.isLt, ← hr0_f.1, ← hr0_f.2]
  have hsr1 : rec1SortedArr K l q1 =
      rec1SlotFn (wOf K) (fun _ => !r1.1) (natToBits (wOf K) r1.2.1) (natToBits (wOf K) r1.2.2.1) (fun _ => false) := by
    rw [rec1SortedArr_eq_occSpec comb br h1K l q1, dif_pos (by dsimp [q1]; exact hp)]
    change rec1InitArr K l ⟨r1.2.2.1, by omega⟩ = _
    dsimp only [rec1InitArr, actBitsFn, mBitsFn]
    rw [dif_pos r1.2.2.isLt, ← hr1_f.1, ← hr1_f.2]
  let arr0 := scanRecArr K l p
  have ha_q0 : arr0 q0 = rec1SlotFn (wOf K) (fun _ => !r0.1) (natToBits (wOf K) r0.2.1)
      (natToBits (wOf K) r0.2.2.1) (scanOccPay K l p q0) := by
    dsimp [arr0, scanRecArr]; rw [hsr0, updateOn_rec1SlotFn_3]
  have ha_q1 : arr0 q1 = rec1SlotFn (wOf K) (fun _ => !r1.1) (natToBits (wOf K) r1.2.1)
      (natToBits (wOf K) r1.2.2.1) (fun _ => false) := by
    dsimp [arr0, scanRecArr, scanOccPay]
    rw [hsr1, dif_pos (by simp [q1]; exact hp), if_neg (by simp [q1]), updateOn_rec1SlotFn_3]
  let ctrlSpec : Bool := r1.1 && r0.1 && (r1.2.1 == r0.2.1)
  let newOcc : Qubits (wOf K) :=
    if r1.1 then natToBits (wOf K) (seqScanOcc L_occ (p + 1)) else fun _ => false
  have hnewOcc_eq : newOcc =
      if ctrlSpec then natToBits (wOf K) (1 + seqScanOcc L_occ p) else fun _ => false := by
    have hseq : seqScanOcc L_occ (p + 1) = if ctrlSpec then seqScanOcc L_occ p + 1 else 0 := by
      have hget1 : L_occ[p + 1]? = some r1 := List.getElem?_eq_getElem (by rw [hL_len]; exact hp)
      have hget0 : L_occ[p]? = some r0 := List.getElem?_eq_getElem (by rw [hL_len]; omega)
      dsimp only [seqScanOcc]
      rw [hget1, hget0]
    dsimp [newOcc]; rw [hseq]
    by_cases hct : ctrlSpec = true
    · have hr1t : r1.1 = true := by
        dsimp [ctrlSpec] at hct; exact (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hct).1 |>.1
      simp [hct, hr1t, add_comm]
    · simp only [hct, Bool.false_eq_true, ↓reduceIte]
      by_cases hr1t : r1.1 = true
      · simp [hr1t, natToBits_zero comb]
      · simp [hr1t]
  dsimp only [scanOccStep]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul,
    LayeredCircuit.id_unitary, act_one]
  -- 1. Forward cmpScanStep
  rw [act_cmpScanStep comb as arith n K d h1K p hp z arr0 hzRec hzScanB hzScanC hz10]
  have hb0_eq : (!(arr0 q1 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0))) = r1.1 := by
    have h0 := congrFun (rec1SlotFn_comp_0 (wOf K) (fun _ => !r1.1) (natToBits (wOf K) r1.2.1)
      (natToBits (wOf K) r1.2.2.1) (fun _ => false)) 0
    rw [ha_q1]
    exact congrArg Bool.not h0 |>.trans (by cases r1.1 <;> rfl)
  have hb1_eq : (!(arr0 q0 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0))) = r0.1 := by
    have h0 := congrFun (rec1SlotFn_comp_0 (wOf K) (fun _ => !r0.1) (natToBits (wOf K) r0.2.1)
      (natToBits (wOf K) r0.2.2.1) (scanOccPay K l p q0)) 0
    rw [ha_q0]
    exact congrArg Bool.not h0 |>.trans (by cases r0.1 <;> rfl)
  have hb2_eq : decide (arr0 q1 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) =
      arr0 q0 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega)) = (r1.2.1 == r0.2.1) := by
    rw [ha_q1, ha_q0, rec1SlotFn_comp_1, rec1SlotFn_comp_1]
    have hm0 : r0.2.1 < 2 ^ wOf K := by rw [hr0_f.2]; exact lt_of_le_of_lt (comb.runOffset_le_N l r0.2.2) hpow
    have hm1 : r1.2.1 < 2 ^ wOf K := by rw [hr1_f.2]; exact lt_of_le_of_lt (comb.runOffset_le_N l r1.2.2) hpow
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, beq_iff_eq]
    exact ⟨fun h => by rw [← comb.bitsToNat_natToBits hm1, ← comb.bitsToNat_natToBits hm0, h],
      fun h => by rw [h]⟩
  have hctrl_eq : (!(arr0 q1 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0)) &&
      !(arr0 q0 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0)) &&
      decide (arr0 q1 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) =
        arr0 q0 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega))) = ctrlSpec := by
    dsimp only [ctrlSpec]
    rw [hb0_eq, hb1_eq, hb2_eq]
  set bVec : Qubits 3 := fun j => match j.1 with
    | 0 => !arr0 q1 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0)
    | 1 => !arr0 q0 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0)
    | _ => decide (arr0 q1 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) =
        arr0 q0 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega))
  set zB := updateOn (eScanB as n K d) z bVec
  set zC := updateOn (eScanCtrl as n K d) zB (fun _ => ctrlSpec)
  have hzC_eq : updateOn (eScanCtrl as n K d) zB (fun _ =>
      !arr0 q1 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0) &&
      !arr0 q0 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0) &&
      decide (arr0 q1 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) =
        arr0 q0 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega))) = zC := by
    rw [hctrl_eq]
  rw [hzC_eq]
  -- 2. ctrlCopyReg: eRec1Occ q1 gets (if ctrlSpec then occ0 else 0)
  dsimp only [comb3]
  rw [act_ctrlCopyRegOn arith
    (hCS := eScanCtrl_disjoint_eRec1Occ as n K d q0)
    (hCD := eScanCtrl_disjoint_eRec1Occ as n K d q1)
    (hSD := eRec1Occ_disjoint_slot as n K d (by simp [q0, q1, Fin.ext_iff]))]
  have hzC_ctrl : zC (eScanCtrl as n K d 0) = ctrlSpec := by
    dsimp only [zC]; rw [updateOn_apply_emb]
  have hzC_rec : zC ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) arr0 := by
    dsimp only [zC, zB]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec1Reg_disjoint_eScanCtrl as n K d b a h.symm)]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec1Reg_disjoint_eScanB as n K d b a h.symm)]
    exact hzRec
  have hzC_occ0 : zC ∘ eRec1Occ as n K d q0 = scanOccPay K l p q0 := by
    have h := comp_ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
      zC arr0 hzC_rec q0 (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega)
    change zC ∘ eRec1Occ as n K d q0 = _ at h
    rw [h, ha_q0, rec1SlotFn_comp_3]
  have hzC_occ1 : zC ∘ eRec1Occ as n K d q1 = fun _ => false := by
    have h := comp_ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
      zC arr0 hzC_rec q1 (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega)
    change zC ∘ eRec1Occ as n K d q1 = _ at h
    rw [h, ha_q1, rec1SlotFn_comp_3]
  let copyOcc : Qubits (wOf K) := if ctrlSpec then scanOccPay K l p q0 else fun _ => false
  have hcopy_val : (if zC (eScanCtrl as n K d 0) then
      fun j => xor (zC (eRec1Occ as n K d q1 j)) (zC (eRec1Occ as n K d q0 j)) else zC ∘ eRec1Occ as n K d q1) =
      copyOcc := by
    rw [hzC_ctrl]
    dsimp [copyOcc]
    split_ifs with hct
    · funext j
      have h1 : zC (eRec1Occ as n K d q1 j) = false := congrFun hzC_occ1 j
      have h2 : zC (eRec1Occ as n K d q0 j) = scanOccPay K l p q0 j := congrFun hzC_occ0 j
      rw [h1, h2, xor_false_left]
    · exact hzC_occ1
  rw [hcopy_val]
  set zCopy := updateOn (eRec1Occ as n K d q1) zC copyOcc
  -- 3. ctrlAddConst 1: eRec1Occ q1 gets newOcc
  have hzCopy_anc : zCopy ∘ eArith12Pref as n K d (wOf K + 1) (le_max_right _ _) = fun _ => false := by
    dsimp only [zCopy, zC, zB]
    rw [updateOn_comp_disjoint _ _ (eRec1Occ_disjoint_eArith12 as n K d _ _ q1)]
    rw [updateOn_comp_disjoint _ _ (eScanCtrl_disjoint_eArith12 as n K d _ _)]
    rw [updateOn_comp_disjoint _ _ (eScanB_disjoint_eArith12 as n K d _ _)]
    funext j; exact congrFun hz10 _
  rw [act_ctrlAddConstOn (arith := arith)
    (hCB := eScanCtrl_disjoint_eRec1Occ as n K d q1)
    (hCA := eScanCtrl_disjoint_eArith12 as n K d _ _)
    (hBA := eRec1Occ_disjoint_eArith12 as n K d _ _ q1)
    (z := zCopy) (hzAnc := hzCopy_anc)]
  have hzCopy_ctrl : zCopy (eScanCtrl as n K d 0) = ctrlSpec := by
    dsimp only [zCopy]
    rw [← Function.comp_apply (f := updateOn (eRec1Occ as n K d q1) zC copyOcc),
      updateOn_comp_disjoint _ _ (fun a b h => eScanCtrl_disjoint_eRec1Occ as n K d q1 b a h.symm)]
    exact hzC_ctrl
  have hzCopy_occ1 : zCopy ∘ eRec1Occ as n K d q1 = copyOcc := updateOn_comp_emb _ _ _
  have hadd_val : (if zCopy (eScanCtrl as n K d 0) then
      natToBits (wOf K) (1 % 2 ^ wOf K + bitsToNat (zCopy ∘ eRec1Occ as n K d q1))
      else zCopy ∘ eRec1Occ as n K d q1) = newOcc := by
    rw [hzCopy_ctrl, Nat.mod_eq_of_lt h1_lt, hzCopy_occ1, hnewOcc_eq]
    dsimp [copyOcc]
    split_ifs with hct
    · have hr0t : r0.1 = true := by
        dsimp [ctrlSpec] at hct
        exact (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hct).1 |>.2
      have hpay0 : scanOccPay K l p q0 = natToBits (wOf K) (seqScanOcc L_occ p) := by
        dsimp [scanOccPay, q0]; rw [dif_pos (by omega), if_pos ⟨le_rfl, hr0t⟩]
      have hseq_lt : seqScanOcc L_occ p < 2 ^ wOf K :=
        lt_of_le_of_lt (seqScanOcc_le L_occ p) (by omega)
      rw [hpay0, comb.bitsToNat_natToBits hseq_lt]
    · rfl
  rw [hadd_val]
  -- 4. cmp.adj restores (eScanB, eScanCtrl) to 0 cleanly via act_adj_ket!
  let zFinal := updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l (p + 1)))
  have hzFinal_eq : zFinal = updateOn (eRec1Occ as n K d q1) z newOcc := by
    dsimp only [zFinal]
    change _ = updateOn (ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) q1
      (wK1Occ K) (wOf K) _) z newOcc
    rw [updateOn_ancRegField_eq_slot, comp_ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K)
        (ancLen_3 n K d _) z arr0 hzRec q1, ha_q1, updateOn_rec1SlotFn_3]
    rw [updateOn_ancRegSlot_eq as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
        z arr0 hzRec q1]
    congr 1; congr 1; funext r
    by_cases hr : r = q1
    · subst hr; rw [Function.update_self]
      dsimp [scanRecArr]; rw [hsr1, updateOn_rec1SlotFn_3]; congr 1
      dsimp only [scanOccPay, newOcc, q1]; rw [dif_pos hp]
      change (if p + 1 ≤ p + 1 ∧ r1.1 = true then natToBits (wOf K) (seqScanOcc L_occ (p + 1)) else fun _ => false) =
        if r1.1 = true then natToBits (wOf K) (seqScanOcc L_occ (p + 1)) else fun _ => false
      by_cases hr1t : r1.1 = true
      · rw [if_pos ⟨le_rfl, hr1t⟩, if_pos hr1t]
      · rw [if_neg (fun h => hr1t h.2), if_neg hr1t]
    · rw [Function.update_of_ne hr]
      dsimp only [arr0, scanRecArr]
      congr 1
      dsimp only [scanOccPay]
      by_cases hrt : r.1 < 2 * K
      · rw [dif_pos hrt, dif_pos hrt]
        have hne : r.1 ≠ p + 1 := fun hv => hr (Fin.ext hv)
        have hle_iff : r.1 ≤ p + 1 ↔ r.1 ≤ p := by omega
        simp only [hle_iff]
      · rw [dif_neg hrt, dif_neg hrt]
  have hzF_rec : zFinal ∘ eRec1Reg as n K d =
      flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l (p + 1)) := updateOn_comp_emb _ _ _
  have hzF_B : zFinal ∘ ancEmb as n K d ⟨8, by decide⟩ = fun _ => false := by
    dsimp only [zFinal]
    rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨8, by decide⟩ (by decide))]
    exact hzScanB
  have hzF_C : zFinal ∘ ancEmb as n K d ⟨9, by decide⟩ = fun _ => false := by
    dsimp only [zFinal]
    rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨9, by decide⟩ (by decide))]
    exact hzScanC
  have hzF_10 : zFinal ∘ ancEmb as n K d ⟨10, by decide⟩ = fun _ => false := by
    dsimp only [zFinal]
    rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨10, by decide⟩ (by decide))]
    exact hz10
  have hcmp_back := act_cmpScanStep comb as arith n K d h1K p hp zFinal (scanRecArr K l (p + 1))
    hzF_rec hzF_B hzF_C hzF_10
  have hna0_eq : scanRecArr K l (p + 1) q0 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0) =
      arr0 q0 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0) := by
    dsimp only [arr0, scanRecArr]
    rw [hsr0, updateOn_rec1SlotFn_3, updateOn_rec1SlotFn_3]
    exact (congrFun (rec1SlotFn_comp_0 (wOf K) (fun _ => !r0.1) (natToBits (wOf K) r0.2.1)
      (natToBits (wOf K) r0.2.2.1) (scanOccPay K l (p + 1) q0)) 0).trans
      (congrFun (rec1SlotFn_comp_0 (wOf K) (fun _ => !r0.1) (natToBits (wOf K) r0.2.1)
        (natToBits (wOf K) r0.2.2.1) (scanOccPay K l p q0)) 0).symm
  have hna1_eq : scanRecArr K l (p + 1) q1 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0) =
      arr0 q1 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0) := by
    dsimp only [arr0, scanRecArr]
    rw [hsr1, updateOn_rec1SlotFn_3, updateOn_rec1SlotFn_3]
    exact (congrFun (rec1SlotFn_comp_0 (wOf K) (fun _ => !r1.1) (natToBits (wOf K) r1.2.1)
      (natToBits (wOf K) r1.2.2.1) (scanOccPay K l (p + 1) q1)) 0).trans
      (congrFun (rec1SlotFn_comp_0 (wOf K) (fun _ => !r1.1) (natToBits (wOf K) r1.2.1)
        (natToBits (wOf K) r1.2.2.1) (scanOccPay K l p q1)) 0).symm
  have hm0_eq : scanRecArr K l (p + 1) q0 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) =
      arr0 q0 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) := by
    dsimp [arr0, scanRecArr]
    rw [hsr0, updateOn_rec1SlotFn_3, updateOn_rec1SlotFn_3, rec1SlotFn_comp_1, rec1SlotFn_comp_1]
  have hm1_eq : scanRecArr K l (p + 1) q1 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) =
      arr0 q1 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) := by
    dsimp [arr0, scanRecArr]
    rw [hsr1, updateOn_rec1SlotFn_3, updateOn_rec1SlotFn_3, rec1SlotFn_comp_1, rec1SlotFn_comp_1]
  have hact_back : act (cmpScanStep as arith n K d h1K p hp).unitary (ket zFinal) =
      ket (updateOn (eRec1Occ as n K d q1) zCopy newOcc) := by
    rw [hcmp_back]
    congr 1
    rw [hna0_eq, hna1_eq, hm0_eq, hm1_eq]
    change updateOn (eScanCtrl as n K d) (updateOn (eScanB as n K d) zFinal bVec)
        ((fun _ => !(arr0 q1 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0)) &&
          !(arr0 q0 (sliceEmb 0 1 (by dsimp [wR1Occ, wK1Occ]; omega) 0)) &&
          decide (arr0 q1 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega) =
            arr0 q0 ∘ sliceEmb 1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega)))) = _
    rw [hctrl_eq, hzFinal_eq]
    dsimp only [zCopy, zC, zB]
    rw [updateOn_idem]
    rw [updateOn_comm (eScanB as n K d) (eRec1Occ as n K d q1) (eScanB_disjoint_eRec1Occ as n K d q1)]
    rw [updateOn_comm (eScanCtrl as n K d) (eRec1Occ as n K d q1) (eScanCtrl_disjoint_eRec1Occ as n K d q1)]
  exact act_adj_ket _ hact_back

lemma scanOccCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) :
    (scanOccCirc as arith n K d h1K).size ≤ (2 * K - 1) * (49 * wOf K + 236) := by
  dsimp [scanOccCirc]
  have h := LayeredCircuit_seqList_size_le
    ((List.range (2 * K - 1)).map fun p =>
      if hp : p + 1 < 2 * K then scanOccStep as arith n K d h1K p hp else LayeredCircuit.id _)
    (49 * wOf K + 236)
    (by
      intro lc hlc
      simp only [List.mem_map] at hlc
      rcases hlc with ⟨p, _, rfl⟩
      split_ifs with hp
      · exact scanOccStep_size as arith n K d h1K p hp
      · simp)
  simpa using h

lemma act_scanOccCirc (comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1))
    (z : Qubits (totWiresDef as n K d))
    (hzRec : z ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (rec1SortedArr K l))
    (hzScanB : z ∘ ancEmb as n K d ⟨8, by decide⟩ = fun _ => false)
    (hzScanC : z ∘ ancEmb as n K d ⟨9, by decide⟩ = fun _ => false)
    (hz10 : z ∘ ancEmb as n K d ⟨10, by decide⟩ = fun _ => false) :
    act (scanOccCirc as arith n K d h1K).unitary (ket z) =
      ket (updateOn (eRec1Reg as n K d) z
        (flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l (2 * K - 1)))) := by
  let st (k : ℕ) : Qubits (totWiresDef as n K d) :=
    updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l k))
  have h0 : st 0 = z := by
    dsimp only [st]
    rw [scanRecArr_zero comb br h1K l]
    exact updateOn_noop _ _ _ hzRec
  conv_lhs => rw [← h0]
  dsimp [scanOccCirc]
  exact act_seqList_range st
    (fun p => if hp : p + 1 < 2 * K then scanOccStep as arith n K d h1K p hp else LayeredCircuit.id _)
    (2 * K - 1)
    (fun p hp => by
      have hp' : p + 1 < 2 * K := by omega
      rw [dif_pos hp']
      have hrec : st p ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l p) :=
        updateOn_comp_emb _ _ _
      have hB : st p ∘ ancEmb as n K d ⟨8, by decide⟩ = fun _ => false := by
        dsimp only [st]
        rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨8, by decide⟩ (by decide))]
        exact hzScanB
      have hC : st p ∘ ancEmb as n K d ⟨9, by decide⟩ = fun _ => false := by
        dsimp only [st]
        rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨9, by decide⟩ (by decide))]
        exact hzScanC
      have h10 : st p ∘ ancEmb as n K d ⟨10, by decide⟩ = fun _ => false := by
        dsimp only [st]
        rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨10, by decide⟩ (by decide))]
        exact hz10
      have hs := act_scanOccStep comb br as arith n K d h1K l p hp' (st p) hrec hB hC h10
      rw [hs]
      congr 1; dsimp only [st]; rw [updateOn_idem])

/-! #### 6.10 Unrouting `occ`, Swapping to `eOccReg`, and Uncomputing `eRec1Reg` -/

lemma unrouteRec1Circ_size (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ) :
    ((unrouteRec1Circ as br n K d).size : ℝ) ≤
      br.C_sort * (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1) := by
  dsimp [unrouteRec1Circ]
  rw [LayeredCircuit.mapWires_size, LayeredCircuit.adj_size]
  simpa [wR1Occ, add_assoc] using br.bitonicSortKeyCircuit_size (dOccOf K) (wK1Occ K) (wP1Occ K) true

def occRoutedPay (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (q : Fin (arity (dOccOf K))) :
    Qubits (wOf K) :=
  if hq : q.1 < 2 * K then occBitsFn K l ⟨q.1, hq⟩ else fun _ => false

def rec1WithOccArr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (q : Fin (arity (dOccOf K))) :
    Qubits (wR1Occ K) :=
  Fin.append (recKey54 (rec1InitArr K l q)) (occRoutedPay K l q)

lemma rec1WithOccArr_lt_update (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (q : Fin (arity (dOccOf K))) (hq : q.1 < 2 * K) :
    updateOn (sliceEmb (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega))
      (rec1WithOccArr K l q) (fun _ => false) = rec1InitArr K l q := by
  dsimp [rec1WithOccArr, rec1InitArr]
  rw [dif_pos hq, recKey54_rec1SlotFn]
  exact updateOn_rec1SlotFn_3 (wOf K) _ _ _ _ _

lemma rec1WithOccArr_ge_eq (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (q : Fin (arity (dOccOf K))) (hq : ¬ q.1 < 2 * K) :
    rec1WithOccArr K l q = rec1InitArr K l q := by
  dsimp [rec1WithOccArr, occRoutedPay, rec1InitArr]
  rw [dif_neg hq, dif_neg hq, recKey54_rec1SlotFn]; rfl

lemma act_unrouteRec1Circ (comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
    (n K d : ℕ) (h1K : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1))
    (z : Qubits (totWiresDef as n K d))
    (hzRec : z ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l (2 * K - 1)))
    (hzTr : z ∘ eTr1 as n K d = rec1SortTr K l)
    (hzAnc : z ∘ ancEmb as n K d ⟨7, by decide⟩ = fun _ => false) :
    act (unrouteRec1Circ as br n K d).unitary (ket z) =
      ket (updateOn (eTr1 as n K d)
        (updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1WithOccArr K l)))
        (fun _ => false)) := by
  have h2KN1 : 2 * K ≤ arity (dOccOf K) := two_K_le_arity_dOcc
  have hN1pow : arity (dOccOf K) < 2 ^ wOf K := by
    have ha := arity_dOcc_lt_four_K h1K
    have hb := two_K_lt_B2 h1K
    have hc := two_mul_B2_add_one_lt_two_pow_wOf h1K
    omega
  have hm_lt : ∀ i : Fin (2 * K), runOffset l i < 2 ^ wOf K := fun i => by
    have := comb.runOffset_le_N l i; omega
  have h1_lt : 1 < 2 ^ wOf K := by
    have := five_le_wOf h1K
    calc 1 < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ wOf K := Nat.pow_le_pow_right (by norm_num) this
  let kIn := recKey54 ∘ rec1InitArr K l
  let yP := scanOccPay K l (2 * K - 1)
  have hscan_eq : scanRecArr K l (2 * K - 1) =
      fun p => Fin.append (sort bitsToNat (dOccOf K) true kIn p) (yP p) := by
    funext p
    have hsort_k : recKey54 (rec1SortedArr K l p) = sort bitsToNat (dOccOf K) true kIn p := by
      change (recKey54 ∘ rec1SortedArr K l) p = _
      dsimp [rec1SortedArr, kIn]
      exact congrFun (br.sort_of_key_comp bitsToNat recKey54 (dOccOf K) true (rec1InitArr K l)) p
    rw [← hsort_k]
    dsimp [scanRecArr, yP]
    funext u
    induction u using Fin.addCases with
    | left a =>
      have hnot : Fin.castAdd (wP1Occ K) a ∉
          Set.range (sliceEmb (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega)) := by
        rintro ⟨b, hb⟩
        have hv := congrArg Fin.val hb
        simp [wP1Occ, wK1Occ] at hv; omega
      rw [updateOn_apply_not_mem _ _ _ hnot, Fin.append_left]
      rfl
    | right b =>
      have hb : Fin.natAdd (wK1Occ K) b = sliceEmb (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega) b :=
        Fin.ext (by simp)
      rw [hb, updateOn_apply_emb]
      rw [← hb, Fin.append_right]
  have htr_eq : rec1SortTr K l = sortTrace bitsToNat (dOccOf K) true kIn := by
    dsimp [rec1SortTr, kIn]
    exact br.sortTrace_of_key_comp bitsToNat recKey54 (dOccOf K) true (rec1InitArr K l)
  have hanc : z ∘ eSort1Anc as n K d = fun _ => false := funext fun k => congrFun hzAnc _
  have hcomp := comp_packDTA54Emb (eRec1Reg as n K d) (eTr1 as n K d) (eSort1Anc as n K d)
    (eRec1Reg_disjoint_eTr1 as n K d) (eRec1Reg_disjoint_eSort1Anc as n K d)
    (eTr1_disjoint_eSort1Anc as n K d) z (scanRecArr K l (2 * K - 1)) (rec1SortTr K l)
    hzRec hzTr hanc
  rw [hscan_eq, htr_eq] at hcomp
  have hunr_spec := br.act_bitonicSortKeyCircuit_adj_unroute (dOccOf K) (wK1Occ K) (wP1Occ K) true kIn yP
  -- Use unrouteSort_rel_sort to identify unrouteSort yP with occRoutedPay
  have hrel : ∀ q : Fin (arity (dOccOf K)),
      unrouteSort (dOccOf K) (sortTrace bitsToNat (dOccOf K) true kIn) yP q = occRoutedPay K l q := by
    let R : Qubits (wK1Occ K) → Qubits (wOf K) → Prop :=
      fun kb ob => ∀ q : Fin (arity (dOccOf K)), kb = kIn q → ob = occRoutedPay K l q
    have hsortR : ∀ p : Fin (arity (dOccOf K)),
        R (sort bitsToNat (dOccOf K) true kIn p) (yP p) := by
      intro p q hkq
      have hsort_k : sort bitsToNat (dOccOf K) true kIn p = recKey54 (rec1SortedArr K l p) := by
        change _ = (recKey54 ∘ rec1SortedArr K l) p
        dsimp [rec1SortedArr, kIn]
        exact (congrFun (br.sort_of_key_comp bitsToNat recKey54 (dOccOf K) true (rec1InitArr K l)) p).symm
      rw [hsort_k, rec1SortedArr_eq_occSpec comb br h1K l p] at hkq
      have hk_inj : ∀ q₁ q₂ : Fin (arity (dOccOf K)), kIn q₁ = kIn q₂ → q₁ = q₂ := by
        intro q₁ q₂ hq12
        have hb := congrArg bitsToNat hq12
        dsimp [kIn] at hb
        by_cases h1 : q₁.1 < 2 * K <;> by_cases h2 : q₂.1 < 2 * K
        · rw [rec1InitArr_lt_key K l q₁ h1, rec1InitArr_lt_key K l q₂ h2,
            rec1KeyBits_eq_iff comb _ _ _ (hm_lt _) (hm_lt _) (by omega) (by omega)] at hb
          exact Fin.ext hb.2.2
        · rw [rec1InitArr_lt_key K l q₁ h1, rec1InitArr_ge_key K l q₂ h2,
            rec1KeyBits_eq_iff comb _ _ _ (hm_lt _) h1_lt (by omega) (by omega)] at hb
          omega
        · rw [rec1InitArr_ge_key K l q₁ h1, rec1InitArr_lt_key K l q₂ h2,
            rec1KeyBits_eq_iff comb _ _ _ h1_lt (hm_lt _) (by omega) (by omega)] at hb
          omega
        · rw [rec1InitArr_ge_key K l q₁ h1, rec1InitArr_ge_key K l q₂ h2,
            rec1KeyBits_eq_iff comb _ _ _ h1_lt h1_lt (by omega) (by omega)] at hb
          exact Fin.ext hb.2.2
      by_cases hp : p.1 < 2 * K
      · rw [dif_pos hp] at hkq
        have hqeq := hk_inj _ q hkq
        subst hqeq
        let L_occ := occSortedList (2 * K) l
        have hL_len : L_occ.length = 2 * K := occSortedList_length (2 * K) l
        let r := L_occ[p.1]'(by rw [hL_len]; exact hp)
        have hrf := occSortedList_mem_fields (List.getElem_mem (by rw [hL_len]; exact hp : p.1 < L_occ.length))
        dsimp only [yP, scanOccPay, occRoutedPay, occBitsFn]
        change (if p.1 < 2 * K then (if p.1 ≤ 2 * K - 1 ∧ r.1 = true then natToBits (wOf K) (seqScanOcc L_occ p.1) else fun _ => false) else fun _ => false) =
          if r.2.2.1 < 2 * K then
            (if 2 ≤ runOffset l ⟨r.2.2.1, r.2.2.isLt⟩ then natToBits (wOf K) (runOcc l ⟨r.2.2.1, r.2.2.isLt⟩)
              else fun _ => false)
          else fun _ => false
        rw [if_pos hp, if_pos r.2.2.isLt]
        have hp_le : p.1 ≤ 2 * K - 1 := by omega
        simp only [hp_le, true_and]
        have hidx_eq : (⟨r.2.2.1, r.2.2.isLt⟩ : Fin (2 * K)) = r.2.2 := Fin.ext rfl
        rw [hidx_eq]
        by_cases hr1 : r.1 = true
        · have h2le : 2 ≤ runOffset l r.2.2 := by
            have := hrf.1; rw [hr1] at this; exact of_decide_eq_true this.symm
          rw [if_pos hr1, if_pos h2le]
          exact congrArg (natToBits (wOf K))
            (comb.seqScanOcc_eq_runOcc (2 * K) l p.1 (by rw [hL_len]; exact hp) hr1)
        · have hr1f : r.1 = false := Bool.eq_false_iff.mpr hr1
          have hnot2 : ¬ 2 ≤ runOffset l r.2.2 := by
            intro h2; exact hr1 (by rw [hrf.1]; exact decide_eq_true h2)
          simp [hr1f, hnot2]
      · rw [dif_neg hp] at hkq
        have hqeq := hk_inj p q hkq
        subst hqeq
        dsimp [yP, scanOccPay, occRoutedPay]
        rw [dif_neg hp, dif_neg hp]
    intro q
    exact br.unrouteSort_rel_sort bitsToNat (dOccOf K) true kIn yP R hsortR q q rfl
  dsimp only [unrouteRec1Circ]
  have hact := act_mapWires_ket_singleton _ _ z _ (by rw [hcomp]; exact hunr_spec)
  rw [hact]
  congr 1
  have harr_eq : (fun q => Fin.append (kIn q) (unrouteSort (dOccOf K) (sortTrace bitsToNat (dOccOf K) true kIn) yP q)) =
      rec1WithOccArr K l := funext fun q => by dsimp [rec1WithOccArr, kIn]; rw [hrel q]
  rw [harr_eq]
  exact updateOn_packDTA54_eq_two (eRec1Reg as n K d) (eTr1 as n K d) (eSort1Anc as n K d)
    (eRec1Reg_disjoint_eTr1 as n K d) (eRec1Reg_disjoint_eSort1Anc as n K d)
    (eTr1_disjoint_eSort1Anc as n K d) z hanc (rec1WithOccArr K l) (fun _ => false)

lemma swapOccOutCirc_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) :
    (swapOccOutCirc as arith n K d h1K).size ≤ (2 * K) * (3 * wOf K) := by
  dsimp [swapOccOutCirc]
  have h := LayeredCircuit_seqList_size_le
    ((List.range (2 * K)).map fun i =>
      if hi : i < 2 * K then
        let q : Fin (arity (dOccOf K)) := ⟨i, by have := two_K_le_arity_dOcc (K := K); omega⟩
        (arith.swapRegCircuit (wOf K)).mapWires
          (combineEmb (eRec1Occ as n K d q) (eOccSlot as n K d ⟨i, hi⟩)
            (eRec1Occ_disjoint_eOccSlot as n K d q ⟨i, hi⟩))
      else LayeredCircuit.id _)
    (3 * wOf K)
    (by
      intro lc hlc
      simp only [List.mem_map] at hlc
      rcases hlc with ⟨i, _, rfl⟩
      split_ifs
      · rw [LayeredCircuit.mapWires_size, arith.swapRegCircuit_size]
      · simp)
  simpa using h

lemma act_swapOccOutCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) (z : Qubits (totWiresDef as n K d))
    (hzRec : z ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (rec1WithOccArr K l))
    (hzOcc : z ∘ ancEmb as n K d ⟨2, by decide⟩ = fun _ => false) :
    act (swapOccOutCirc as arith n K d h1K).unitary (ket z) =
      ket (updateOn (eOccReg as n K d)
        (updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1InitArr K l)))
        (flatReg (2 * K) (wOf K) (occBitsFn K l))) := by
  have h2K : 2 * K ≤ arity (dOccOf K) := two_K_le_arity_dOcc
  let arrP (p : ℕ) (q : Fin (arity (dOccOf K))) : Qubits (wR1Occ K) :=
    if q.1 < p then rec1InitArr K l q else rec1WithOccArr K l q
  let occP (p : ℕ) (i : Fin (2 * K)) : Qubits (wOf K) :=
    if i.1 < p then occBitsFn K l i else fun _ => false
  let st (p : ℕ) : Qubits (totWiresDef as n K d) :=
    updateOn (eOccReg as n K d)
      (updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (arrP p)))
      (flatReg (2 * K) (wOf K) (occP p))
  have h0 : st 0 = z := by
    dsimp only [st]
    have ha0 : arrP 0 = rec1WithOccArr K l := funext fun q => by dsimp [arrP]
    have ho0 : occP 0 = fun _ => fun _ => false := funext fun i => by dsimp [occP]
    rw [ha0, ho0]
    have hnoop1 : updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1WithOccArr K l)) = z :=
      updateOn_noop _ _ _ hzRec
    rw [hnoop1]
    apply updateOn_noop
    funext idx
    rcases finProdFinEquiv.surjective idx with ⟨⟨i, b⟩, rfl⟩
    have hzo : z (eOccReg as n K d (finProdFinEquiv (i, b))) = false := congrFun hzOcc _
    simp [hzo, flatReg]
  conv_lhs => rw [← h0]
  dsimp [swapOccOutCirc]
  have hloop := act_seqList_range st
    (fun i => if hi : i < 2 * K then
      let q : Fin (arity (dOccOf K)) := ⟨i, by have := two_K_le_arity_dOcc (K := K); omega⟩
      (arith.swapRegCircuit (wOf K)).mapWires
        (combineEmb (eRec1Occ as n K d q) (eOccSlot as n K d ⟨i, hi⟩)
          (eRec1Occ_disjoint_eOccSlot as n K d q ⟨i, hi⟩))
      else LayeredCircuit.id _)
    (2 * K)
    (fun i hi => by
      rw [dif_pos hi]
      let qF : Fin (arity (dOccOf K)) := ⟨i, by omega⟩
      let iF : Fin (2 * K) := ⟨i, hi⟩
      rw [act_swapRegOn arith]
      have hst_occ : st i ∘ eOccReg as n K d = flatReg (2 * K) (wOf K) (occP i) := updateOn_comp_emb _ _ _
      have hst_rec : st i ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (arrP i) := by
        dsimp only [st]
        rw [updateOn_comp_disjoint _ _ (fun a b h => eRec1Reg_disjoint_eOccReg as n K d b a h.symm),
          updateOn_comp_emb]
      have hv_recOcc : st i ∘ eRec1Occ as n K d qF = occBitsFn K l iF := by
        have h := comp_ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
          (st i) (arrP i) hst_rec qF (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega)
        change st i ∘ eRec1Occ as n K d qF = _ at h
        rw [h]
        dsimp only [arrP, qF]; rw [if_neg (Nat.lt_irrefl i)]
        funext b
        have hb : sliceEmb (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega) b =
            Fin.natAdd (wK1Occ K) b := Fin.ext (by simp)
        rw [Function.comp_apply, hb]
        dsimp only [rec1WithOccArr]; rw [Fin.append_right]
        dsimp only [occRoutedPay]; rw [dif_pos hi]
      have hv_occSlot : st i ∘ eOccSlot as n K d iF = fun _ => false := by
        funext b
        have := congrFun hst_occ (finProdFinEquiv (iF, b))
        simpa [eOccSlot, flatReg, Function.comp_apply, occP, iF] using this
      rw [hv_recOcc, hv_occSlot]
      congr 1
      change updateOn (eOccSlot as n K d iF)
          (updateOn (ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) qF
            (wK1Occ K) (wOf K) _) (st i) (fun _ => false)) (occBitsFn K l iF) = st (i + 1)
      rw [updateOn_ancRegField_eq_slot, comp_ancRegSlot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K)
          (ancLen_3 n K d _) (st i) (arrP i) hst_rec qF]
      rw [updateOn_ancRegSlot_eq as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)
          (st i) (arrP i) hst_rec qF]
      change updateOn (eOccSlot as n K d iF) (updateOn (eRec1Reg as n K d) (st i) _) (occBitsFn K l iF) = st (i + 1)
      dsimp only [st]
      rw [updateOn_comm (eRec1Reg as n K d) (eOccReg as n K d) (eRec1Reg_disjoint_eOccReg as n K d)]
      rw [updateOn_idem]
      change updateOn ((slotInReg (2 * K) (wOf K) iF).trans (eOccReg as n K d))
          (updateOn (eOccReg as n K d)
            (updateOn (eRec1Reg as n K d) z
              (flatReg (arity (dOccOf K)) (wR1Occ K)
                (Function.update (arrP i) qF
                  (updateOn (sliceEmb (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega))
                    (arrP i qF) (fun _ => false)))))
            (flatReg (2 * K) (wOf K) (occP i))) (occBitsFn K l iF) = st (i + 1)
      rw [updateOn_slot_absorb (eOccReg as n K d) _ (occP i) iF (occBitsFn K l iF)]
      have harr_upd : Function.update (arrP i) qF
          (updateOn (sliceEmb (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega))
            (arrP i qF) (fun _ => false)) = arrP (i + 1) := by
        funext r
        by_cases hr : r = qF
        · subst hr; rw [Function.update_self]
          dsimp [arrP, qF]; rw [if_neg (Nat.lt_irrefl i), if_pos (Nat.lt_succ_self i)]
          exact rec1WithOccArr_lt_update K l qF hi
        · rw [Function.update_of_ne hr]
          have hne : r.1 ≠ i := fun hv => hr (Fin.ext hv)
          dsimp [arrP]; by_cases hlt : r.1 < i
          · simp [hlt, Nat.lt_trans hlt (Nat.lt_succ_self _)]
          · simp [hlt, show ¬ r.1 < i + 1 by omega]
      have hocc_upd : Function.update (occP i) iF (occBitsFn K l iF) = occP (i + 1) := by
        funext j
        by_cases hj : j = iF
        · subst hj; rw [Function.update_self]; simp [occP, iF]
        · rw [Function.update_of_ne hj]
          have hne : j.1 ≠ i := fun hv => hj (Fin.ext hv)
          dsimp [occP]; by_cases hlt : j.1 < i
          · simp [hlt, Nat.lt_trans hlt (Nat.lt_succ_self _)]
          · simp [hlt, show ¬ j.1 < i + 1 by omega]
      rw [harr_upd, hocc_upd])
  rw [hloop]
  congr 1
  dsimp only [st]
  have harr_all : arrP (2 * K) = rec1InitArr K l := funext fun q => by
    dsimp [arrP]; split_ifs with hq
    · rfl
    · exact rec1WithOccArr_ge_eq K l q hq
  have hocc_all : occP (2 * K) = occBitsFn K l := funext fun i => by dsimp [occP]; exact if_pos i.isLt
  rw [harr_all, hocc_all]

/-! #### 6.11 Combined Step 2 (`step2Circ`) and Step 1+2 (`step12Circ`) -/

lemma step2Circ_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (br : BitonicRouting54)
    (n K d : ℕ) (h1K : 1 ≤ K) :
    ((step2Circ as arith br n K d h1K).size : ℝ) ≤
      2 * (arity (dOccOf K) * (2 * wOf K + 2) : ℕ) +
      2 * (br.C_sort * (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1)) +
      ((2 * K - 1) * (49 * wOf K + 236) : ℕ) +
      ((2 * K) * (3 * wOf K) : ℕ) := by
  dsimp [step2Circ]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, LayeredCircuit.adj_size]
  have hpack : ((packRec1Circ as arith n K d).size : ℝ) ≤ (arity (dOccOf K) * (2 * wOf K + 2) : ℕ) :=
    Nat.cast_le.mpr (packRec1Circ_size as arith n K d)
  have hsort := sortRec1Circ_size as br n K d
  have hscan : ((scanOccCirc as arith n K d h1K).size : ℝ) ≤ ((2 * K - 1) * (49 * wOf K + 236) : ℕ) :=
    Nat.cast_le.mpr (scanOccCirc_size as arith n K d h1K)
  have hunr := unrouteRec1Circ_size as br n K d
  have hswap : ((swapOccOutCirc as arith n K d h1K).size : ℝ) ≤ ((2 * K) * (3 * wOf K) : ℕ) :=
    Nat.cast_le.mpr (swapOccOutCirc_size as arith n K d h1K)
  dsimp only [wR1Occ, wK1Occ, wP1Occ] at *
  push_cast at *
  linarith

lemma act_step2Circ (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (br : BitonicRouting54) (n K d : ℕ) (h1K : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1))
    (z : Qubits (totWiresDef as n K d))
    (hzM : z ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l))
    (hzAct : z ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l))
    (hz2 : z ∘ ancEmb as n K d ⟨2, by decide⟩ = fun _ => false)
    (hz3 : z ∘ ancEmb as n K d ⟨3, by decide⟩ = fun _ => false)
    (hz4 : z ∘ ancEmb as n K d ⟨4, by decide⟩ = fun _ => false)
    (hz7 : z ∘ ancEmb as n K d ⟨7, by decide⟩ = fun _ => false)
    (hz8 : z ∘ ancEmb as n K d ⟨8, by decide⟩ = fun _ => false)
    (hz9 : z ∘ ancEmb as n K d ⟨9, by decide⟩ = fun _ => false)
    (hz10 : z ∘ ancEmb as n K d ⟨10, by decide⟩ = fun _ => false) :
    act (step2Circ as arith br n K d h1K).unitary (ket z) =
      ket (updateOn (eOccReg as n K d) z (flatReg (2 * K) (wOf K) (occBitsFn K l))) := by
  dsimp only [step2Circ]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul,
    LayeredCircuit.id_unitary, act_one]
  -- 1. packRec1Circ
  rw [act_packRec1Circ comb as arith n K d z hzAct hzM hz3]
  set z1 := updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1InitArr K l))
  -- 2. sortRec1Circ
  have hz1_R : z1 ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (rec1InitArr K l) :=
    updateOn_comp_emb _ _ _
  have hz1_4 : z1 ∘ ancEmb as n K d ⟨4, by decide⟩ = fun _ => false := by
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨4, by decide⟩ (by decide))]
    exact hz4
  have hz1_7 : z1 ∘ ancEmb as n K d ⟨7, by decide⟩ = fun _ => false := by
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨7, by decide⟩ (by decide))]
    exact hz7
  rw [act_sortRec1Circ as br n K d z1 hz1_R hz1_4 hz1_7]
  have hz2_simp : updateOn (eTr1 as n K d)
        (updateOn (eRec1Reg as n K d) z1 (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1SortedArr K l)))
        (rec1SortTr K l) =
      updateOn (eTr1 as n K d)
        (updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1SortedArr K l)))
        (rec1SortTr K l) := by
    dsimp only [z1]; rw [updateOn_idem]
  rw [hz2_simp]
  set z2 := updateOn (eTr1 as n K d)
    (updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1SortedArr K l)))
    (rec1SortTr K l)
  -- 3. scanOccCirc
  have hz2_R : z2 ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (rec1SortedArr K l) := by
    dsimp only [z2]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec1Reg_disjoint_eTr1 as n K d b a h.symm),
      updateOn_comp_emb]
  have hz2_8 : z2 ∘ ancEmb as n K d ⟨8, by decide⟩ = fun _ => false := by
    dsimp only [z2]
    rw [updateOn_comp_disjoint _ _ (eTr1_disjoint_anc_other as n K d ⟨8, by decide⟩ (by decide))]
    rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨8, by decide⟩ (by decide))]
    exact hz8
  have hz2_9 : z2 ∘ ancEmb as n K d ⟨9, by decide⟩ = fun _ => false := by
    dsimp only [z2]
    rw [updateOn_comp_disjoint _ _ (eTr1_disjoint_anc_other as n K d ⟨9, by decide⟩ (by decide))]
    rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨9, by decide⟩ (by decide))]
    exact hz9
  have hz2_10 : z2 ∘ ancEmb as n K d ⟨10, by decide⟩ = fun _ => false := by
    dsimp only [z2]
    rw [updateOn_comp_disjoint _ _ (eTr1_disjoint_anc_other as n K d ⟨10, by decide⟩ (by decide))]
    rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨10, by decide⟩ (by decide))]
    exact hz10
  rw [act_scanOccCirc comb br as arith n K d h1K l z2 hz2_R hz2_8 hz2_9 hz2_10]
  have hz3_simp : updateOn (eRec1Reg as n K d) z2
        (flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l (2 * K - 1))) =
      updateOn (eTr1 as n K d)
        (updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l (2 * K - 1))))
        (rec1SortTr K l) := by
    dsimp only [z2]
    rw [← updateOn_comm (eTr1 as n K d) (eRec1Reg as n K d)
        (fun a b h => eRec1Reg_disjoint_eTr1 as n K d b a h.symm),
      updateOn_idem]
  rw [hz3_simp]
  set z3 := updateOn (eTr1 as n K d)
    (updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l (2 * K - 1))))
    (rec1SortTr K l)
  -- 4. unrouteRec1Circ
  have hz3_R : z3 ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (scanRecArr K l (2 * K - 1)) := by
    dsimp only [z3]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eRec1Reg_disjoint_eTr1 as n K d b a h.symm),
      updateOn_comp_emb]
  have hz3_Tr : z3 ∘ eTr1 as n K d = rec1SortTr K l := updateOn_comp_emb _ _ _
  have hz3_7 : z3 ∘ ancEmb as n K d ⟨7, by decide⟩ = fun _ => false := by
    dsimp only [z3]
    rw [updateOn_comp_disjoint _ _ (eTr1_disjoint_anc_other as n K d ⟨7, by decide⟩ (by decide))]
    rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨7, by decide⟩ (by decide))]
    exact hz7
  rw [act_unrouteRec1Circ comb br as n K d h1K l z3 hz3_R hz3_Tr hz3_7]
  have hz4_simp : updateOn (eTr1 as n K d)
        (updateOn (eRec1Reg as n K d) z3 (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1WithOccArr K l)))
        (fun _ => false) =
      updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1WithOccArr K l)) := by
    dsimp only [z3]
    rw [updateOn_comm (eRec1Reg as n K d) (eTr1 as n K d) (eRec1Reg_disjoint_eTr1 as n K d),
      updateOn_idem, updateOn_idem,
      updateOn_noop (eTr1 as n K d) _ _ (by
        rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_eTr1 as n K d)]
        funext j; exact congrFun hz4 _)]
  rw [hz4_simp]
  set z4 := updateOn (eRec1Reg as n K d) z (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1WithOccArr K l))
  -- 5. swapOccOutCirc
  have hz4_R : z4 ∘ eRec1Reg as n K d = flatReg (arity (dOccOf K)) (wR1Occ K) (rec1WithOccArr K l) :=
    updateOn_comp_emb _ _ _
  have hz4_2 : z4 ∘ ancEmb as n K d ⟨2, by decide⟩ = fun _ => false := by
    dsimp only [z4]
    rw [updateOn_comp_disjoint _ _ (eRec1Reg_disjoint_anc_other as n K d ⟨2, by decide⟩ (by decide))]
    exact hz2
  rw [act_swapOccOutCirc as arith n K d h1K l z4 hz4_R hz4_2]
  -- 6. (packRec1Circ).adj collapses everything to `updateOn eOccReg z ...`!
  let zOut := updateOn (eOccReg as n K d) z (flatReg (2 * K) (wOf K) (occBitsFn K l))
  have hzOut_act : zOut ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l) := by
    dsimp only [zOut]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_eActReg as n K d)]
    exact hzAct
  have hzOut_m : zOut ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l) := by
    dsimp only [zOut]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_eMReg as n K d)]
    exact hzM
  have hzOut_3 : zOut ∘ ancEmb as n K d ⟨3, by decide⟩ = fun _ => false := by
    dsimp only [zOut]
    rw [updateOn_comp_disjoint _ _ (eOccReg_disjoint_anc_other as n K d ⟨3, by decide⟩ (by decide))]
    exact hz3
  have hpack_out := act_packRec1Circ comb as arith n K d zOut hzOut_act hzOut_m hzOut_3
  have hz_match : updateOn (eOccReg as n K d)
        (updateOn (eRec1Reg as n K d) z4 (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1InitArr K l)))
        (flatReg (2 * K) (wOf K) (occBitsFn K l)) =
      updateOn (eRec1Reg as n K d) zOut (flatReg (arity (dOccOf K)) (wR1Occ K) (rec1InitArr K l)) := by
    dsimp only [z4, zOut]
    rw [updateOn_idem,
      updateOn_comm (eOccReg as n K d) (eRec1Reg as n K d) (fun a b h => eRec1Reg_disjoint_eOccReg as n K d b a h.symm)]
  rw [hz_match]
  exact act_adj_ket _ hpack_out

lemma step12Circ_size (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (br : BitonicRouting54)
    (n K d : ℕ) (h1K : 1 ≤ K) :
    ((step12Circ as arith br n K d h1K).size : ℝ) ≤
      (wOf K + (2 * K - 1) * (28 * sOf n + 42 * wOf K + 28) : ℕ) +
      2 * (arity (dOccOf K) * (2 * wOf K + 2) : ℕ) +
      2 * (br.C_sort * (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1)) +
      ((2 * K - 1) * (49 * wOf K + 236) : ℕ) +
      ((2 * K) * (3 * wOf K) : ℕ) := by
  dsimp [step12Circ]
  rw [LayeredCircuit.seq_size]
  have h1 : ((step1Circ as arith n K d h1K).size : ℝ) ≤
      (wOf K + (2 * K - 1) * (28 * sOf n + 42 * wOf K + 28) : ℕ) :=
    Nat.cast_le.mpr (step1Circ_size as arith n K d h1K)
  have h2 := step2Circ_size as arith br n K d h1K
  dsimp only [wR1Occ, wK1Occ, wP1Occ] at *
  push_cast at *
  linarith

lemma act_step12Circ (comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (br : BitonicRouting54) (n K d : ℕ) (h1K : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l)
    (z : Qubits (totWiresDef as n K d))
    (hzL : z ∘ eL as n K d = flatReg (2 * K) (sOf n) fun p => particleSym54 n (sOf n) (l p))
    (hzAnc : ∀ k : Fin 24, k.1 ≤ 10 → z ∘ ancEmb as n K d k = fun _ => false) :
    act (step12Circ as arith br n K d h1K).unitary (ket z) =
      ket (updateOn (eOccReg as n K d)
        (updateOn (eActReg as n K d)
          (updateOn (eMReg as n K d) z (flatReg (2 * K) (wOf K) (mBitsFn K l)))
          (flatReg (2 * K) 1 (actBitsFn K l)))
        (flatReg (2 * K) (wOf K) (occBitsFn K l))) := by
  dsimp only [step12Circ]
  rw [LayeredCircuit.seq_unitary, act_mul]
  rw [act_step1Circ comb as arith n K d h1K l hl z hzL
    (funext fun _ => congrFun (hzAnc ⟨0, by decide⟩ (by decide)) _)
    (funext fun _ => congrFun (hzAnc ⟨1, by decide⟩ (by decide)) _)
    (hzAnc ⟨5, by decide⟩ (by decide))
    (hzAnc ⟨6, by decide⟩ (by decide))
    (hzAnc ⟨10, by decide⟩ (by decide))]
  set z1 := updateOn (eActReg as n K d)
    (updateOn (eMReg as n K d) z (flatReg (2 * K) (wOf K) (mBitsFn K l)))
    (flatReg (2 * K) 1 (actBitsFn K l))
  have hz1_M : z1 ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l) := by
    dsimp only [z1]
    rw [updateOn_comp_disjoint _ _ (fun a b h => eMReg_disjoint_eActReg as n K d b a h.symm),
      updateOn_comp_emb]
  have hz1_A : z1 ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l) := updateOn_comp_emb _ _ _
  have hz1_other : ∀ k : Fin 24, 2 ≤ k.1 → k.1 ≤ 10 → z1 ∘ ancEmb as n K d k = fun _ => false := by
    intro k hk2 hk10
    dsimp only [z1]
    have hne1 : k ≠ ⟨1, by decide⟩ := fun h => by subst h; simp at hk2
    have hne0 : k ≠ ⟨0, by decide⟩ := fun h => by subst h; simp at hk2
    rw [updateOn_comp_disjoint _ _ (eActReg_disjoint_anc_other as n K d k hne1)]
    rw [updateOn_comp_disjoint _ _ (eMReg_disjoint_anc_other as n K d k hne0)]
    exact hzAnc k hk10
  exact act_step2Circ comb as arith br n K d h1K l z1 hz1_M hz1_A
    (hz1_other ⟨2, by decide⟩ (by decide) (by decide))
    (hz1_other ⟨3, by decide⟩ (by decide) (by decide))
    (hz1_other ⟨4, by decide⟩ (by decide) (by decide))
    (hz1_other ⟨7, by decide⟩ (by decide) (by decide))
    (hz1_other ⟨8, by decide⟩ (by decide) (by decide))
    (hz1_other ⟨9, by decide⟩ (by decide) (by decide))
    (hz1_other ⟨10, by decide⟩ (by decide) (by decide))

end HarmBucketWork54

open QuantumLTF.Membership.Supplement HarmBucketWork54 in
theorem solution : Nonempty QuantumLTF.Membership.Supplement.HarmBucketOcc54 :=
  ⟨{
    step12Circ_size := fun as arith br n K d h1K => step12Circ_size as arith br n K d h1K
    act_step12Circ := fun comb as arith br n K d h1K l hl z hzL hzAnc =>
      act_step12Circ comb as arith br n K d h1K l hl z hzL hzAnc
  }⟩
