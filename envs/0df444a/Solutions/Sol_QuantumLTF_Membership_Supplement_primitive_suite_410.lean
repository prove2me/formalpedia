-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.primitive_suite_410
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T06:15:12.715402+00:00
-- url     : https://prove2.me/submissions/cdb004fa-762f-41bb-ba99-4397818c27ea

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_coupledOp410
import Definitions.Def_QuantumLTF_Membership_Supplement_primitiveSuite410
import Theorems.Thm_QuantumLTF_Membership_Supplement_coupled_transducer_410

set_option autoImplicit false

namespace Thm410Bridge

open QAlgorithms QuantumLTF.Majority QuantumLTF.Membership QuantumLTF.Membership.Supplement
open Thm49Primitives Thm410Router

/-! ### Part 1: Bridge lemmas for `chCirc`, `eqCirc`, `hcCirc`, and `cnCirc` -/

private lemma packCH_zero (n : ℕ) (c : Bool) (x a : Qubits n) :
    CoupledOp410.packCH n n c x a 0 = c := by
  simp [CoupledOp410.packCH]

private lemma packCH_tgt (n : ℕ) (c : Bool) (x a : Qubits n) (i : Fin n) :
    CoupledOp410.packCH n n c x a ⟨1 + i.1, by have := i.isLt; omega⟩ = x i := by
  dsimp only [CoupledOp410.packCH]
  have hi := i.isLt
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1; ext; simp

private lemma packCH_anc (n : ℕ) (c : Bool) (x a : Qubits n) (j : Fin n) :
    CoupledOp410.packCH n n c x a (Fin.natAdd (1 + n) j) = a j := by
  dsimp only [CoupledOp410.packCH]
  rw [dif_neg (by simp), dif_neg (by simp)]
  congr 1; ext; simp

private lemma packCH_inj (n : ℕ) (c : Bool) :
    Function.Injective (fun y : Qubits n => CoupledOp410.packCH n n c y (fun _ => false)) := by
  intro y1 y2 h
  funext i
  have hi := congrFun h ⟨1 + i.1, by have := i.isLt; omega⟩
  simpa [packCH_tgt] using hi

private lemma eq_packCH_of (n : ℕ) (c : Bool) (w : Qubits (1 + n + n))
    (h0 : w 0 = c) (hanc : ∀ j : Fin n, w (Fin.natAdd (1 + n) j) = false) :
    w = CoupledOp410.packCH n n c (fun i : Fin n => w ⟨1 + i.1, by have := i.isLt; omega⟩)
      (fun _ => false) := by
  funext k
  dsimp only [CoupledOp410.packCH]
  by_cases hk0 : k.1 = 0
  · rw [dif_pos hk0]
    have hk : k = 0 := Fin.ext hk0
    rw [hk, h0]
  · rw [dif_neg hk0]
    by_cases hk1 : k.1 < 1 + n
    · rw [dif_pos hk1]
      congr 1; ext; simp; omega
    · rw [dif_neg hk1]
      have hkt := k.isLt
      have hk_eq : k = Fin.natAdd (1 + n) ⟨k.1 - (1 + n), by omega⟩ := Fin.ext (by simp; omega)
      rw [hk_eq]
      exact hanc _

private lemma bridge_ch_act (n : ℕ) (c : Bool) (x : Qubits n) :
    act (ctrlHadamardN n).toCircuit.unitary
        (ket (CoupledOp410.packCH n n c x (fun _ => false))) =
      if c then
        ∑ y : Qubits n, (hadamardN n y x) • ket (CoupledOp410.packCH n n true y (fun _ => false))
      else
        ket (CoupledOp410.packCH n n false x (fun _ => false)) := by
  classical
  let z : Qubits (1 + n + n) := CoupledOp410.packCH n n c x (fun _ => false)
  have hz_clean : ∀ j : Fin n, z (Fin.natAdd (1 + n) j) = false := fun j =>
    packCH_anc n c x (fun _ => false) j
  change act (ctrlHadamardN n).unitary (ket z) = _
  rw [act_ket_eq]
  have hz_zero : z (Fin.castAdd n ((0 : Fin (n + 1)).cast (Nat.add_comm n 1))) = c :=
    packCH_zero n c x (fun _ => false)
  have hz_tail : Fin.tail (fun i : Fin (n + 1) => z (Fin.castAdd n (i.cast (Nat.add_comm n 1)))) = x := by
    funext i
    rw [← packCH_tgt n c x (fun _ => false) i]
    dsimp [Fin.tail]
    congr 1
    exact Fin.ext (by simp; omega)
  have hentry_val : ∀ (y : Qubits n) (c' : Bool),
      (ctrlHadamardN n).unitary (CoupledOp410.packCH n n c' y (fun _ => false)) z =
        if c' = c then (if c then hadamardN n y x else if y = x then 1 else 0) else 0 := by
    intro y c'
    rw [ctrlHadamardN_implements n _ z hz_clean]
    have hy_clean : ∀ j : Fin n,
        CoupledOp410.packCH n n c' y (fun _ => false) (Fin.natAdd (1 + n) j) = false := fun j =>
      packCH_anc n c' y (fun _ => false) j
    rw [if_pos hy_clean]
    simp only [ctrlHadamardMat, Matrix.of_apply, controlledQubits, controlled, Matrix.submatrix_apply,
      Matrix.one_apply]
    have hy_zero : CoupledOp410.packCH n n c' y (fun _ => false)
        (Fin.castAdd n ((0 : Fin (n + 1)).cast (Nat.add_comm n 1))) = c' :=
      packCH_zero n c' y (fun _ => false)
    have hy_tail : Fin.tail (fun i : Fin (n + 1) =>
        CoupledOp410.packCH n n c' y (fun _ => false) (Fin.castAdd n (i.cast (Nat.add_comm n 1)))) = y := by
      funext i
      rw [← packCH_tgt n c' y (fun _ => false) i]
      dsimp [Fin.tail]
      congr 1
      exact Fin.ext (by simp; omega)
    simp only [hy_zero, hz_zero, hy_tail, hz_tail]
    by_cases hcc : c' = c
    · simp [hcc]
    · simp [hcc]
  cases c
  · rw [if_neg Bool.false_ne_true]
    rw [Finset.sum_eq_single z]
    · have hz1 : (ctrlHadamardN n).unitary z z = 1 := by
        simpa using hentry_val x false
      change (ctrlHadamardN n).unitary z z • ket z = ket z
      rw [hz1, one_smul]
    · intro w _ hne
      rw [ctrlHadamardN_implements n w z hz_clean]
      by_cases hw_clean : ∀ j : Fin n, w (Fin.natAdd (1 + n) j) = false
      · rw [if_pos hw_clean]
        simp only [ctrlHadamardMat, Matrix.of_apply, controlledQubits, controlled,
          Matrix.submatrix_apply, Matrix.one_apply, hz_zero, hz_tail]
        by_cases hw0 : w (Fin.castAdd n ((0 : Fin (n + 1)).cast (Nat.add_comm n 1))) = false
        · simp only [hw0, ↓reduceIte, Bool.false_eq_true]
          have hwt_ne : Fin.tail (fun i : Fin (n + 1) =>
              w (Fin.castAdd n (i.cast (Nat.add_comm n 1)))) ≠ x := by
            intro heq
            apply hne
            have hw0' : w 0 = false := hw0
            rw [eq_packCH_of n false w hw0' hw_clean]
            congr 1
            funext i
            have hi := congrFun heq i
            dsimp [Fin.tail] at hi
            rw [← hi]
            congr 1
            exact Fin.ext (by simp; omega)
          rw [if_neg hwt_ne, zero_smul]
        · rw [if_neg hw0, zero_smul]
      · rw [if_neg hw_clean, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_pos rfl]
    let img : Finset (Qubits (1 + n + n)) :=
      Finset.univ.image (fun y : Qubits n => CoupledOp410.packCH n n true y (fun _ => false))
    have hsub : (∑ w : Qubits (1 + n + n), (ctrlHadamardN n).unitary w z • ket w) =
        ∑ w ∈ img, (ctrlHadamardN n).unitary w z • ket w := by
      rw [← Finset.sum_subset (Finset.subset_univ img)]
      intro w _ hw_img
      rw [ctrlHadamardN_implements n w z hz_clean]
      by_cases hw_clean : ∀ j : Fin n, w (Fin.natAdd (1 + n) j) = false
      · rw [if_pos hw_clean]
        simp only [ctrlHadamardMat, Matrix.of_apply, controlledQubits, controlled,
          Matrix.submatrix_apply, hz_zero]
        by_cases hw0 : w (Fin.castAdd n ((0 : Fin (n + 1)).cast (Nat.add_comm n 1))) = true
        · exfalso
          apply hw_img
          rw [Finset.mem_image]
          refine ⟨fun i : Fin n => w ⟨1 + i.1, by have := i.isLt; omega⟩, Finset.mem_univ _, ?_⟩
          exact (eq_packCH_of n true w hw0 hw_clean).symm
        · rw [if_neg hw0, zero_smul]
      · rw [if_neg hw_clean, zero_smul]
    rw [hsub, Finset.sum_image (fun y1 _ y2 _ h => packCH_inj n true h)]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hy_val := hentry_val y true
    simp only [↓reduceIte] at hy_val
    rw [hy_val]

private lemma packEq_addr (L : ℕ) (addr : Qubits L) (tgt : Bool) (a : Qubits L) (i : Fin L) :
    CoupledOp410.packEq L L addr tgt a ⟨i.1, by have := i.isLt; omega⟩ = addr i := by
  dsimp only [CoupledOp410.packEq]
  have hi := i.isLt
  rw [dif_pos hi]

private lemma packEq_tgt (L : ℕ) (addr : Qubits L) (tgt : Bool) (a : Qubits L) :
    CoupledOp410.packEq L L addr tgt a ⟨L, by omega⟩ = tgt := by
  dsimp only [CoupledOp410.packEq]
  rw [dif_neg (by simp), dif_pos rfl]

private lemma packEq_anc (L : ℕ) (addr : Qubits L) (tgt : Bool) (a : Qubits L) (j : Fin L) :
    CoupledOp410.packEq L L addr tgt a (Fin.natAdd (L + 1) j) = a j := by
  dsimp only [CoupledOp410.packEq]
  have hj := j.isLt
  rw [dif_neg (by simp; omega), dif_neg (by simp; omega)]
  congr 1; ext; simp

private lemma packEq_inj (L : ℕ) (addr : Qubits L) :
    Function.Injective (fun b' : Bool => CoupledOp410.packEq L L addr b' (fun _ => false)) := by
  intro b1 b2 h
  have hb := congrFun h ⟨L, by omega⟩
  simpa [packEq_tgt] using hb

private lemma eq_packEq_of (L : ℕ) (addr : Qubits L) (y : Qubits (L + 1 + L))
    (haddr : ∀ i : Fin L, y ⟨i.1, by have := i.isLt; omega⟩ = addr i)
    (hanc : ∀ j : Fin L, y (Fin.natAdd (L + 1) j) = false) :
    y = CoupledOp410.packEq L L addr (y ⟨L, by omega⟩) (fun _ => false) := by
  funext k
  dsimp only [CoupledOp410.packEq]
  by_cases hk0 : k.1 < L
  · rw [dif_pos hk0]
    exact haddr ⟨k.1, hk0⟩
  · rw [dif_neg hk0]
    by_cases hk1 : k.1 = L
    · rw [dif_pos hk1]
      have hk_eq : k = ⟨L, by omega⟩ := Fin.ext hk1
      rw [hk_eq]
    · rw [dif_neg hk1]
      have hkt := k.isLt
      have hk_eq : k = Fin.natAdd (L + 1) ⟨k.1 - (L + 1), by omega⟩ := Fin.ext (by simp; omega)
      rw [hk_eq]
      exact hanc _

private lemma bridge_eq_act (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (addr : Qubits L) (tgt : Bool) :
    act (multiEqCtrl1 L pat U hU).toCircuit.unitary
        (ket (CoupledOp410.packEq L L addr tgt (fun _ => false))) =
      if addr = pat then
        ∑ b' : Bool, (U b' tgt) • ket (CoupledOp410.packEq L L addr b' (fun _ => false))
      else
        ket (CoupledOp410.packEq L L addr tgt (fun _ => false)) := by
  classical
  let z : Qubits (L + 1 + L) := CoupledOp410.packEq L L addr tgt (fun _ => false)
  have hz_clean : ∀ j : Fin L, z (Fin.natAdd (L + 1) j) = false := fun j =>
    packEq_anc L addr tgt (fun _ => false) j
  change act (multiEqCtrl1 L pat U hU).unitary (ket z) = _
  rw [act_ket_eq]
  have hz_addr : ∀ i : Fin L, z ⟨i.1, by omega⟩ = addr i := fun i =>
    packEq_addr L addr tgt (fun _ => false) i
  have hz_tgt : z ⟨L, by omega⟩ = tgt := packEq_tgt L addr tgt (fun _ => false)
  have hentry_val : ∀ b' : Bool,
      (multiEqCtrl1 L pat U hU).unitary (CoupledOp410.packEq L L addr b' (fun _ => false)) z =
        if addr = pat then U b' tgt else if b' = tgt then 1 else 0 := by
    intro b'
    rw [multiEqCtrl1_implements L pat U hU _ z hz_clean]
    have hy_clean : ∀ j : Fin L,
        CoupledOp410.packEq L L addr b' (fun _ => false) (Fin.natAdd (L + 1) j) = false := fun j =>
      packEq_anc L addr b' (fun _ => false) j
    rw [if_pos hy_clean]
    simp only [eqCtrlMat, Matrix.of_apply]
    have hy_addr : ∀ i : Fin L,
        CoupledOp410.packEq L L addr b' (fun _ => false) (Fin.castAdd L ⟨i.1, by omega⟩) =
        z (Fin.castAdd L ⟨i.1, by omega⟩) := fun i => by
      change CoupledOp410.packEq L L addr b' (fun _ => false) ⟨i.1, by have := i.isLt; omega⟩ =
        z ⟨i.1, by have := i.isLt; omega⟩
      rw [packEq_addr, hz_addr]
    have hy_tgt : CoupledOp410.packEq L L addr b' (fun _ => false) (Fin.castAdd L ⟨L, by omega⟩) = b' :=
      packEq_tgt L addr b' (fun _ => false)
    have hz_tgt' : z (Fin.castAdd L ⟨L, by omega⟩) = tgt := hz_tgt
    have hpat_iff : (∀ i : Fin L, z (Fin.castAdd L ⟨i.1, by omega⟩) = pat i) ↔ addr = pat := by
      constructor
      · intro h; funext i; simpa [hz_addr] using h i
      · intro h i; rw [← h]; exact hz_addr i
    rw [if_pos hy_addr]
    simp only [hy_tgt, hz_tgt']
    by_cases haddr : addr = pat
    · rw [if_pos (hpat_iff.mpr haddr), if_pos haddr]
    · rw [if_neg (mt hpat_iff.mp haddr), if_neg haddr]
  by_cases haddr : addr = pat
  · rw [if_pos haddr]
    let img : Finset (Qubits (L + 1 + L)) :=
      Finset.univ.image (fun b' : Bool => CoupledOp410.packEq L L addr b' (fun _ => false))
    have hsub : (∑ y : Qubits (L + 1 + L), (multiEqCtrl1 L pat U hU).unitary y z • ket y) =
        ∑ y ∈ img, (multiEqCtrl1 L pat U hU).unitary y z • ket y := by
      rw [← Finset.sum_subset (Finset.subset_univ img)]
      intro y _ hy_img
      rw [multiEqCtrl1_implements L pat U hU y z hz_clean]
      by_cases hy_clean : ∀ j : Fin L, y (Fin.natAdd (L + 1) j) = false
      · rw [if_pos hy_clean]
        simp only [eqCtrlMat, Matrix.of_apply]
        by_cases hy_addr : ∀ i : Fin L,
            y (Fin.castAdd L ⟨i.1, by omega⟩) = z (Fin.castAdd L ⟨i.1, by omega⟩)
        · exfalso
          apply hy_img
          rw [Finset.mem_image]
          refine ⟨y ⟨L, by omega⟩, Finset.mem_univ _, ?_⟩
          have hy_addr' : ∀ i : Fin L, y ⟨i.1, by have := i.isLt; omega⟩ = addr i := fun i => by
            simpa [hz_addr] using hy_addr i
          exact (eq_packEq_of L addr y hy_addr' hy_clean).symm
        · rw [if_neg hy_addr, zero_smul]
      · rw [if_neg hy_clean, zero_smul]
    rw [hsub, Finset.sum_image (fun b1 _ b2 _ h => packEq_inj L addr h)]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [hentry_val b', if_pos haddr]
  · rw [if_neg haddr]
    rw [Finset.sum_eq_single z]
    · have hz1 := hentry_val tgt
      rw [if_neg haddr, if_pos rfl] at hz1
      change (multiEqCtrl1 L pat U hU).unitary (CoupledOp410.packEq L L addr tgt (fun _ => false)) z • ket z = ket z
      rw [hz1, one_smul]
    · intro y _ hy_ne
      rw [multiEqCtrl1_implements L pat U hU y z hz_clean]
      by_cases hy_clean : ∀ j : Fin L, y (Fin.natAdd (L + 1) j) = false
      · rw [if_pos hy_clean]
        simp only [eqCtrlMat, Matrix.of_apply]
        by_cases hy_addr : ∀ i : Fin L,
            y (Fin.castAdd L ⟨i.1, by omega⟩) = z (Fin.castAdd L ⟨i.1, by omega⟩)
        · rw [if_pos hy_addr]
          have hnot_pat : ¬ ∀ i : Fin L, z (Fin.castAdd L ⟨i.1, by omega⟩) = pat i := by
            intro h; apply haddr; funext i; simpa [hz_addr] using h i
          rw [if_neg hnot_pat]
          have hne_tgt : y (Fin.castAdd L ⟨L, by omega⟩) ≠ z (Fin.castAdd L ⟨L, by omega⟩) := by
            intro h
            apply hy_ne
            have hy_addr' : ∀ i : Fin L, y ⟨i.1, by have := i.isLt; omega⟩ = addr i := fun i => by
              simpa [hz_addr] using hy_addr i
            have hy_tgt' : y ⟨L, by omega⟩ = tgt := by
              have hz_tgt' : z (Fin.castAdd L ⟨L, by omega⟩) = tgt := hz_tgt
              change y (Fin.castAdd L ⟨L, by omega⟩) = tgt
              rw [h, hz_tgt']
            rw [eq_packEq_of L addr y hy_addr' hy_clean, hy_tgt']
          rw [if_neg hne_tgt, zero_smul]
        · rw [if_neg hy_addr, zero_smul]
      · rw [if_neg hy_clean, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h

private lemma packHC_eq_addCases (n : ℕ) (x : Qubits n)
    (w : Qubits (hcEll n)) (a : Qubits (hammingAnc n)) :
    CoupledOp410.packHC n (Nat.clog 2 (n + 1)) (hammingAnc n) x w a =
      Fin.addCases (Fin.addCases x w) a := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · refine Fin.addCases (fun q => ?_) (fun b => ?_) i
    · simp [CoupledOp410.packHC, Fin.addCases_left, q.isLt]
    · dsimp only [CoupledOp410.packHC]
      have hnot : ¬ (Fin.castAdd (hammingAnc n) (Fin.natAdd n b)).1 < n := by simp
      have hlt : (Fin.castAdd (hammingAnc n) (Fin.natAdd n b)).1 < n + Nat.clog 2 (n + 1) := by
        simp
      rw [dif_neg hnot, dif_pos hlt, Fin.addCases_left, Fin.addCases_right]
      congr 1; ext; simp
  · dsimp only [CoupledOp410.packHC]
    rw [dif_neg (by simp; omega), dif_neg (by simp), Fin.addCases_right]
    congr 1; ext; simp

private lemma bridge_hc_act (n : ℕ) (x : Qubits n) :
    act (hammingCounter n).toCircuit.unitary
        (ket (CoupledOp410.packHC n (Nat.clog 2 (n + 1)) (hammingAnc n) x (fun _ => false) (fun _ => false))) =
      ket (CoupledOp410.packHC n (Nat.clog 2 (n + 1)) (hammingAnc n) x
        (CoupledOp410.natToBitsLSB (Nat.clog 2 (n + 1)) (hammingWeight x)) (fun _ => false)) := by
  rw [packHC_eq_addCases, packHC_eq_addCases]
  have hbits : CoupledOp410.natToBitsLSB (Nat.clog 2 (n + 1)) (hammingWeight x) =
      Thm49Primitives.natToBitsLSB (hcEll n) (Finset.univ.filter fun i : Fin n => x i = true).card :=
    rfl
  rw [hbits]
  exact act_hammingCounter_zero_ket n x

private lemma padZero_boolCons_eq_packCN (n : ℕ) (c : Bool) (x : Qubits n) :
    padZero (1 + n) n (boolCons c x) = CoupledOp410.packCN n n c x (fun _ => false) := by
  funext w
  dsimp only [CoupledOp410.packCN]
  by_cases hw0 : w.1 = 0
  · rw [dif_pos hw0]
    have hw : w = Fin.castAdd n 0 := Fin.ext hw0
    conv_lhs => rw [hw]
    rw [padZero_castAdd, boolCons_zero]
  · rw [dif_neg hw0]
    by_cases hw1 : w.1 < 1 + n
    · rw [dif_pos hw1]
      have hw : w = Fin.castAdd n (Fin.natAdd 1 ⟨w.1 - 1, by omega⟩) :=
        Fin.ext (by simp; omega)
      conv_lhs => rw [hw]
      rw [padZero_castAdd, boolCons_natAdd]
    · rw [dif_neg hw1]
      have hw : w = Fin.natAdd (1 + n) ⟨w.1 - (1 + n), by have := w.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      conv_lhs => rw [hw]
      rw [padZero_natAdd]

private lemma ctrlNotFn_boolCons (n : ℕ) (c : Bool) (x : Qubits n) :
    ctrlNotFn n (boolCons c x) = boolCons c (if c then (fun i => !(x i)) else x) := by
  funext i
  dsimp only [ctrlNotFn]
  by_cases hi0 : i.1 = 0
  · rw [if_pos hi0]
    have hi : i = 0 := Fin.ext hi0
    subst hi; simp [boolCons_zero]
  · rw [if_neg hi0]
    have hi : i = Fin.natAdd 1 ⟨i.1 - 1, by have := i.isLt; omega⟩ :=
      Fin.ext (by simp; omega)
    rw [hi, boolCons_natAdd, boolCons_natAdd, boolCons_zero]
    cases c <;> simp

private lemma bridge_cn_act (n : ℕ) (c : Bool) (x : Qubits n) :
    act (ctrlNotN n).toCircuit.unitary
        (ket (CoupledOp410.packCN n n c x (fun _ => false))) =
      ket (CoupledOp410.packCN n n c (if c then (fun i => !(x i)) else x) (fun _ => false)) := by
  rw [← padZero_boolCons_eq_packCN, ← padZero_boolCons_eq_packCN, ← ctrlNotFn_boolCons]
  exact act_ctrlNotN_ket n (boolCons c x)

/-! ### Part 2: Multiplexed `uTilde410Circ` from `coherentRouter`, `ctrlTwoLevelGate`, `ctrlLtPhaseSignGate`, and `ctrlU0DiagSignGate` -/

private lemma twoLevelMat_bridge {M : ℕ} (u v : Qubits (CoupledOp410.qW M)) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) :
    twoLevelMat (CoupledOp410.qW M) u v M2 = CoupledOp410.twoLevelMat u v huv M2 := by
  ext y z
  simp only [twoLevelMat, CoupledOp410.twoLevelMat, Matrix.of_apply]
  by_cases hyu : y = u
  · by_cases hzu : z = u
    · simp [hyu, hzu]
    · by_cases hzv : z = v
      · simp [hyu, hzv, huv]
      · have h1 : u ≠ z := Ne.symm hzu
        simp [hyu, hzu, hzv, h1]
  · by_cases hyv : y = v
    · by_cases hzu : z = u
      · simp [hyv, hzu, huv.symm]
      · by_cases hzv : z = v
        · simp [hyv, hzv, huv.symm]
        · have h1 : v ≠ z := Ne.symm hzv
          simp [hyv, hzu, hzv, h1]
    · by_cases hzu : z = u
      · have h1 : u ≠ y := Ne.symm hyu
        simp [hyu, hyv, hzu, h1]
      · by_cases hzv : z = v
        · have h1 : v ≠ y := Ne.symm hyv
          simp [hyu, hyv, hzv, h1]
        · by_cases hyz : y = z
          · rw [hyz]
            simp [hzu, hzv]
          · have h1 : z ≠ y := Ne.symm hyz
            simp [hyu, hyv, hzu, hzv, hyz, h1]

private lemma diagPhase_u0_eq (M : ℕ) :
    diagPhaseMat (u0DiagSignBool (CoupledOp410.qW M)) = CoupledOp410.D_mat410 M 0 := by
  ext y z
  simp only [diagPhaseMat, CoupledOp410.D_mat410, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz
    rw [if_pos rfl, if_pos rfl]
    have hsign : u0DiagSignBool (CoupledOp410.qW M) y =
        decide (2 ≤ CoupledOp410.bitsToNatLSB y ∧ CoupledOp410.bitsToNatLSB y % 2 = 0) := rfl
    simp only [hsign, CoupledOp410.diagSign410, ↓reduceIte]
    generalize CoupledOp410.bitsToNatLSB y = s
    by_cases hs : s ≤ 1
    · have hnot : ¬ 2 ≤ s := by omega
      simp [hs, hnot]
    · rw [if_neg hs]
      have hs2 : 2 ≤ s := by omega
      rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
      · have hodd : Odd (s + 1) := by
          obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
          exact ⟨q, by omega⟩
        simp [hs2, hmod, hodd.neg_one_pow]
      · have heven : Even (s + 1) := by
          have : (s + 1) % 2 = 0 := by omega
          exact even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero this)
        simp [hs2, hmod, heven.neg_one_pow]
  · rw [if_neg hyz, if_neg hyz]

private lemma diagPhase_dt_eq (M t : ℕ) (ht : 1 ≤ t) :
    diagPhaseMat (dtSignBool (CoupledOp410.qW M) (t / 2)) = CoupledOp410.D_mat410 M t := by
  ext y z
  simp only [diagPhaseMat, CoupledOp410.D_mat410, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz
    rw [if_pos rfl, if_pos rfl, dtSignBool_spec]
    have hbits : Thm49Primitives.bitsToNatLSB y = CoupledOp410.bitsToNatLSB y := rfl
    rw [hbits]
    simp only [CoupledOp410.diagSign410, show t ≠ 0 by omega, ↓reduceIte]
    generalize CoupledOp410.bitsToNatLSB y = s
    by_cases hs0 : s = 0
    · simp [hs0]
    · rw [if_neg hs0, if_neg hs0]
      by_cases hs1 : s = 1
      · rw [if_pos hs1, if_pos hs1]
        rcases Nat.mod_two_eq_zero_or_one (t / 2) with hm | hm
        · have hev : Even (t / 2) := even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero hm)
          simp [hm, hev.neg_one_pow]
        · have hod : Odd (t / 2) := Nat.odd_iff.mpr hm
          simp [hm, hod.neg_one_pow]
      · rw [if_neg hs1, if_neg hs1]
        rcases Nat.mod_two_eq_zero_or_one (min (s - 2) (t / 2)) with hm | hm
        · have hev : Even (min (s - 2) (t / 2)) := even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero hm)
          simp [hm, hev.neg_one_pow]
        · have hod : Odd (min (s - 2) (t / 2)) := Nat.odd_iff.mpr hm
          simp [hm, hod.neg_one_pow]
  · rw [if_neg hyz, if_neg hyz]

private lemma pauliX_mem_u : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, pauliX,
    Matrix.of_apply]
  cases a <;> cases b <;> norm_num

private lemma hadamard_mem_u : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hHs : star hadamard = hadamard := by
    ext a b; cases a <;> cases b <;> simp [hadamard, Matrix.star_apply, Complex.conj_ofReal]
  rw [hHs, hadamard_mul_self]

private noncomputable def uTildeLeaf (M : ℕ) (hM : 1 ≤ M) (t : ℕ) :
    LayeredCircuit (1 + CoupledOp410.qW M + (1 + (1 + CoupledOp410.qW M))) :=
  let qw := CoupledOp410.qW M
  let ancLeaf := 1 + (1 + qw)
  if t = 0 then
    let cD := ctrlU0DiagSignGate qw
    let cR := ctrlTwoLevelGate qw (CoupledOp410.modeKet M 0) (CoupledOp410.modeKet M 1)
      (CoupledOp410.modeKet_ne M 0 1 (by omega) (by omega) (by omega))
      pauliX pauliX_mem_u
    padAncClean (by omega : max (1 + qw) (1 + qw) ≤ ancLeaf) (seqClean cD cR)
  else if 2 * M + 1 < t then
    LayeredCircuit.id (1 + qw + ancLeaf)
  else if hodd : Odd t ∧ t / 2 < M then
    let j := t / 2
    have hj : 2 + j < M + 2 := by omega
    have hR2J : ∀ j', CoupledOp410.R2J j' ∈ Matrix.unitaryGroup Bool ℂ :=
      coupled_transducer_410.2.1
    let cD := ctrlLtPhaseSignGate qw j
    let cH := ctrlTwoLevelGate qw (CoupledOp410.modeKet M 1) (CoupledOp410.modeKet M (2 + j))
      (CoupledOp410.modeKet_ne M 1 (2 + j) (by omega) hj (by omega))
      hadamard hadamard_mem_u
    let cR := ctrlTwoLevelGate qw (CoupledOp410.modeKet M 0) (CoupledOp410.modeKet M 1)
      (CoupledOp410.modeKet_ne M 0 1 (by omega) (by omega) (by omega))
      (CoupledOp410.R2J j) (hR2J j)
    let rot := seqClean cH (seqClean cR cH)
    padAncClean (by omega : max ancLeaf (max (1 + qw) (max (1 + qw) (1 + qw))) ≤ ancLeaf)
      (seqClean cD rot)
  else if t = 2 * M + 1 then
    have hR2T : ∀ M', CoupledOp410.R2Top M' ∈ Matrix.unitaryGroup Bool ℂ :=
      coupled_transducer_410.2.2.1
    let cD := ctrlLtPhaseSignGate qw M
    let cR := ctrlTwoLevelGate qw (CoupledOp410.modeKet M 0) (CoupledOp410.modeKet M 1)
      (CoupledOp410.modeKet_ne M 0 1 (by omega) (by omega) (by omega))
      (CoupledOp410.R2Top M) (hR2T M)
    padAncClean (by omega : max ancLeaf (1 + qw) ≤ ancLeaf) (seqClean cD cR)
  else
    ctrlLtPhaseSignGate qw (t / 2)

private lemma clog2_add_one_le_bridge (q : ℕ) : Nat.clog 2 (q + 1) ≤ q + 1 := by
  rw [clog2_le_iff_le_pow]
  induction q with
  | zero => simp
  | succ k ih => rw [pow_succ']; omega

private lemma uTildeLeaf_size (M : ℕ) (hM : 1 ≤ M) (t : ℕ) :
    (uTildeLeaf M hM t).size ≤ 98 * CoupledOp410.qW M + 79 := by
  dsimp only [uTildeLeaf]
  split_ifs with h0 hgt hodd htop
  · simp only [padAncClean_size, seqClean_size]
    have h1 := ctrlU0DiagSignGate_size (CoupledOp410.qW M)
    have h2 := ctrlTwoLevelGate_size (CoupledOp410.qW M)
      (CoupledOp410.modeKet M 0) (CoupledOp410.modeKet M 1)
      (CoupledOp410.modeKet_ne M 0 1 (by omega) (by omega) (by omega))
      pauliX pauliX_mem_u
    omega
  · simp
  · simp only [padAncClean_size, seqClean_size]
    have h1 := ctrlLtPhaseSignGate_size (CoupledOp410.qW M) (t / 2)
    have h2 := ctrlTwoLevelGate_size (CoupledOp410.qW M)
      (CoupledOp410.modeKet M 1) (CoupledOp410.modeKet M (2 + t / 2))
      (CoupledOp410.modeKet_ne M 1 (2 + t / 2) (by omega) (by omega) (by omega))
      hadamard hadamard_mem_u
    have h3 := ctrlTwoLevelGate_size (CoupledOp410.qW M)
      (CoupledOp410.modeKet M 0) (CoupledOp410.modeKet M 1)
      (CoupledOp410.modeKet_ne M 0 1 (by omega) (by omega) (by omega))
      (CoupledOp410.R2J (t / 2)) (coupled_transducer_410.2.1 (t / 2))
    omega
  · simp only [padAncClean_size, seqClean_size]
    have h1 := ctrlLtPhaseSignGate_size (CoupledOp410.qW M) M
    have h2 := ctrlTwoLevelGate_size (CoupledOp410.qW M)
      (CoupledOp410.modeKet M 0) (CoupledOp410.modeKet M 1)
      (CoupledOp410.modeKet_ne M 0 1 (by omega) (by omega) (by omega))
      (CoupledOp410.R2Top M) (coupled_transducer_410.2.2.1 M)
    omega
  · have h1 := ctrlLtPhaseSignGate_size (CoupledOp410.qW M) (t / 2)
    omega

private lemma uTildeLeaf_depth (M : ℕ) (hM : 1 ≤ M) (t : ℕ) :
    (uTildeLeaf M hM t).depth ≤ 88 * CoupledOp410.qW M + 84 := by
  dsimp only [uTildeLeaf]
  split_ifs with h0 hgt hodd htop
  · simp only [padAncClean_depth, seqClean_depth]
    have h1 := ctrlU0DiagSignGate_depth (CoupledOp410.qW M)
    have hc := clog2_add_one_le_bridge (CoupledOp410.qW M)
    have h2 := ctrlTwoLevelGate_depth_linear (CoupledOp410.qW M)
      (CoupledOp410.modeKet M 0) (CoupledOp410.modeKet M 1)
      (CoupledOp410.modeKet_ne M 0 1 (by omega) (by omega) (by omega))
      pauliX pauliX_mem_u
    omega
  · simp
  · simp only [padAncClean_depth, seqClean_depth]
    have h1 := ctrlLtPhaseSignGate_depth_linear (CoupledOp410.qW M) (t / 2)
    have h2 := ctrlTwoLevelGate_depth_linear (CoupledOp410.qW M)
      (CoupledOp410.modeKet M 1) (CoupledOp410.modeKet M (2 + t / 2))
      (CoupledOp410.modeKet_ne M 1 (2 + t / 2) (by omega) (by omega) (by omega))
      hadamard hadamard_mem_u
    have h3 := ctrlTwoLevelGate_depth_linear (CoupledOp410.qW M)
      (CoupledOp410.modeKet M 0) (CoupledOp410.modeKet M 1)
      (CoupledOp410.modeKet_ne M 0 1 (by omega) (by omega) (by omega))
      (CoupledOp410.R2J (t / 2)) (coupled_transducer_410.2.1 (t / 2))
    omega
  · simp only [padAncClean_depth, seqClean_depth]
    have h1 := ctrlLtPhaseSignGate_depth_linear (CoupledOp410.qW M) M
    have h2 := ctrlTwoLevelGate_depth_linear (CoupledOp410.qW M)
      (CoupledOp410.modeKet M 0) (CoupledOp410.modeKet M 1)
      (CoupledOp410.modeKet_ne M 0 1 (by omega) (by omega) (by omega))
      (CoupledOp410.R2Top M) (coupled_transducer_410.2.2.1 M)
    omega
  · have h1 := ctrlLtPhaseSignGate_depth_linear (CoupledOp410.qW M) (t / 2)
    omega

private lemma uTildeLeaf_implements (M : ℕ) (hM : 1 ≤ M) (t : ℕ) :
    (uTildeLeaf M hM t).ImplementsOnClean (ctrlBlockMat (CoupledOp410.U_op410 M t)) := by
  dsimp only [uTildeLeaf]
  split_ifs with h0 hgt hodd htop
  · subst h0
    have hU0 : CoupledOp410.U_op410 M 0 = CoupledOp410.R_mat410 M 0 * CoupledOp410.D_mat410 M 0 := by
      simp [CoupledOp410.U_op410]
    rw [hU0, ctrlBlockMat_mul]
    apply padAncClean_implements
    apply seqClean_implements
    · rw [← diagPhase_u0_eq M]
      exact ctrlU0DiagSignGate_implements (CoupledOp410.qW M)
    · have hR0 : CoupledOp410.R_mat410 M 0 =
          twoLevelMat (CoupledOp410.qW M) (CoupledOp410.modeKet M 0) (CoupledOp410.modeKet M 1) pauliX := by
        simp only [CoupledOp410.R_mat410, ↓reduceIte]
        exact (twoLevelMat_bridge _ _ _ _).symm
      rw [hR0]
      exact ctrlTwoLevelGate_implements _ _ _ _ _ _
  · have hUgt : CoupledOp410.U_op410 M t = 1 := by simp [CoupledOp410.U_op410, hgt]
    rw [hUgt, ctrlBlockMat_one]
    intro y z hz
    simp only [LayeredCircuit.id_unitary, Matrix.one_apply]
    by_cases hy : ∀ j : Fin (1 + (1 + CoupledOp410.qW M)),
        y (Fin.natAdd (1 + CoupledOp410.qW M) j) = false
    · rw [if_pos hy]
      have heq : y = z ↔ (fun i => y (Fin.castAdd (1 + (1 + CoupledOp410.qW M)) i)) =
          (fun i => z (Fin.castAdd (1 + (1 + CoupledOp410.qW M)) i)) := by
        refine ⟨fun h => by subst h; rfl, fun h => funext fun k => Fin.addCases ?_ ?_ k⟩
        · intro i; exact congrFun h i
        · intro j; rw [hy j, hz j]
      by_cases hcast : (fun i => y (Fin.castAdd (1 + (1 + CoupledOp410.qW M)) i)) =
          (fun i => z (Fin.castAdd (1 + (1 + CoupledOp410.qW M)) i))
      · rw [if_pos hcast, if_pos (heq.mpr hcast)]
      · rw [if_neg hcast, if_neg (mt heq.mp hcast)]
    · rw [if_neg hy]
      have hne : y ≠ z := fun h => hy fun j => by rw [h]; exact hz j
      rw [if_neg hne]
  · have ht1 : 1 ≤ t := Nat.pos_of_ne_zero h0
    have hUt : CoupledOp410.U_op410 M t = CoupledOp410.R_mat410 M t * CoupledOp410.D_mat410 M t := by
      simp [CoupledOp410.U_op410, hgt]
    rw [hUt, ctrlBlockMat_mul]
    apply padAncClean_implements
    apply seqClean_implements
    · rw [← diagPhase_dt_eq M t ht1]
      exact ctrlLtPhaseSignGate_implements (CoupledOp410.qW M) (t / 2)
    · have hRt : CoupledOp410.R_mat410 M t =
          twoLevelMat (CoupledOp410.qW M) (CoupledOp410.modeKet M 1)
            (CoupledOp410.modeKet M (2 + t / 2)) hadamard *
          (twoLevelMat (CoupledOp410.qW M) (CoupledOp410.modeKet M 0)
            (CoupledOp410.modeKet M 1) (CoupledOp410.R2J (t / 2)) *
           twoLevelMat (CoupledOp410.qW M) (CoupledOp410.modeKet M 1)
            (CoupledOp410.modeKet M (2 + t / 2)) hadamard) := by
        simp only [CoupledOp410.R_mat410, if_neg h0, dif_pos hodd, Matrix.mul_assoc]
        rw [twoLevelMat_bridge, twoLevelMat_bridge]
      rw [hRt, ctrlBlockMat_mul, ctrlBlockMat_mul, ← Matrix.mul_assoc]
      refine seqClean_implements _ _ _ _ (ctrlTwoLevelGate_implements _ _ _ _ _ _)
        (seqClean_implements _ _ _ _ (ctrlTwoLevelGate_implements _ _ _ _ _ _)
          (ctrlTwoLevelGate_implements _ _ _ _ _ _))
  · subst htop
    have ht1 : 1 ≤ 2 * M + 1 := by omega
    have hUt : CoupledOp410.U_op410 M (2 * M + 1) =
        CoupledOp410.R_mat410 M (2 * M + 1) * CoupledOp410.D_mat410 M (2 * M + 1) := by
      simp [CoupledOp410.U_op410]
    have hdiv : (2 * M + 1) / 2 = M := by omega
    rw [hUt, ctrlBlockMat_mul]
    apply padAncClean_implements
    apply seqClean_implements
    · have hlt := ctrlLtPhaseSignGate_implements (CoupledOp410.qW M) ((2 * M + 1) / 2)
      rw [diagPhase_dt_eq M (2 * M + 1) ht1] at hlt
      rw [hdiv] at hlt
      exact hlt
    · have hRtop : CoupledOp410.R_mat410 M (2 * M + 1) =
          twoLevelMat (CoupledOp410.qW M) (CoupledOp410.modeKet M 0)
            (CoupledOp410.modeKet M 1) (CoupledOp410.R2Top M) := by
        have hnot_odd : ¬ (Odd (2 * M + 1) ∧ (2 * M + 1) / 2 < M) := by omega
        dsimp only [CoupledOp410.R_mat410]
        rw [if_neg (by omega), dif_neg hnot_odd, if_pos ⟨hM, rfl⟩]
        exact (twoLevelMat_bridge _ _ _ _).symm
      rw [hRtop]
      exact ctrlTwoLevelGate_implements _ _ _ _ _ _
  · have ht1 : 1 ≤ t := Nat.pos_of_ne_zero h0
    have hUt : CoupledOp410.U_op410 M t = CoupledOp410.D_mat410 M t := by
      have hRt : CoupledOp410.R_mat410 M t = 1 := by
        simp only [CoupledOp410.R_mat410, if_neg h0, dif_neg hodd]
        rw [if_neg (fun ⟨_, heq⟩ => htop heq)]
      simp [CoupledOp410.U_op410, hgt, hRt]
    rw [hUt, ← diagPhase_dt_eq M t ht1]
    exact ctrlLtPhaseSignGate_implements (CoupledOp410.qW M) (t / 2)

private def swapWFCEmb (ℓ q_w anc : ℕ) : Fin (ℓ + 1 + q_w + anc) ↪ Fin (1 + ℓ + q_w + anc) where
  toFun i :=
    if h1 : i.1 < ℓ then ⟨1 + i.1, by omega⟩
    else if h2 : i.1 = ℓ then ⟨0, by omega⟩
    else ⟨i.1, by have := i.isLt; omega⟩
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt
    have hval := congrArg Fin.val hab
    change (if h1 : a.1 < ℓ then (⟨1 + a.1, by omega⟩ : Fin (1 + ℓ + q_w + anc))
      else if h2 : a.1 = ℓ then ⟨0, by omega⟩ else ⟨a.1, by omega⟩).1 =
      (if h1 : b.1 < ℓ then (⟨1 + b.1, by omega⟩ : Fin (1 + ℓ + q_w + anc))
      else if h2 : b.1 = ℓ then ⟨0, by omega⟩ else ⟨b.1, by omega⟩).1 at hval
    split_ifs at hval <;> dsimp only at hval <;> exact Fin.ext (by omega)

private lemma swapWFCEmb_lt (ℓ q_w anc : ℕ) (i : Fin (ℓ + 1 + q_w + anc)) (h : i.1 < ℓ) :
    swapWFCEmb ℓ q_w anc i = ⟨1 + i.1, by omega⟩ := by
  change (if h1 : i.1 < ℓ then (⟨1 + i.1, _⟩ : Fin (1 + ℓ + q_w + anc))
    else if h2 : i.1 = ℓ then ⟨0, _⟩ else ⟨i.1, _⟩) = _
  rw [dif_pos h]

private lemma swapWFCEmb_eq (ℓ q_w anc : ℕ) (i : Fin (ℓ + 1 + q_w + anc)) (h : i.1 = ℓ) :
    swapWFCEmb ℓ q_w anc i = ⟨0, by omega⟩ := by
  change (if h1 : i.1 < ℓ then (⟨1 + i.1, _⟩ : Fin (1 + ℓ + q_w + anc))
    else if h2 : i.1 = ℓ then ⟨0, _⟩ else ⟨i.1, _⟩) = _
  rw [dif_neg (by omega), dif_pos h]

private lemma swapWFCEmb_gt (ℓ q_w anc : ℕ) (i : Fin (ℓ + 1 + q_w + anc)) (h1 : ¬ i.1 < ℓ) (h2 : i.1 ≠ ℓ) :
    swapWFCEmb ℓ q_w anc i = ⟨i.1, by have := i.isLt; omega⟩ := by
  change (if h1 : i.1 < ℓ then (⟨1 + i.1, _⟩ : Fin (1 + ℓ + q_w + anc))
    else if h2 : i.1 = ℓ then ⟨0, _⟩ else ⟨i.1, _⟩) = _
  rw [dif_neg h1, dif_neg h2]

private lemma mem_range_swapWFCEmb (ℓ q_w anc : ℕ) (i : Fin (1 + ℓ + q_w + anc)) :
    i ∈ Set.range (swapWFCEmb ℓ q_w anc) := by
  have hi_lt : i.1 < ℓ + 1 + q_w + anc := by have := i.isLt; omega
  by_cases h0 : i.1 = 0
  · refine ⟨⟨ℓ, by omega⟩, ?_⟩
    rw [swapWFCEmb_eq ℓ q_w anc ⟨ℓ, by omega⟩ rfl]
    exact Fin.ext h0.symm
  · by_cases h1 : i.1 < 1 + ℓ
    · refine ⟨⟨i.1 - 1, by omega⟩, ?_⟩
      rw [swapWFCEmb_lt ℓ q_w anc ⟨i.1 - 1, by omega⟩ (by simp; omega)]
      exact Fin.ext (by simp; omega)
    · refine ⟨⟨i.1, by omega⟩, ?_⟩
      rw [swapWFCEmb_gt ℓ q_w anc ⟨i.1, by omega⟩ (by simp; omega) (by simp; omega)]

private lemma packUTilde410_comp_swapWFC (M n' h_tree anc_leaf : ℕ)
    (fc : Bool) (w : Qubits (Nat.clog 2 (n' + 1))) (mode : Qubits (CoupledOp410.qW M)) :
    CoupledOp410.packUTilde410 M n' (routerAnc (Nat.clog 2 (n' + 1)) (CoupledOp410.qW M) h_tree anc_leaf)
        fc w mode (fun _ => false) ∘
      swapWFCEmb (Nat.clog 2 (n' + 1)) (CoupledOp410.qW M)
        (routerAnc (Nat.clog 2 (n' + 1)) (CoupledOp410.qW M) h_tree anc_leaf) =
      padZero (routerMain (Nat.clog 2 (n' + 1)) (CoupledOp410.qW M))
        (routerAnc (Nat.clog 2 (n' + 1)) (CoupledOp410.qW M) h_tree anc_leaf)
        (packRouterMain w fc mode) := by
  let ℓ := Nat.clog 2 (n' + 1)
  let q_w := CoupledOp410.qW M
  let anc := routerAnc ℓ q_w h_tree anc_leaf
  funext i
  rw [Function.comp_apply]
  have hi := i.isLt
  by_cases h1 : i.1 < ℓ
  · rw [swapWFCEmb_lt ℓ q_w anc i h1]
    have hcast : i = Fin.castAdd anc ⟨i.1, by change i.1 < ℓ + 1 + q_w; omega⟩ := rfl
    conv_rhs => rw [hcast]
    rw [padZero_castAdd]
    dsimp only [CoupledOp410.packUTilde410, packRouterMain]
    rw [dif_neg (by omega), dif_pos (by omega), dif_pos h1]
    congr 1; exact Fin.ext (by simp)
  · by_cases h2 : i.1 = ℓ
    · rw [swapWFCEmb_eq ℓ q_w anc i h2]
      have hcast : i = Fin.castAdd anc ⟨ℓ, by change ℓ < ℓ + 1 + q_w; omega⟩ := Fin.ext h2
      conv_rhs => rw [hcast]
      rw [padZero_castAdd]
      dsimp only [CoupledOp410.packUTilde410, packRouterMain]
      rw [dif_pos rfl, dif_neg (by omega), dif_pos rfl]
    · rw [swapWFCEmb_gt ℓ q_w anc i h1 h2]
      by_cases h3 : i.1 < ℓ + 1 + q_w
      · have hcast : i = Fin.castAdd anc ⟨i.1, h3⟩ := rfl
        conv_rhs => rw [hcast]
        rw [padZero_castAdd]
        dsimp only [CoupledOp410.packUTilde410, packRouterMain]
        rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega), dif_neg h1, dif_neg h2]
        congr 1; exact Fin.ext (by simp; omega)
      · have hnat : i = Fin.natAdd (routerMain ℓ q_w)
            ⟨i.1 - (ℓ + 1 + q_w), by change i.1 < ℓ + 1 + q_w + anc at hi; omega⟩ :=
          Fin.ext (by change i.1 = (ℓ + 1 + q_w) + (i.1 - (ℓ + 1 + q_w)); omega)
        conv_rhs => rw [hnat]
        rw [padZero_natAdd]
        dsimp only [CoupledOp410.packUTilde410]
        rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

private noncomputable def uTildeRouter (M n' : ℕ) (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n') :
    LayeredCircuit (1 + Nat.clog 2 (n' + 1) + CoupledOp410.qW M +
      routerAnc (Nat.clog 2 (n' + 1)) (CoupledOp410.qW M) (Nat.clog 2 (2 * M + 2))
        (1 + (1 + CoupledOp410.qW M))) :=
  let ℓ := Nat.clog 2 (n' + 1)
  let q_w := CoupledOp410.qW M
  let h_tree := Nat.clog 2 (2 * M + 2)
  let anc_leaf := 1 + (1 + q_w)
  let h_le : h_tree ≤ ℓ := Nat.clog_mono_right 2 (by omega)
  let leaves : Fin (2 ^ h_tree) → LayeredCircuit (1 + q_w + anc_leaf) := fun t => uTildeLeaf M hM t.1
  (coherentRouter ℓ q_w h_tree anc_leaf h_le leaves).mapWires (swapWFCEmb ℓ q_w (routerAnc ℓ q_w h_tree anc_leaf))

private lemma two_pow_clog2_le_two_mul_pred {x : ℕ} (hx : 2 ≤ x) :
    2 ^ Nat.clog 2 x ≤ 2 * (x - 1) := by
  have hk_pos : 1 ≤ Nat.clog 2 x := by
    by_contra h
    have h0 : Nat.clog 2 x = 0 := by omega
    have hle : x ≤ 2 ^ 0 := clog2_le_iff_le_pow.mp (le_of_eq h0)
    omega
  have hlt : 2 ^ (Nat.clog 2 x - 1) < x := by
    by_contra hge
    have hck : Nat.clog 2 x ≤ Nat.clog 2 x - 1 := clog2_le_iff_le_pow.mpr (by omega)
    omega
  have hpow : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk_pos, pow_succ']
  omega

private lemma uTildeRouter_size (M n' : ℕ) (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n') (hn3 : 3 ≤ n') :
    ((uTildeRouter M n' hM hle).size : ℝ) ≤ (800 / Real.log 2) * n' * Real.log n' := by
  let ℓ := Nat.clog 2 (n' + 1)
  let q_w := CoupledOp410.qW M
  let h_tree := Nat.clog 2 (2 * M + 2)
  let anc_leaf := 1 + (1 + q_w)
  have h_le : h_tree ≤ ℓ := Nat.clog_mono_right 2 (by omega)
  have hqw_le : q_w ≤ ℓ := Nat.clog_mono_right 2 (by omega)
  have hℓ2 : 2 ≤ ℓ := by
    by_contra hlt
    have h1 : ℓ ≤ 1 := by omega
    have hpow : n' + 1 ≤ 2 ^ 1 := clog2_le_iff_le_pow.mp h1
    omega
  have hpow_le : 2 ^ h_tree ≤ 2 * n' := by
    have h := two_pow_clog2_le_two_mul_pred (by omega : 2 ≤ 2 * M + 2)
    change 2 ^ Nat.clog 2 (2 * M + 2) ≤ 2 * n'
    omega
  have hrout := coherentRouter_size_le ℓ q_w h_tree anc_leaf (98 * q_w + 79) h_le
    (fun t => uTildeLeaf M hM t.1) (fun t => uTildeLeaf_size M hM t.1)
  have hsize_eq : (uTildeRouter M n' hM hle).size =
      (coherentRouter ℓ q_w h_tree anc_leaf h_le (fun t => uTildeLeaf M hM t.1)).size :=
    LayeredCircuit.mapWires_size _ _
  have hnat_bound : (uTildeRouter M n' hM hle).size ≤ 400 * n' * ℓ := by
    have ha1 : 2 ^ h_tree - 1 ≤ 2 * n' := by omega
    have hb1 : q_w + 1 ≤ 2 * ℓ := by dsimp only [q_w, ℓ] at hqw_le hℓ2 ⊢; omega
    have h2 : 16 * (2 ^ h_tree - 1) * (q_w + 1) ≤ 64 * n' * ℓ :=
      calc 16 * (2 ^ h_tree - 1) * (q_w + 1)
          ≤ 16 * (2 * n') * (2 * ℓ) := by gcongr
        _ = 64 * n' * ℓ := by ring
    have ha3 : 98 * q_w + 79 ≤ 138 * ℓ := by dsimp only [q_w, ℓ] at hqw_le hℓ2 ⊢; omega
    have h3 : 2 ^ h_tree * (98 * q_w + 79) ≤ 276 * n' * ℓ :=
      calc 2 ^ h_tree * (98 * q_w + 79)
          ≤ (2 * n') * (138 * ℓ) := by gcongr
        _ = 276 * n' * ℓ := by ring
    have h4 : 24 * (ℓ + 2) ≤ 48 * n' * ℓ :=
      calc 24 * (ℓ + 2) ≤ 24 * (2 * ℓ) := by omega
        _ = 48 * 1 * ℓ := by ring
        _ ≤ 48 * n' * ℓ := by gcongr; omega
    have hsum : 48 * n' * ℓ + 64 * n' * ℓ + 276 * n' * ℓ ≤ 400 * n' * ℓ := by
      have h1_eq : 48 * n' * ℓ + 64 * n' * ℓ + 276 * n' * ℓ = 388 * (n' * ℓ) := by ring
      have h2_eq : 400 * n' * ℓ = 400 * (n' * ℓ) := by ring
      omega
    calc (uTildeRouter M n' hM hle).size
        = (coherentRouter ℓ q_w h_tree anc_leaf h_le (fun t => uTildeLeaf M hM t.1)).size := hsize_eq
      _ ≤ 24 * (ℓ + 2) + 16 * (2 ^ h_tree - 1) * (q_w + 1) + 2 ^ h_tree * (98 * q_w + 79) := hrout
      _ ≤ 48 * n' * ℓ + 64 * n' * ℓ + 276 * n' * ℓ := by gcongr
      _ ≤ 400 * n' * ℓ := hsum
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ge : 1 ≤ Real.log n' / Real.log 2 := by
    rw [one_le_div hlog2_pos]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n'))
  have hclog := clog2_succ_le_real_log (by omega : 1 ≤ n')
  have hℓ_real : (ℓ : ℝ) ≤ (2 / Real.log 2) * Real.log n' := by
    calc (ℓ : ℝ) ≤ Real.log n' / Real.log 2 + 1 := hclog
      _ ≤ Real.log n' / Real.log 2 + Real.log n' / Real.log 2 := by linarith
      _ = (2 / Real.log 2) * Real.log n' := by ring
  have hcast : ((uTildeRouter M n' hM hle).size : ℝ) ≤ 400 * (n' : ℝ) * (ℓ : ℝ) := by
    exact_mod_cast hnat_bound
  have hn0 : (0 : ℝ) ≤ 400 * (n' : ℝ) := by positivity
  calc ((uTildeRouter M n' hM hle).size : ℝ)
      ≤ 400 * (n' : ℝ) * (ℓ : ℝ) := hcast
    _ ≤ 400 * (n' : ℝ) * ((2 / Real.log 2) * Real.log n') := mul_le_mul_of_nonneg_left hℓ_real hn0
    _ = (800 / Real.log 2) * n' * Real.log n' := by ring

private noncomputable def uTildeDepthBound (M n' : ℕ) : ℕ :=
  let ℓ := Nat.clog 2 (n' + 1)
  let q_w := CoupledOp410.qW M
  let h_tree := Nat.clog 2 (2 * M + 2)
  20 * Nat.clog 2 (ℓ + 2) + 16 * h_tree + 2 * Nat.clog 2 (q_w + 1) + (88 * q_w + 84) + 6

private lemma uTildeDepthBound_real (M n' : ℕ) (_hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n') (hn3 : 3 ≤ n') :
    (uTildeDepthBound M n' : ℝ) ≤ (800 / Real.log 2) * Real.log n' := by
  let ℓ := Nat.clog 2 (n' + 1)
  let q_w := CoupledOp410.qW M
  let h_tree := Nat.clog 2 (2 * M + 2)
  have h_le : h_tree ≤ ℓ := Nat.clog_mono_right 2 (by omega)
  have hqw_le : q_w ≤ ℓ := Nat.clog_mono_right 2 (by omega)
  have hℓ2 : 2 ≤ ℓ := by
    by_contra hlt
    have h1 : ℓ ≤ 1 := by omega
    have hpow : n' + 1 ≤ 2 ^ 1 := clog2_le_iff_le_pow.mp h1
    omega
  have hc1 : Nat.clog 2 (ℓ + 2) ≤ ℓ + 2 := clog2_add_one_le_bridge (ℓ + 1)
  have hc2 : Nat.clog 2 (q_w + 1) ≤ q_w + 1 := clog2_add_one_le_bridge q_w
  have hnat : uTildeDepthBound M n' ≤ 400 * ℓ := by
    change 20 * Nat.clog 2 (ℓ + 2) + 16 * h_tree + 2 * Nat.clog 2 (q_w + 1) + (88 * q_w + 84) + 6 ≤ 400 * ℓ
    omega
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ge : 1 ≤ Real.log n' / Real.log 2 := by
    rw [one_le_div hlog2_pos]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n'))
  have hclog := clog2_succ_le_real_log (by omega : 1 ≤ n')
  have hℓ_real : (ℓ : ℝ) ≤ (2 / Real.log 2) * Real.log n' := by
    calc (ℓ : ℝ) ≤ Real.log n' / Real.log 2 + 1 := hclog
      _ ≤ Real.log n' / Real.log 2 + Real.log n' / Real.log 2 := by linarith
      _ = (2 / Real.log 2) * Real.log n' := by ring
  have hcast : (uTildeDepthBound M n' : ℝ) ≤ 400 * (ℓ : ℝ) := by exact_mod_cast hnat
  calc (uTildeDepthBound M n' : ℝ)
      ≤ 400 * (ℓ : ℝ) := hcast
    _ ≤ 400 * ((2 / Real.log 2) * Real.log n') := mul_le_mul_of_nonneg_left hℓ_real (by norm_num)
    _ = (800 / Real.log 2) * Real.log n' := by ring

private lemma bridge_uTilde_act (M n' : ℕ) (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n')
    (fc : Bool) (w : Qubits (Nat.clog 2 (n' + 1))) (mode : Qubits (CoupledOp410.qW M)) :
    act (uTildeRouter M n' hM hle).toCircuit.unitary
        (ket (CoupledOp410.packUTilde410 M n'
          (routerAnc (Nat.clog 2 (n' + 1)) (CoupledOp410.qW M) (Nat.clog 2 (2 * M + 2))
            (1 + (1 + CoupledOp410.qW M)))
          fc w mode (fun _ => false))) =
      if fc then
        ∑ mode' : Qubits (CoupledOp410.qW M),
          (CoupledOp410.U_op410 M (CoupledOp410.bitsToNatLSB w) mode' mode) •
            ket (CoupledOp410.packUTilde410 M n'
              (routerAnc (Nat.clog 2 (n' + 1)) (CoupledOp410.qW M) (Nat.clog 2 (2 * M + 2))
                (1 + (1 + CoupledOp410.qW M)))
              true w mode' (fun _ => false))
      else
        ket (CoupledOp410.packUTilde410 M n'
          (routerAnc (Nat.clog 2 (n' + 1)) (CoupledOp410.qW M) (Nat.clog 2 (2 * M + 2))
            (1 + (1 + CoupledOp410.qW M)))
          false w mode (fun _ => false)) := by
  let ℓ := Nat.clog 2 (n' + 1)
  let q_w := CoupledOp410.qW M
  let h_tree := Nat.clog 2 (2 * M + 2)
  let anc_leaf := 1 + (1 + q_w)
  let h_le : h_tree ≤ ℓ := Nat.clog_mono_right 2 (by omega)
  let anc := routerAnc ℓ q_w h_tree anc_leaf
  let emb := swapWFCEmb ℓ q_w anc
  let leaves : Fin (2 ^ h_tree) → LayeredCircuit (1 + q_w + anc_leaf) := fun t => uTildeLeaf M hM t.1
  let U_mat : Fin (2 ^ h_tree) → Matrix (Qubits q_w) (Qubits q_w) ℂ := fun t => CoupledOp410.U_op410 M t.1
  have hleaves : ∀ t, (leaves t).ImplementsOnClean (ctrlBlockMat (U_mat t)) := fun t =>
    uTildeLeaf_implements M hM t.1
  change act ((coherentRouter ℓ q_w h_tree anc_leaf h_le leaves).mapWires emb).unitary
      (ket (CoupledOp410.packUTilde410 M n' anc fc w mode (fun _ => false))) = _
  have hcomp_out : ∀ (b : Bool) (m' : Qubits q_w),
      CoupledOp410.packUTilde410 M n' anc b w m' (fun _ => false) ∘ emb =
        padZero (routerMain ℓ q_w) anc (packRouterMain w b m') := fun b m' =>
    packUTilde410_comp_swapWFC M n' h_tree anc_leaf b w m'
  have hact_router := act_coherentRouter_ket ℓ q_w h_tree anc_leaf h_le leaves U_mat hleaves w fc mode
  have hcond_eq : (fc = true ∧ Thm49Primitives.bitsToNatLSB w < 2 ^ h_tree) ↔
      (fc = true ∧ CoupledOp410.bitsToNatLSB w < 2 ^ h_tree) := Iff.rfl
  by_cases hfc : fc = true
  · subst hfc
    rw [if_pos rfl]
    by_cases hlt : CoupledOp410.bitsToNatLSB w < 2 ^ h_tree
    · have hcond : true = true ∧ Thm49Primitives.bitsToNatLSB w < 2 ^ h_tree := ⟨rfl, hlt⟩
      rw [dif_pos hcond] at hact_router
      conv_lhs at hact_router => rw [← hcomp_out true mode]
      refine act_mapWires_ket_sum (coherentRouter ℓ q_w h_tree anc_leaf h_le leaves) emb
        (CoupledOp410.packUTilde410 M n' anc true w mode (fun _ => false))
        (fun mode' => CoupledOp410.U_op410 M (CoupledOp410.bitsToNatLSB w) mode' mode)
        (fun mode' => padZero (routerMain ℓ q_w) anc (packRouterMain w true mode'))
        (fun mode' => CoupledOp410.packUTilde410 M n' anc true w mode' (fun _ => false))
        ?_ ?_ ?_
      · refine hact_router.trans ?_
        refine Finset.sum_congr rfl fun mode' _ => ?_
        rfl
      · intro mode'
        exact hcomp_out true mode'
      · intro mode' i hi
        exact absurd (mem_range_swapWFCEmb ℓ q_w anc i) hi
    · have hnot : ¬ (true = true ∧ Thm49Primitives.bitsToNatLSB w < 2 ^ h_tree) := fun h => hlt h.2
      rw [dif_neg hnot] at hact_router
      conv_lhs at hact_router => rw [← hcomp_out true mode]
      have hge_pow : 2 * M + 2 ≤ 2 ^ h_tree := Nat.le_pow_clog (by norm_num) (2 * M + 2)
      have hgt_M : 2 * M + 1 < CoupledOp410.bitsToNatLSB w := by
        have h1 : 2 ^ h_tree ≤ CoupledOp410.bitsToNatLSB w := Nat.le_of_not_lt hlt
        omega
      have hU_one : CoupledOp410.U_op410 M (CoupledOp410.bitsToNatLSB w) = 1 := by
        simp [CoupledOp410.U_op410, hgt_M]
      have hsum_one : (∑ mode' : Qubits q_w,
            CoupledOp410.U_op410 M (CoupledOp410.bitsToNatLSB w) mode' mode •
              ket (CoupledOp410.packUTilde410 M n' anc true w mode' (fun _ => false))) =
          ket (CoupledOp410.packUTilde410 M n' anc true w mode (fun _ => false)) := by
        rw [Finset.sum_eq_single mode]
        · rw [hU_one, Matrix.one_apply_eq, one_smul]
        · intro mode' _ hne
          rw [hU_one, Matrix.one_apply_ne hne, zero_smul]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum_one]
      refine act_mapWires_ket (coherentRouter ℓ q_w h_tree anc_leaf h_le leaves) emb
        (CoupledOp410.packUTilde410 M n' anc true w mode (fun _ => false))
        (padZero (routerMain ℓ q_w) anc (packRouterMain w true mode)) hact_router
        (CoupledOp410.packUTilde410 M n' anc true w mode (fun _ => false))
        (hcomp_out true mode)
        (fun i hi => absurd (mem_range_swapWFCEmb ℓ q_w anc i) hi)
  · have hfc_f : fc = false := Bool.eq_false_iff.mpr hfc
    subst hfc_f
    rw [if_neg Bool.false_ne_true]
    have hnot : ¬ (false = true ∧ Thm49Primitives.bitsToNatLSB w < 2 ^ h_tree) := by simp
    rw [dif_neg hnot] at hact_router
    conv_lhs at hact_router => rw [← hcomp_out false mode]
    refine act_mapWires_ket (coherentRouter ℓ q_w h_tree anc_leaf h_le leaves) emb
      (CoupledOp410.packUTilde410 M n' anc false w mode (fun _ => false))
      (padZero (routerMain ℓ q_w) anc (packRouterMain w false mode)) hact_router
      (CoupledOp410.packUTilde410 M n' anc false w mode (fun _ => false))
      (hcomp_out false mode)
      (fun i hi => absurd (mem_range_swapWFCEmb ℓ q_w anc i) hi)

/-! ### Part 3: Concrete `PrimitiveSuite410` instantiation -/

noncomputable def thm410PrimitiveSuite : CoupledOp410.PrimitiveSuite410 where
  toffoliCirc := toffoli3.toCircuit
  toffoliDepth := toffoli3.depth
  toffoli_hdepth _ _ := toffoli3.nonOracleDepth_le
  toffoli_act b₀ b₁ b₂ := by
    let x : Qubits 3 := fun i : Fin 3 =>
      if i.1 = 0 then b₀ else if i.1 = 1 then b₁ else b₂
    change act toffoli3.unitary (ket x) = _
    rw [act_toffoli3_ket x]
    congr 1; funext i; fin_cases i <;> rfl
  ancCH := id
  chCirc n := (ctrlHadamardN n).toCircuit
  chDepth n := (ctrlHadamardN n).depth
  ch_hdepth n _ _ := (ctrlHadamardN n).nonOracleDepth_le
  C_ch := 7 / Real.log 2
  hC_ch_pos := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  ch_bound n hn := by
    refine ⟨?_, ctrlHadamardN_depth_real n hn⟩
    have hsize : ((ctrlHadamardN n).toCircuit.length : ℝ) ≤ 3 * (n : ℝ) := by
      exact_mod_cast ctrlHadamardN_size n
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_le1 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h3_le : (3 : ℝ) ≤ 7 / Real.log 2 := by
      rw [le_div_iff₀ hlog2_pos]; linarith
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc ((ctrlHadamardN n).toCircuit.length : ℝ)
        ≤ 3 * (n : ℝ) := hsize
      _ ≤ (7 / Real.log 2) * (n : ℝ) := mul_le_mul_of_nonneg_right h3_le hn0
  ch_act := bridge_ch_act
  ancEq := id
  eqCirc L pat U hU := (multiEqCtrl1 L pat U hU).toCircuit
  eqDepth L := 10 * Nat.clog 2 (L + 1) + 3
  eq_hdepth L pat U hU _ _ :=
    le_trans (multiEqCtrl1 L pat U hU).nonOracleDepth_le (multiEqCtrl1_depth L pat U hU)
  C_eq := 13
  hC_eq_pos := by norm_num
  eq_bound L pat U hU := by
    refine ⟨?_, ?_⟩
    · have hsize : ((multiEqCtrl1 L pat U hU).toCircuit.length : ℝ) ≤ 12 * ((L : ℝ) + 1) := by
        exact_mod_cast multiEqCtrl1_size L pat U hU
      have hL0 : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
      linarith
    · exact_mod_cast (by omega : 10 * Nat.clog 2 (L + 1) + 3 ≤ 13 * (Nat.clog 2 (L + 1) + 1))
  eq_act := bridge_eq_act
  ancHC := hammingAnc
  hcCirc n := (hammingCounter n).toCircuit
  hcAdjCirc n := (hammingCounter n).adj.toCircuit
  hcDepth n := (hammingCounter n).depth
  hc_hdepth n _ _ :=
    ⟨(hammingCounter n).nonOracleDepth_le,
      le_of_le_of_eq (hammingCounter n).adj.nonOracleDepth_le (LayeredCircuit.adj_depth _)⟩
  hcAdj_length n := LayeredCircuit.adj_size (hammingCounter n)
  hcAdj_unitary n := LayeredCircuit.adj_unitary (hammingCounter n)
  C_hc := 209 / Real.log 2
  hC_hc_pos := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  hc_bound n hn := by
    refine ⟨?_, hammingCounter_depth_real n hn⟩
    have hsize : ((hammingCounter n).toCircuit.length : ℝ) ≤ 53 * (n : ℝ) := by
      exact_mod_cast hammingCounter_size n
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog_le : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h53_le : (53 : ℝ) ≤ (209 / Real.log 2) * Real.log (n : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2_pos]
      nlinarith
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc ((hammingCounter n).toCircuit.length : ℝ)
        ≤ 53 * (n : ℝ) := hsize
      _ ≤ ((209 / Real.log 2) * Real.log (n : ℝ)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right h53_le hn0
      _ = (209 / Real.log 2) * (n : ℝ) * Real.log (n : ℝ) := by ring
  hc_act := bridge_hc_act
  ancCN := id
  cnCirc n := (ctrlNotN n).toCircuit
  cnDepth n := 2 * Nat.clog 2 (n + 1) + 3
  cn_hdepth n _ _ := le_trans (ctrlNotN n).nonOracleDepth_le (ctrlNotN_depth n)
  C_cn := 7 / Real.log 2
  hC_cn_pos := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  cn_bound n hn := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨?_, ?_⟩
    · have hsize : ((ctrlNotN n).toCircuit.length : ℝ) = 3 * (n : ℝ) := by
        exact_mod_cast ctrlNotN_size n
      have hlog2_le1 : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h3_le : (3 : ℝ) ≤ 7 / Real.log 2 := by
        rw [le_div_iff₀ hlog2_pos]; linarith
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      calc ((ctrlNotN n).toCircuit.length : ℝ)
          = 3 * (n : ℝ) := hsize
        _ ≤ (7 / Real.log 2) * (n : ℝ) := mul_le_mul_of_nonneg_right h3_le hn0
    · have hclog := clog2_succ_le_real_log (by omega : 1 ≤ n)
      have hlog_ge : 1 ≤ Real.log n / Real.log 2 := by
        rw [one_le_div hlog2_pos]
        exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      calc ((2 * Nat.clog 2 (n + 1) + 3 : ℕ) : ℝ)
          = 2 * (Nat.clog 2 (n + 1) : ℝ) + 3 := by push_cast; ring
        _ ≤ 2 * (Real.log n / Real.log 2 + 1) + 3 := by linarith
        _ = 2 * (Real.log n / Real.log 2) + 5 := by ring
        _ ≤ 2 * (Real.log n / Real.log 2) + 5 * (Real.log n / Real.log 2) := by linarith
        _ = (7 / Real.log 2) * Real.log n := by ring
  cn_act := bridge_cn_act
  ancUTilde M n' := routerAnc (Nat.clog 2 (n' + 1)) (CoupledOp410.qW M) (Nat.clog 2 (2 * M + 2))
    (1 + (1 + CoupledOp410.qW M))
  uTilde410Circ M n' hM hle := (uTildeRouter M n' hM hle).toCircuit
  uTilde410Depth M n' := uTildeDepthBound M n'
  uTilde410_hdepth M n' hM hle _ _ := by
    refine le_trans (uTildeRouter M n' hM hle).nonOracleDepth_le ?_
    dsimp only [uTildeRouter]
    rw [LayeredCircuit.mapWires_depth]
    exact coherentRouter_depth (Nat.clog 2 (n' + 1)) (CoupledOp410.qW M) (Nat.clog 2 (2 * M + 2))
      (1 + (1 + CoupledOp410.qW M)) (88 * CoupledOp410.qW M + 84)
      (Nat.clog_mono_right 2 (by omega)) _ (fun t => uTildeLeaf_depth M hM t.1)
  C_ut := 800 / Real.log 2
  hC_ut_pos := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  uTilde410_bound M n' hM hle hn3 :=
    ⟨uTildeRouter_size M n' hM hle hn3, uTildeDepthBound_real M n' hM hle hn3⟩
  uTilde410_act := bridge_uTilde_act

end Thm410Bridge

open QAlgorithms QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.CoupledOp410

theorem solution : Nonempty PrimitiveSuite410 := ⟨Thm410Bridge.thm410PrimitiveSuite⟩
