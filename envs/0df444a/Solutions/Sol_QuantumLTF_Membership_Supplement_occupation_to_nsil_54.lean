-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.occupation_to_nsil_54
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T04:02:31.387818+00:00
-- url     : https://prove2.me/submissions/639a423a-ac61-48da-a9ab-db7b0fc1e55c

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_padKet
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_occArith54
import Theorems.Thm_QuantumLTF_Membership_Supplement_bitonic_routing_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_occ_arith_54

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement.StageA

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open Thm49Primitives Thm410Router Cslib.BitonicSort

/-! ### Generic Circuit, Bit-Vector, and Block-Embedding Helpers -/

lemma act_adj_ket_of_act_ket {m : ℕ} (lc : LayeredCircuit m) {z₀ z₁ : Qubits m}
    (h : act lc.unitary (ket z₀) = ket z₁) :
    act lc.adj.unitary (ket z₁) = ket z₀ := by
  have h1 := congrArg (act lc.adj.unitary) h.symm
  conv_rhs at h1 =>
    rw [← act_mul, LayeredCircuit.adj_unitary,
      Matrix.mem_unitaryGroup_iff'.mp lc.unitary_mem_unitaryGroup, act_one]
  exact h1

lemma act_seqList_fin_ket {m k : ℕ} (f : Fin k → LayeredCircuit m)
    (z : (i : ℕ) → i ≤ k → Qubits m)
    (hstep : ∀ (i : ℕ) (hi : i < k),
      act (f ⟨i, hi⟩).unitary (ket (z i (le_of_lt hi))) = ket (z (i + 1) hi)) :
    act (LayeredCircuit.seqList (List.ofFn f)).unitary (ket (z 0 (Nat.zero_le k))) =
      ket (z k le_rfl) := by
  have hgen : ∀ (r : ℕ) (hr : r ≤ k),
      act (LayeredCircuit.seqList ((List.ofFn f).take r)).unitary (ket (z 0 (Nat.zero_le k))) =
        ket (z r hr) := by
    intro r
    induction r with
    | zero =>
      intro hr
      simp [LayeredCircuit.seqList, LayeredCircuit.id_unitary, act_one]
    | succ r ih =>
      intro hr
      have htake : (List.ofFn f).take (r + 1) =
          (List.ofFn f).take r ++ [f ⟨r, hr⟩] := by
        rw [List.take_succ_eq_append_getElem (by simp; exact hr)]
        simp [List.getElem_ofFn]
      have hseq_app : ∀ (xs ys : List (LayeredCircuit m)),
          (LayeredCircuit.seqList (xs ++ ys)).unitary =
            (LayeredCircuit.seqList ys).unitary * (LayeredCircuit.seqList xs).unitary := by
        intro xs ys
        simp [LayeredCircuit.seqList_unitary]
      rw [htake, hseq_app, act_mul, ih (le_of_lt hr)]
      simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, LayeredCircuit.id_unitary,
        one_mul]
      exact hstep r hr
  have hfinal := hgen k le_rfl
  rwa [List.take_of_length_le (by simp)] at hfinal

lemma seqList_ofFn_size_le {m k : ℕ} (f : Fin k → LayeredCircuit m) (B : ℕ)
    (hB : ∀ i : Fin k, (f i).size ≤ B) :
    (LayeredCircuit.seqList (List.ofFn f)).size ≤ k * B := by
  rw [LayeredCircuit.seqList_size]
  have hmap : ((List.ofFn f).map LayeredCircuit.size).sum = ∑ i : Fin k, (f i).size := by
    rw [List.map_ofFn, List.sum_ofFn]
    rfl
  rw [hmap]
  calc ∑ i : Fin k, (f i).size
      ≤ ∑ _i : Fin k, B := Finset.sum_le_sum fun i _ => hB i
    _ = k * B := by simp

lemma padKet_ket_eq {N : ℕ} (e : ℕ) (x : Qubits N) :
    padKet e (ket x) = ket (padZero N e x) := by
  ext z
  simp only [padKet, ket, WithLp.ofLp_toLp, PiLp.single_apply]
  by_cases hclean : ∀ j : Fin e, z (Fin.natAdd N j) = false
  · rw [if_pos hclean]
    have hiff : (fun i => z (Fin.castAdd e i)) = x ↔ z = padZero N e x := by
      constructor
      · intro h
        funext u
        refine Fin.addCases (fun i => ?_) (fun j => ?_) u
        · simp [← h]
        · simp [hclean j]
      · intro h
        subst h
        funext i
        simp
    by_cases h1 : (fun i => z (Fin.castAdd e i)) = x
    · rw [if_pos h1, if_pos (hiff.mp h1)]
    · rw [if_neg h1, if_neg (mt hiff.mpr h1)]
  · rw [if_neg hclean]
    have hne : z ≠ padZero N e x := by
      intro h
      apply hclean
      intro j
      rw [h]
      simp
    rw [if_neg hne]

lemma embedPartAndDeg54_ket_eq {m N : ℕ} (partEmb : Fin N ↪ Fin m)
    (y : Qubits N) (degRest z_out : Qubits m)
    (hin : ∀ i : Fin N, z_out (partEmb i) = y i)
    (hout : ∀ a : Fin m, a ∉ Set.range partEmb → z_out a = degRest a) :
    embedPartAndDeg54 partEmb (ket y) degRest = ket z_out := by
  ext z
  simp only [embedPartAndDeg54_apply, ket, PiLp.single_apply]
  by_cases hdeg : ∀ a : Fin m, a ∉ Set.range partEmb → z a = degRest a
  · rw [if_pos hdeg]
    have hiff : (fun i => z (partEmb i)) = y ↔ z = z_out := by
      constructor
      · intro h
        funext a
        by_cases ha : a ∈ Set.range partEmb
        · obtain ⟨i, rfl⟩ := ha
          exact (congrFun h i).trans (hin i).symm
        · exact (hdeg a ha).trans (hout a ha).symm
      · intro h
        subst h
        funext i
        exact hin i
    by_cases h1 : (fun i => z (partEmb i)) = y
    · rw [if_pos h1, if_pos (hiff.mp h1)]
    · rw [if_neg h1, if_neg (mt hiff.mpr h1)]
  · rw [if_neg hdeg]
    have hne : z ≠ z_out := by
      intro h
      apply hdeg
      intro a ha
      rw [h]
      exact hout a ha
    rw [if_neg hne]

lemma bitsToNat_lt_two_pow {w : ℕ} (b : Qubits w) : bitsToNat b < 2 ^ w := by
  rw [← bitsEquivFin_apply]
  exact (bitsEquivFin w b).isLt

lemma bitsToNat_natToBits_exact {w x : ℕ} (hx : x < 2 ^ w) :
    bitsToNat (natToBits w x) = x := by
  rw [← bitsEquivFin_apply]
  simp [natToBits, Nat.mod_eq_of_lt hx]

lemma natToBits_eq_bitsToNat_iff {w : ℕ} (b : Qubits w) :
    natToBits w (bitsToNat b) = b := by
  have h1 : (bitsEquivFin w (natToBits w (bitsToNat b)) : ℕ) = (bitsEquivFin w b : ℕ) := by
    rw [bitsEquivFin_apply, bitsEquivFin_apply]
    exact bitsToNat_natToBits_exact (bitsToNat_lt_two_pow b)
  exact (bitsEquivFin w).injective (Fin.ext h1)

lemma bitsToNat_append {w1 w2 : ℕ} (a : Qubits w1) (b : Qubits w2) :
    bitsToNat (Fin.append a b) = bitsToNat a * 2 ^ w2 + bitsToNat b := by
  dsimp only [bitsToNat]
  rw [Fin.sum_univ_add, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.append_left, Fin.val_castAdd]
    have hi := i.isLt
    have hexp : w1 + w2 - 1 - i.1 = (w1 - 1 - i.1) + w2 := by omega
    cases ha : a i <;> simp [hexp, pow_add]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.append_right, Fin.val_natAdd]
    have hexp : w1 + w2 - 1 - (w1 + j.1) = w2 - 1 - j.1 := by omega
    rw [hexp]

lemma bitsToNat_append3 {w1 w2 w3 : ℕ} (a : Qubits w1) (b : Qubits w2) (c : Qubits w3) :
    bitsToNat (Fin.append a (Fin.append b c)) =
      (bitsToNat a * 2 ^ w2 + bitsToNat b) * 2 ^ w3 + bitsToNat c := by
  rw [bitsToNat_append, bitsToNat_append, add_mul, mul_assoc, ← pow_add, add_comm w2 w3, add_assoc]

/-- Reverse wire order of an embedding `Fin w ↪ Fin total`. -/
def revEmb {w total : ℕ} (e : Fin w ↪ Fin total) : Fin w ↪ Fin total where
  toFun i := e i.rev
  inj' _ _ h := Fin.rev_injective (e.injective h)

@[simp] lemma revEmb_apply {w total : ℕ} (e : Fin w ↪ Fin total) (i : Fin w) :
    revEmb e i = e i.rev := rfl

lemma range_revEmb {w total : ℕ} (e : Fin w ↪ Fin total) :
    Set.range (revEmb e) = Set.range e := by
  ext x
  simp only [Set.mem_range, revEmb_apply]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i.rev, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i.rev, by simp⟩

/-- Contiguous wire segment `[start .. start + len)` inside `Fin total`. -/
def segEmb (start len total : ℕ) (h : start + len ≤ total) : Fin len ↪ Fin total where
  toFun i := ⟨start + i.1, by omega⟩
  inj' a b heq := Fin.ext (by have := congrArg Fin.val heq; dsimp only at this; omega)

@[simp] lemma segEmb_val {start len total : ℕ} (h : start + len ≤ total) (i : Fin len) :
    (segEmb start len total h i).1 = start + i.1 := rfl

/-- Sub-register embedding for array slot `pos : Fin M` of stride `stride` and slice `[off .. off + len)`. -/
def slotSliceEmb (base stride M off len total : ℕ)
    (hstride : off + len ≤ stride) (hbound : base + M * stride ≤ total)
    (pos : Fin M) : Fin len ↪ Fin total where
  toFun i := ⟨base + pos.1 * stride + off + i.1, by
    have hp := pos.isLt
    have hi := i.isLt
    have hmul : (pos.1 + 1) * stride ≤ M * stride := Nat.mul_le_mul_right stride hp
    have hstep : pos.1 * stride + stride ≤ M * stride := by
      simpa [Nat.succ_mul] using hmul
    omega⟩
  inj' a b heq := Fin.ext (by have := congrArg Fin.val heq; dsimp only at this; omega)

@[simp] lemma slotSliceEmb_val (base stride M off len total : ℕ)
    (hstride : off + len ≤ stride) (hbound : base + M * stride ≤ total)
    (pos : Fin M) (i : Fin len) :
    (slotSliceEmb base stride M off len total hstride hbound pos i).1 =
      base + pos.1 * stride + off + i.1 := rfl

lemma flatReg_append_bits {M w1 w2 : ℕ} (k1 : Fin M → Qubits w1) (k2 : Fin M → Qubits w2)
    (pos : Fin M) (u : Fin (w1 + w2)) :
    flatReg M (w1 + w2) (fun i => Fin.append (k1 i) (k2 i)) (finProdFinEquiv (pos, u)) =
      Fin.append (k1 pos) (k2 pos) u := by
  simp [flatReg]

/-! ### Stage A Context & Wire Layout -/

structure OccCtx where
  O : OccArith54
  R : BitonicRouting54
  n : ℕ
  K : ℕ
  D : ℕ
  q : ℕ
  hn : 1 ≤ n
  hK : 1 ≤ K
  hD : 2 * K + 1 ≤ D
  hq : D ≤ 2 ^ q

namespace OccCtx

variable (C : OccCtx)

def s : ℕ := Nat.clog 2 C.n + 1
abbrev m : ℕ := C.n + 1
abbrev N : ℕ := 2 * C.K
def w_v : ℕ := Nat.clog 2 (2 * C.K + 1)
abbrev w_a : ℕ := C.s + 1
def d : ℕ := Nat.clog 2 (C.m + C.N)
abbrev M : ℕ := arity C.d
def w_pos : ℕ := max C.w_a (max C.w_v C.d) + 1
abbrev w_k1 : ℕ := C.w_v + C.w_a
abbrev w_p1 : ℕ := C.w_a
abbrev w_rec1 : ℕ := C.w_k1 + C.w_p1
abbrev w_k2 : ℕ := C.w_a + 1 + C.w_v
abbrev w_p2 : ℕ := C.w_a + C.w_v
abbrev w_rec : ℕ := C.w_k2 + C.w_p2
abbrev T : ℕ := sortTraceSize C.d

lemma M_eq : C.M = 2 ^ C.d := arity_eq_two_pow C.d

lemma w_v_ge_two : 2 ≤ C.w_v := by
  dsimp only [w_v]
  have h1 : 2 ^ 1 < 2 * C.K + 1 := by have := C.hK; omega
  have h2 := Nat.le_pow_clog (by norm_num : 1 < 2) (2 * C.K + 1)
  by_contra hlt
  have hw : Nat.clog 2 (2 * C.K + 1) ≤ 1 := by omega
  have hp : 2 ^ Nat.clog 2 (2 * C.K + 1) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hw
  omega

lemma w_v_le_q : C.w_v ≤ C.q := by
  dsimp only [w_v]
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  exact le_trans C.hD C.hq

lemma N_add_one_lt_two_pow_w_v : C.N + 1 < 2 ^ C.w_v := by
  dsimp only [N, w_v]
  have hle : 2 * C.K + 1 ≤ 2 ^ Nat.clog 2 (2 * C.K + 1) :=
    Nat.le_pow_clog (by norm_num : 1 < 2) (2 * C.K + 1)
  have hpos : 1 ≤ Nat.clog 2 (2 * C.K + 1) := by have := C.w_v_ge_two; dsimp [w_v] at this; omega
  have heven : 2 ^ Nat.clog 2 (2 * C.K + 1) % 2 = 0 := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Nat.clog 2 (2 * C.K + 1) ≠ 0)
    rw [ht, pow_succ]
    omega
  omega

lemma n_lt_two_pow_s : C.n < 2 ^ C.s := by
  dsimp only [s]
  have hle : C.n ≤ 2 ^ Nat.clog 2 C.n := Nat.le_pow_clog (by norm_num : 1 < 2) C.n
  have hpos : 1 ≤ 2 ^ Nat.clog 2 C.n := Nat.one_le_two_pow
  rw [pow_succ']
  omega

lemma m_lt_two_pow_w_a : C.m < 2 ^ C.w_a := by
  dsimp only [m, w_a, s]
  have hle : C.n ≤ 2 ^ Nat.clog 2 C.n := Nat.le_pow_clog (by norm_num : 1 < 2) C.n
  have hn1 := C.hn
  have hpow : 2 ^ (Nat.clog 2 C.n + 1 + 1) = 4 * 2 ^ Nat.clog 2 C.n := by
    rw [pow_succ', pow_succ']; ring
  omega

lemma m_add_N_le_M : C.m + C.N ≤ C.M := by
  rw [C.M_eq]
  exact Nat.le_pow_clog (by norm_num : 1 < 2) (C.m + C.N)

lemma M_lt_two_pow_w_pos : C.M < 2 ^ C.w_pos := by
  rw [C.M_eq]
  apply Nat.pow_lt_pow_right (by norm_num)
  dsimp only [w_pos]
  omega

lemma w_a_lt_w_pos : C.w_a < C.w_pos := by dsimp [w_pos]; omega
lemma w_v_lt_w_pos : C.w_v < C.w_pos := by dsimp [w_pos]; omega
lemma w_rec1_le_w_rec : C.w_rec1 ≤ C.w_rec := by
  dsimp only [w_rec1, w_k1, w_p1, w_rec, w_k2, w_p2]; omega

abbrev offA : ℕ := 0
abbrev lenA : ℕ := C.n * C.q
abbrev offK : ℕ := C.lenA
abbrev lenK : ℕ := C.w_v
abbrev offL : ℕ := C.offK + C.lenK
abbrev lenL : ℕ := C.N * C.s
abbrev offP : ℕ := C.offL + C.lenL
abbrev lenP : ℕ := C.n * C.w_v
abbrev offArr : ℕ := C.offP + C.lenP
abbrev lenArr : ℕ := C.M * C.w_rec
abbrev offTr : ℕ := C.offArr + C.lenArr
abbrev lenTr : ℕ := C.T
abbrev offScr : ℕ := C.offTr + C.lenTr
abbrev lenScr : ℕ := 2 * C.w_pos + C.w_a + C.w_v + C.w_k2 + C.s + 16
abbrev e_occ : ℕ := C.lenK + C.lenL + C.lenP + C.lenArr + C.lenTr + C.lenScr
abbrev total : ℕ := C.n * C.q + C.e_occ

lemma total_eq : C.total = C.offScr + C.lenScr := by
  dsimp only [total, e_occ, offScr, offTr, offArr, offP, offL, offK, lenA]; omega

lemma offK_le : C.offK + C.lenK ≤ C.total := by
  rw [C.total_eq]; dsimp only [offScr, offTr, offArr, offP, offL]; omega
lemma offL_le : C.offL + C.lenL ≤ C.total := by
  rw [C.total_eq]; dsimp only [offScr, offTr, offArr, offP]; omega
lemma offP_le : C.offP + C.lenP ≤ C.total := by
  rw [C.total_eq]; dsimp only [offScr, offTr, offArr]; omega
lemma offArr_le : C.offArr + C.lenArr ≤ C.total := by
  rw [C.total_eq]; dsimp only [offScr, offTr]; omega
lemma offTr_le : C.offTr + C.lenTr ≤ C.total := by
  rw [C.total_eq]; dsimp only [offScr]; omega

/-- Embedding of the low `w_v` LSB-first wires of `A[i]`. -/
def aLowEmbLSB (i : Fin C.n) : Fin C.w_v ↪ Fin C.total where
  toFun u := ⟨i.1 * C.q + (C.q - 1 - u.1), by
    have hi := i.isLt
    have hu := u.isLt
    have hq := C.w_v_le_q
    have hmul : (i.1 + 1) * C.q ≤ C.n * C.q := Nat.mul_le_mul_right C.q hi
    have hstep : i.1 * C.q + C.q ≤ C.n * C.q := by simpa [Nat.succ_mul] using hmul
    have hle : C.n * C.q ≤ C.total := by dsimp [total]; omega
    omega⟩
  inj' a b heq := Fin.ext (by
    have hv := congrArg Fin.val heq; dsimp only at hv
    have ha := a.isLt; have hb := b.isLt; have hq := C.w_v_le_q
    omega)

@[simp] lemma aLowEmbLSB_val (i : Fin C.n) (u : Fin C.w_v) :
    (C.aLowEmbLSB i u).1 = i.1 * C.q + (C.q - 1 - u.1) := rfl

def kEmbLSB : Fin C.w_v ↪ Fin C.total := segEmb C.offK C.w_v C.total C.offK_le
def partEmb : Fin (C.N * C.s) ↪ Fin C.total := segEmb C.offL (C.N * C.s) C.total C.offL_le

def lSlotEmb (r : Fin C.N) : Fin C.s ↪ Fin C.total :=
  slotSliceEmb C.offL C.s C.N 0 C.s C.total (by omega) C.offL_le r

lemma lSlotEmb_eq_partEmb (r : Fin C.N) (b : Fin C.s) :
    C.lSlotEmb r b = C.partEmb (finProdFinEquiv (r, b)) := by
  apply Fin.ext
  dsimp only [lSlotEmb, partEmb, segEmb, slotSliceEmb, finProdFinEquiv, Equiv.coe_fn_mk]
  change C.offL + r.1 * C.s + 0 + b.1 = C.offL + (b.1 + C.s * r.1)
  ring

def lSlotEmbLSB (r : Fin C.N) : Fin C.s ↪ Fin C.total := revEmb (C.lSlotEmb r)

def pSlotEmbLSB (i : Fin C.n) : Fin C.w_v ↪ Fin C.total :=
  slotSliceEmb C.offP C.w_v C.n 0 C.w_v C.total (by omega) C.offP_le i

def trEmb : Fin C.T ↪ Fin C.total := segEmb C.offTr C.T C.total C.offTr_le
def scrEmb (off len : ℕ) (h : off + len ≤ C.lenScr) : Fin len ↪ Fin C.total :=
  segEmb (C.offScr + off) len C.total (by rw [C.total_eq]; omega)

-- Pass 1 slot sub-embeddings in `Arr`
abbrev c1EmbMSB (pos : Fin C.M) : Fin C.w_v ↪ Fin C.total :=
  slotSliceEmb C.offArr C.w_rec C.M 0 C.w_v C.total (by dsimp [w_rec, w_k2, w_p2]; omega) C.offArr_le pos
abbrev c1EmbLSB (pos : Fin C.M) : Fin C.w_v ↪ Fin C.total := revEmb (C.c1EmbMSB pos)
abbrev a1EmbMSB (pos : Fin C.M) : Fin C.w_a ↪ Fin C.total :=
  slotSliceEmb C.offArr C.w_rec C.M C.w_v C.w_a C.total (by dsimp [w_rec, w_k2, w_p2]; omega) C.offArr_le pos
abbrev a1EmbLSB (pos : Fin C.M) : Fin C.w_a ↪ Fin C.total := revEmb (C.a1EmbMSB pos)
abbrev b1EmbLSB (pos : Fin C.M) : Fin C.w_a ↪ Fin C.total :=
  slotSliceEmb C.offArr C.w_rec C.M (C.w_v + C.w_a) C.w_a C.total (by dsimp [w_rec, w_k2, w_p2]; omega) C.offArr_le pos

-- Pass 2 slot sub-embeddings in `Arr`
abbrev b2EmbMSB (pos : Fin C.M) : Fin C.w_a ↪ Fin C.total :=
  slotSliceEmb C.offArr C.w_rec C.M 0 C.w_a C.total (by dsimp [w_rec, w_k2, w_p2]; omega) C.offArr_le pos
abbrev b2EmbLSB (pos : Fin C.M) : Fin C.w_a ↪ Fin C.total := revEmb (C.b2EmbMSB pos)
abbrev f2Emb (pos : Fin C.M) : Fin 1 ↪ Fin C.total :=
  slotSliceEmb C.offArr C.w_rec C.M C.w_a 1 C.total (by dsimp [w_rec, w_k2, w_p2]; omega) C.offArr_le pos
abbrev ceff2EmbMSB (pos : Fin C.M) : Fin C.w_v ↪ Fin C.total :=
  slotSliceEmb C.offArr C.w_rec C.M (C.w_a + 1) C.w_v C.total (by dsimp [w_rec, w_k2, w_p2]; omega) C.offArr_le pos
abbrev ceff2EmbLSB (pos : Fin C.M) : Fin C.w_v ↪ Fin C.total := revEmb (C.ceff2EmbMSB pos)
abbrev a2EmbLSB (pos : Fin C.M) : Fin C.w_a ↪ Fin C.total :=
  slotSliceEmb C.offArr C.w_rec C.M C.w_k2 C.w_a C.total (by dsimp [w_rec, w_k2, w_p2]; omega) C.offArr_le pos
abbrev c2EmbLSB (pos : Fin C.M) : Fin C.w_v ↪ Fin C.total :=
  slotSliceEmb C.offArr C.w_rec C.M (C.w_k2 + C.w_a) C.w_v C.total (by dsimp [w_rec, w_k2, w_p2]; omega) C.offArr_le pos

def arr1AllEmb : Fin (C.M * C.w_rec1) ↪ Fin C.total where
  toFun idx :=
    let p := finProdFinEquiv.symm idx
    ⟨C.offArr + p.1.1 * C.w_rec + p.2.1, by
      have hp1 := p.1.isLt
      have hp2 := p.2.isLt
      have h1 : C.w_rec1 ≤ C.w_rec := C.w_rec1_le_w_rec
      have h2 := C.offArr_le
      have hmul : (p.1.1 + 1) * C.w_rec ≤ C.M * C.w_rec := Nat.mul_le_mul_right C.w_rec hp1
      have hstep : p.1.1 * C.w_rec + C.w_rec ≤ C.M * C.w_rec := by simpa [Nat.succ_mul] using hmul
      dsimp only [lenArr] at h2
      omega⟩
  inj' x y h := by
    have hv := congrArg Fin.val h; dsimp only at hv
    set px := finProdFinEquiv.symm x
    set py := finProdFinEquiv.symm y
    have hx2 := px.2.isLt; have hy2 := py.2.isLt; have h1 := C.w_rec1_le_w_rec
    have hp1 : px.1.1 = py.1.1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have : (px.1.1 + 1) * C.w_rec ≤ py.1.1 * C.w_rec := Nat.mul_le_mul_right C.w_rec hlt
        simp only [Nat.succ_mul] at this; omega
      · have : (py.1.1 + 1) * C.w_rec ≤ px.1.1 * C.w_rec := Nat.mul_le_mul_right C.w_rec hlt
        simp only [Nat.succ_mul] at this; omega
    have hp2 : px.2.1 = py.2.1 := by rw [hp1] at hv; omega
    exact finProdFinEquiv.symm.injective (Prod.ext (Fin.ext hp1) (Fin.ext hp2))

def arr2AllEmb : Fin (C.M * C.w_rec) ↪ Fin C.total :=
  segEmb C.offArr (C.M * C.w_rec) C.total C.offArr_le

lemma arr2AllEmb_pair (pos : Fin C.M) (u : Fin C.w_rec) :
    (C.arr2AllEmb (finProdFinEquiv (pos, u))).1 = C.offArr + pos.1 * C.w_rec + u.1 := by
  dsimp only [arr2AllEmb, segEmb, finProdFinEquiv, Equiv.coe_fn_mk]
  change C.offArr + (u.1 + C.w_rec * pos.1) = C.offArr + pos.1 * C.w_rec + u.1
  ring

lemma mapWires_adj_unitary {m₀ m : ℕ} (lc : LayeredCircuit m₀) (emb : Fin m₀ ↪ Fin m) :
    (lc.mapWires emb).adj.unitary = (lc.adj.mapWires emb).unitary := by
  rw [LayeredCircuit.adj_unitary, LayeredCircuit.mapWires_unitary,
    LayeredCircuit.mapWires_unitary, LayeredCircuit.adj_unitary, embedOp_star]

lemma updateOn_combineEmb54_right {a b m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m)
    (hab : ∀ i j, ea i ≠ eb j) (z : Qubits m) (f : Qubits (a + b))
    (hf_left : ∀ i : Fin a, f (Fin.castAdd b i) = z (ea i)) :
    updateOn (combineEmb54 ea eb hab) z f =
      updateOn eb z (fun j => f (Fin.natAdd a j)) := by
  funext u
  by_cases hub : u ∈ Set.range eb
  · rcases hub with ⟨j, rfl⟩
    have heq : eb j = combineEmb54 ea eb hab (Fin.natAdd a j) := (combineEmb54_natAdd ea eb hab j).symm
    conv_lhs => rw [heq, updateOn_apply_emb]
    rw [updateOn_apply_emb]
  · rw [updateOn_apply_not_mem _ _ _ hub]
    by_cases hua : u ∈ Set.range ea
    · rcases hua with ⟨i, rfl⟩
      have heq : ea i = combineEmb54 ea eb hab (Fin.castAdd b i) := (combineEmb54_castAdd ea eb hab i).symm
      rw [heq, updateOn_apply_emb, hf_left i]
      exact congrArg z heq.symm.symm
    · have hnot : u ∉ Set.range (combineEmb54 ea eb hab) := by
        rintro ⟨k, rfl⟩
        induction k using Fin.addCases with
        | left i => exact hua ⟨i, (combineEmb54_castAdd ea eb hab i).symm⟩
        | right j => exact hub ⟨j, (combineEmb54_natAdd ea eb hab j).symm⟩
      exact updateOn_apply_not_mem _ _ _ hnot

/-! ### Reusable Register Operations (`LayeredCircuit C.total`) -/

def zeroEmb0 : Fin 0 ↪ Fin C.total where
  toFun := Fin.elim0
  inj' i := Fin.elim0 i

def padZeroEmb {m : ℕ} (emb : Fin m ↪ Fin C.total) : Fin (m + 0) ↪ Fin C.total :=
  combineEmb54 emb C.zeroEmb0 (fun _ j => Fin.elim0 j)

lemma combineEmb54_disj {a b c : ℕ} (ea : Fin a ↪ Fin C.total) (eb : Fin b ↪ Fin C.total)
    (ec : Fin c ↪ Fin C.total) (hab : ∀ i j, ea i ≠ eb j)
    (hac : ∀ i k, ea i ≠ ec k) (hbc : ∀ j k, eb j ≠ ec k) :
    ∀ i k, combineEmb54 ea eb hab i ≠ ec k := fun i k => by
  change Fin.addCases ea eb i ≠ ec k
  refine Fin.addCases (fun i0 => by simpa using hac i0 k) (fun j0 => by simpa using hbc j0 k) i

noncomputable def copyRegC (w : ℕ) (src dst : Fin w ↪ Fin C.total)
    (hdisj : ∀ i j, src i ≠ dst j) : LayeredCircuit C.total :=
  (C.O.copyRegCircuit w).mapWires (C.padZeroEmb (combineEmb54 src dst hdisj))

lemma copyRegC_size (w : ℕ) (src dst : Fin w ↪ Fin C.total)
    (hdisj : ∀ i j, src i ≠ dst j) : (C.copyRegC w src dst hdisj).size = w := by
  simp [copyRegC, C.O.copyRegCircuit_size]

lemma act_copyRegC (w : ℕ) (src dst : Fin w ↪ Fin C.total)
    (hdisj : ∀ i j, src i ≠ dst j) (z : Qubits C.total) :
    act (C.copyRegC w src dst hdisj).unitary (ket z) =
      ket (updateOn dst z (fun j => xor (z (dst j)) (z (src j)))) := by
  have hact := C.O.act_subReg_perm (C.O.copyRegCircuit w) (copyRegFn54 w)
    (C.O.copyRegCircuit_implements w) (combineEmb54 src dst hdisj) C.zeroEmb0
    (fun _ j => Fin.elim0 j) z (fun j => Fin.elim0 j)
  change act (C.copyRegC w src dst hdisj).unitary (ket z) = _ at hact
  rw [hact, updateOn_combineEmb54_right]
  · refine congrArg ket (congrArg (updateOn dst z) (funext fun j => ?_))
    dsimp only [copyRegFn54, Function.comp_apply]
    have hle : w ≤ (Fin.natAdd w j).1 := by simp
    rw [if_pos hle, combineEmb54_natAdd]
    have hsub : (⟨(Fin.natAdd w j).1 - w, by simp; omega⟩ : Fin (w + w)) = Fin.castAdd w j :=
      Fin.ext (by simp)
    rw [hsub, combineEmb54_castAdd]
  · intro i
    dsimp only [copyRegFn54, Function.comp_apply]
    have hlt : ¬ w ≤ (Fin.castAdd w i).1 := by simp
    rw [if_neg hlt, combineEmb54_castAdd]

noncomputable def setConstC (w c : ℕ) (dst : Fin w ↪ Fin C.total) : LayeredCircuit C.total :=
  (C.O.setConstCircuit w c).mapWires (C.padZeroEmb dst)

lemma setConstC_size (w c : ℕ) (dst : Fin w ↪ Fin C.total) :
    (C.setConstC w c dst).size ≤ w := by
  simpa [setConstC] using C.O.setConstCircuit_size w c

lemma act_setConstC (w c : ℕ) (dst : Fin w ↪ Fin C.total) (z : Qubits C.total) :
    act (C.setConstC w c dst).unitary (ket z) =
      ket (updateOn dst z (setConstFn54 w c (z ∘ dst))) :=
  C.O.act_subReg_perm (C.O.setConstCircuit w c) (setConstFn54 w c)
    (C.O.setConstCircuit_implements w c) dst C.zeroEmb0
    (fun _ j => Fin.elim0 j) z (fun j => Fin.elim0 j)

noncomputable def eqConstC (w c : ℕ) (reg : Fin w ↪ Fin C.total) (tgt : Fin 1 ↪ Fin C.total)
    (anc : Fin w ↪ Fin C.total)
    (hrt : ∀ i j, reg i ≠ tgt j) (hra : ∀ i j, reg i ≠ anc j) (hta : ∀ i j, tgt i ≠ anc j) :
    LayeredCircuit C.total :=
  (C.O.eqConstCircuit w c).mapWires
    (combineEmb54 (combineEmb54 reg tgt hrt) anc (C.combineEmb54_disj reg tgt anc hrt hra hta))

lemma eqConstC_size (w c : ℕ) (reg : Fin w ↪ Fin C.total) (tgt : Fin 1 ↪ Fin C.total)
    (anc : Fin w ↪ Fin C.total)
    (hrt : ∀ i j, reg i ≠ tgt j) (hra : ∀ i j, reg i ≠ anc j) (hta : ∀ i j, tgt i ≠ anc j) :
    (C.eqConstC w c reg tgt anc hrt hra hta).size ≤ 14 * w + 12 := by
  simpa [eqConstC] using C.O.eqConstCircuit_size w c

lemma act_eqConstC (w c : ℕ) (reg : Fin w ↪ Fin C.total) (tgt : Fin 1 ↪ Fin C.total)
    (anc : Fin w ↪ Fin C.total)
    (hrt : ∀ i j, reg i ≠ tgt j) (hra : ∀ i j, reg i ≠ anc j) (hta : ∀ i j, tgt i ≠ anc j)
    (z : Qubits C.total) (hclean : ∀ j : Fin w, z (anc j) = false) :
    act (C.eqConstC w c reg tgt anc hrt hra hta).unitary (ket z) =
      ket (updateOn tgt z (fun j => xor (z (tgt j))
        (decide (∀ i : Fin w, z (reg i) = natToBitsLSB w c i)))) := by
  have hact := C.O.act_subReg_perm (C.O.eqConstCircuit w c) (eqConstFn54 w c)
    (C.O.eqConstCircuit_implements w c) (combineEmb54 reg tgt hrt) anc
    (C.combineEmb54_disj reg tgt anc hrt hra hta) z hclean
  change act (C.eqConstC w c reg tgt anc hrt hra hta).unitary (ket z) = _ at hact
  rw [hact, updateOn_combineEmb54_right]
  · refine congrArg ket (congrArg (updateOn tgt z) (funext fun j => ?_))
    have hj0 : j = 0 := Subsingleton.elim j 0
    subst hj0
    have hj_nat : Fin.natAdd w (0 : Fin 1) = ⟨w, Nat.lt_succ_self w⟩ := Fin.ext (by simp)
    dsimp only [eqConstFn54, Function.comp_apply]
    rw [hj_nat, Function.update_self, ← hj_nat, combineEmb54_natAdd]
    refine congrArg (xor (z (tgt 0))) (decide_eq_decide.mpr (forall_congr' fun i => ?_))
    have hi_eq : (⟨i.1, by omega⟩ : Fin (w + 1)) = Fin.castAdd 1 i := rfl
    rw [hi_eq, combineEmb54_castAdd]
  · intro i
    have hi := i.isLt
    have hne : (Fin.castAdd 1 i : Fin (w + 1)) ≠ ⟨w, Nat.lt_succ_self w⟩ :=
      Fin.ne_of_val_ne (by simp; omega)
    dsimp only [eqConstFn54]
    rw [Function.update_of_ne hne]
    simp only [Function.comp_apply, combineEmb54_castAdd]

noncomputable def addInPlaceC (w : ℕ) (a b : Fin w ↪ Fin C.total) (anc : Fin 1 ↪ Fin C.total)
    (hab : ∀ i j, a i ≠ b j) (haa : ∀ i j, a i ≠ anc j) (hba : ∀ i j, b i ≠ anc j) :
    LayeredCircuit C.total :=
  (C.O.addInPlaceCircuit w).mapWires
    (combineEmb54 (combineEmb54 a b hab) anc (C.combineEmb54_disj a b anc hab haa hba))

lemma addInPlaceC_size (w : ℕ) (a b : Fin w ↪ Fin C.total) (anc : Fin 1 ↪ Fin C.total)
    (hab : ∀ i j, a i ≠ b j) (haa : ∀ i j, a i ≠ anc j) (hba : ∀ i j, b i ≠ anc j) :
    (C.addInPlaceC w a b anc hab haa hba).size = 14 * w := by
  simpa [addInPlaceC] using C.O.addInPlaceCircuit_size w

lemma act_addInPlaceC (w : ℕ) (a b : Fin w ↪ Fin C.total) (anc : Fin 1 ↪ Fin C.total)
    (hab : ∀ i j, a i ≠ b j) (haa : ∀ i j, a i ≠ anc j) (hba : ∀ i j, b i ≠ anc j)
    (z : Qubits C.total) (hclean : ∀ j : Fin 1, z (anc j) = false) :
    act (C.addInPlaceC w a b anc hab haa hba).unitary (ket z) =
      ket (updateOn b z (natToBitsLSB w (bitsToNatLSB (z ∘ a) + bitsToNatLSB (z ∘ b)))) := by
  have hact := C.O.act_subReg_perm (C.O.addInPlaceCircuit w) (addInPlaceFn54 w)
    (C.O.addInPlaceCircuit_implements w) (combineEmb54 a b hab) anc
    (C.combineEmb54_disj a b anc hab haa hba) z hclean
  change act (C.addInPlaceC w a b anc hab haa hba).unitary (ket z) = _ at hact
  rw [hact, updateOn_combineEmb54_right]
  · refine congrArg ket (congrArg (updateOn b z) (funext fun j => ?_))
    dsimp only [addInPlaceFn54, Function.comp_apply]
    rw [dif_neg (by simp)]
    have ha_eq : (fun i : Fin w => z (combineEmb54 a b hab ⟨i.1, by omega⟩)) = z ∘ a := by
      funext i
      have hi : (⟨i.1, by omega⟩ : Fin (w + w)) = Fin.castAdd w i := rfl
      rw [hi, combineEmb54_castAdd]; rfl
    have hb_eq : (fun i : Fin w => z (combineEmb54 a b hab ⟨w + i.1, by omega⟩)) = z ∘ b := by
      funext i
      have hi : (⟨w + i.1, by omega⟩ : Fin (w + w)) = Fin.natAdd w i := rfl
      rw [hi, combineEmb54_natAdd]; rfl
    rw [ha_eq, hb_eq]
    exact congrArg (natToBitsLSB w (bitsToNatLSB (z ∘ a) + bitsToNatLSB (z ∘ b)))
      (Fin.ext (by simp))
  · intro i
    dsimp only [addInPlaceFn54, Function.comp_apply]
    rw [dif_pos (by simp)]
    calc z ((combineEmb54 a b hab) ⟨(Fin.castAdd w i).1, _⟩)
        = z ((combineEmb54 a b hab) (Fin.castAdd w i)) :=
          congrArg z (congrArg (combineEmb54 a b hab) (Fin.ext (by simp)))
      _ = z (a i) := by rw [combineEmb54_castAdd]

noncomputable def subInPlaceC (w : ℕ) (a b : Fin w ↪ Fin C.total) (anc : Fin 1 ↪ Fin C.total)
    (hab : ∀ i j, a i ≠ b j) (haa : ∀ i j, a i ≠ anc j) (hba : ∀ i j, b i ≠ anc j) :
    LayeredCircuit C.total :=
  (C.O.subInPlaceCircuit w).mapWires
    (combineEmb54 (combineEmb54 a b hab) anc (C.combineEmb54_disj a b anc hab haa hba))

lemma subInPlaceC_size (w : ℕ) (a b : Fin w ↪ Fin C.total) (anc : Fin 1 ↪ Fin C.total)
    (hab : ∀ i j, a i ≠ b j) (haa : ∀ i j, a i ≠ anc j) (hba : ∀ i j, b i ≠ anc j) :
    (C.subInPlaceC w a b anc hab haa hba).size = 14 * w := by
  simpa [subInPlaceC] using C.O.subInPlaceCircuit_size w

lemma act_subInPlaceC (w : ℕ) (a b : Fin w ↪ Fin C.total) (anc : Fin 1 ↪ Fin C.total)
    (hab : ∀ i j, a i ≠ b j) (haa : ∀ i j, a i ≠ anc j) (hba : ∀ i j, b i ≠ anc j)
    (z : Qubits C.total) (hclean : ∀ j : Fin 1, z (anc j) = false) :
    act (C.subInPlaceC w a b anc hab haa hba).unitary (ket z) =
      ket (updateOn b z (natToBitsLSB w (2 ^ w + bitsToNatLSB (z ∘ b) - bitsToNatLSB (z ∘ a)))) := by
  have hact := C.O.act_subReg_perm (C.O.subInPlaceCircuit w) (subInPlaceFn54 w)
    (C.O.subInPlaceCircuit_implements w) (combineEmb54 a b hab) anc
    (C.combineEmb54_disj a b anc hab haa hba) z hclean
  change act (C.subInPlaceC w a b anc hab haa hba).unitary (ket z) = _ at hact
  rw [hact, updateOn_combineEmb54_right]
  · refine congrArg ket (congrArg (updateOn b z) (funext fun j => ?_))
    dsimp only [subInPlaceFn54, Function.comp_apply]
    rw [dif_neg (by simp)]
    have ha_eq : (fun i : Fin w => z (combineEmb54 a b hab ⟨i.1, by omega⟩)) = z ∘ a := by
      funext i
      have hi : (⟨i.1, by omega⟩ : Fin (w + w)) = Fin.castAdd w i := rfl
      rw [hi, combineEmb54_castAdd]; rfl
    have hb_eq : (fun i : Fin w => z (combineEmb54 a b hab ⟨w + i.1, by omega⟩)) = z ∘ b := by
      funext i
      have hi : (⟨w + i.1, by omega⟩ : Fin (w + w)) = Fin.natAdd w i := rfl
      rw [hi, combineEmb54_natAdd]; rfl
    rw [ha_eq, hb_eq]
    exact congrArg (natToBitsLSB w (2 ^ w + bitsToNatLSB (z ∘ b) - bitsToNatLSB (z ∘ a)))
      (Fin.ext (by simp))
  · intro i
    dsimp only [subInPlaceFn54, Function.comp_apply]
    rw [dif_pos (by simp)]
    calc z ((combineEmb54 a b hab) ⟨(Fin.castAdd w i).1, _⟩)
        = z ((combineEmb54 a b hab) (Fin.castAdd w i)) :=
          congrArg z (congrArg (combineEmb54 a b hab) (Fin.ext (by simp)))
      _ = z (a i) := by rw [combineEmb54_castAdd]

noncomputable def ctrlCopyRegC (w : ℕ) (ctrl : Fin 1 ↪ Fin C.total) (src dst : Fin w ↪ Fin C.total)
    (hcs : ∀ i j, ctrl i ≠ src j) (hcd : ∀ i j, ctrl i ≠ dst j) (hsd : ∀ i j, src i ≠ dst j) :
    LayeredCircuit C.total :=
  let embCS := combineEmb54 ctrl src hcs
  (C.O.ctrlCopyRegCircuit w).mapWires
    (C.padZeroEmb (combineEmb54 embCS dst (C.combineEmb54_disj ctrl src dst hcs hcd hsd)))

lemma ctrlCopyRegC_size (w : ℕ) (ctrl : Fin 1 ↪ Fin C.total) (src dst : Fin w ↪ Fin C.total)
    (hcs : ∀ i j, ctrl i ≠ src j) (hcd : ∀ i j, ctrl i ≠ dst j) (hsd : ∀ i j, src i ≠ dst j) :
    (C.ctrlCopyRegC w ctrl src dst hcs hcd hsd).size = 5 * w := by
  simpa [ctrlCopyRegC] using C.O.ctrlCopyRegCircuit_size w

lemma act_ctrlCopyRegC (w : ℕ) (ctrl : Fin 1 ↪ Fin C.total) (src dst : Fin w ↪ Fin C.total)
    (hcs : ∀ i j, ctrl i ≠ src j) (hcd : ∀ i j, ctrl i ≠ dst j) (hsd : ∀ i j, src i ≠ dst j)
    (z : Qubits C.total) :
    act (C.ctrlCopyRegC w ctrl src dst hcs hcd hsd).unitary (ket z) =
      ket (updateOn dst z (fun j => if z (ctrl 0) then xor (z (dst j)) (z (src j)) else z (dst j))) := by
  let embCS := combineEmb54 ctrl src hcs
  have hdisj : ∀ i j, embCS i ≠ dst j := C.combineEmb54_disj ctrl src dst hcs hcd hsd
  have hact := C.O.act_subReg_perm (C.O.ctrlCopyRegCircuit w) (ctrlCopyRegFn54 w)
    (C.O.ctrlCopyRegCircuit_implements w) (combineEmb54 embCS dst hdisj) C.zeroEmb0
    (fun _ j => Fin.elim0 j) z (fun j => Fin.elim0 j)
  change act (C.ctrlCopyRegC w ctrl src dst hcs hcd hsd).unitary (ket z) = _ at hact
  rw [hact, updateOn_combineEmb54_right]
  · refine congrArg ket (congrArg (updateOn dst z) (funext fun j => ?_))
    have hctrl : z ((combineEmb54 embCS dst hdisj) ⟨0, by omega⟩) = z (ctrl 0) := by
      have h0 : (⟨0, by omega⟩ : Fin (1 + w + w)) = Fin.castAdd w (Fin.castAdd w 0) := rfl
      rw [h0, combineEmb54_castAdd, combineEmb54_castAdd]
    have hsrc : z ((combineEmb54 embCS dst hdisj) ⟨1 + w + j.1 - w, by omega⟩) =
        z (src j) := by
      have hsub : (⟨1 + w + j.1 - w, by omega⟩ : Fin (1 + w + w)) =
          Fin.castAdd w (Fin.natAdd 1 j) := Fin.ext (by simp; omega)
      rw [hsub, combineEmb54_castAdd, combineEmb54_natAdd]
    dsimp only [ctrlCopyRegFn54, Function.comp_apply]
    simp only [hctrl]
    by_cases hcz : z (ctrl 0) = true
    · simp [hcz, combineEmb54_natAdd, hsrc]
    · simp [hcz, combineEmb54_natAdd]
  · intro i
    have hctrl : z ((combineEmb54 embCS dst hdisj) ⟨0, by omega⟩) = z (ctrl 0) := by
      have h0 : (⟨0, by omega⟩ : Fin (1 + w + w)) = Fin.castAdd w (Fin.castAdd w 0) := rfl
      rw [h0, combineEmb54_castAdd, combineEmb54_castAdd]
    dsimp only [ctrlCopyRegFn54, Function.comp_apply]
    simp only [hctrl]
    rw [combineEmb54_castAdd]
    by_cases hcz : z (ctrl 0) = true <;> simp [hcz]

noncomputable def sortKeyC (w_k w_p : ℕ) (arrEmb : Fin (C.M * (w_k + w_p)) ↪ Fin C.total)
    (ancEmb : Fin w_k ↪ Fin C.total)
    (hAT : ∀ i j, arrEmb i ≠ C.trEmb j)
    (hAA : ∀ i k, arrEmb i ≠ ancEmb k)
    (hTA : ∀ j k, C.trEmb j ≠ ancEmb k) : LayeredCircuit C.total :=
  let embDT := combineEmb54 arrEmb C.trEmb hAT
  let embDTA := combineEmb54 embDT ancEmb (C.combineEmb54_disj arrEmb C.trEmb ancEmb hAT hAA hTA)
  (C.R.bitonicSortKeyCircuit C.d w_k w_p true).mapWires embDTA

lemma sortKeyC_size (w_k w_p : ℕ) (arrEmb : Fin (C.M * (w_k + w_p)) ↪ Fin C.total)
    (ancEmb : Fin w_k ↪ Fin C.total)
    (hAT : ∀ i j, arrEmb i ≠ C.trEmb j)
    (hAA : ∀ i k, arrEmb i ≠ ancEmb k)
    (hTA : ∀ j k, C.trEmb j ≠ ancEmb k) :
    ((C.sortKeyC w_k w_p arrEmb ancEmb hAT hAA hTA).size : ℝ) ≤
      C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (w_k + w_p + 1 : ℝ) := by
  simpa [sortKeyC] using C.R.bitonicSortKeyCircuit_size C.d w_k w_p true

lemma act_sortKeyC (w_k w_p : ℕ) (arrEmb : Fin (C.M * (w_k + w_p)) ↪ Fin C.total)
    (ancEmb : Fin w_k ↪ Fin C.total)
    (hAT : ∀ i j, arrEmb i ≠ C.trEmb j)
    (hAA : ∀ i k, arrEmb i ≠ ancEmb k)
    (hTA : ∀ j k, C.trEmb j ≠ ancEmb k)
    (z : Qubits C.total) (x : Fin C.M → Qubits (w_k + w_p))
    (harr : z ∘ arrEmb = flatReg C.M (w_k + w_p) x)
    (htr : z ∘ C.trEmb = fun _ => false)
    (hanc : z ∘ ancEmb = fun _ => false) :
    let embDT := combineEmb54 arrEmb C.trEmb hAT
    let xs := sort (fun r => bitsToNat (recKey54 r)) C.d true x
    let trs := sortTrace (fun r => bitsToNat (recKey54 r)) C.d true x
    act (C.sortKeyC w_k w_p arrEmb ancEmb hAT hAA hTA).unitary (ket z) =
      ket (updateOn embDT z (Fin.append (flatReg C.M (w_k + w_p) xs) trs)) := by
  intro embDT xs trs
  let hDTA := C.combineEmb54_disj arrEmb C.trEmb ancEmb hAT hAA hTA
  let embDTA := combineEmb54 embDT ancEmb hDTA
  have hz_comp : z ∘ embDTA = packDTA54 C.M (w_k + w_p) C.T w_k x (fun _ => false) := by
    funext u
    refine Fin.addCases (fun i => ?_) (fun j => ?_) u
    · refine Fin.addCases (fun ia => ?_) (fun it => ?_) i
      · simp only [Function.comp_apply, embDTA, embDT, combineEmb54_castAdd, packDTA54,
          padZero_castAdd, Fin.append_left]
        exact congrFun harr ia
      · simp only [Function.comp_apply, embDTA, embDT, combineEmb54_castAdd, combineEmb54_natAdd,
          packDTA54, padZero_castAdd, Fin.append_right]
        exact congrFun htr it
    · simp only [Function.comp_apply, embDTA, combineEmb54_natAdd, packDTA54, padZero_natAdd]
      exact congrFun hanc j
  have hact_base := C.R.act_bitonicSortKeyCircuit_ket C.d w_k w_p true x
  rw [← hz_comp] at hact_base
  refine act_mapWires_ket (C.R.bitonicSortKeyCircuit C.d w_k w_p true) embDTA z _ hact_base _ ?_ ?_
  · funext u
    refine Fin.addCases (fun i => ?_) (fun j => ?_) u
    · dsimp only [Function.comp_apply, embDTA]
      rw [combineEmb54_castAdd, updateOn_apply_emb]
      simp only [packDTA54, padZero_castAdd]
      rfl
    · have hj_not : ancEmb j ∉ Set.range embDT := by
        rintro ⟨i, hi⟩
        exact hDTA i j hi
      dsimp only [Function.comp_apply, embDTA]
      rw [combineEmb54_natAdd, updateOn_apply_not_mem _ _ _ hj_not]
      simp only [packDTA54, padZero_natAdd]
      exact congrFun hanc j
  · intro i hi
    have hi_dt : i ∉ Set.range embDT := fun ⟨u, hu⟩ => hi ⟨Fin.castAdd w_k u, by simpa [embDTA] using hu⟩
    exact updateOn_apply_not_mem _ _ _ hi_dt

lemma act_sortKeyC_adj (w_k w_p : ℕ) (arrEmb : Fin (C.M * (w_k + w_p)) ↪ Fin C.total)
    (ancEmb : Fin w_k ↪ Fin C.total)
    (hAT : ∀ i j, arrEmb i ≠ C.trEmb j)
    (hAA : ∀ i k, arrEmb i ≠ ancEmb k)
    (hTA : ∀ j k, C.trEmb j ≠ ancEmb k)
    (z : Qubits C.total)
    (k_in : Fin C.M → Qubits w_k) (y_p : Fin C.M → Qubits w_p)
    (harr : z ∘ arrEmb = flatReg C.M (w_k + w_p) (fun i => Fin.append (sort bitsToNat C.d true k_in i) (y_p i)))
    (htr : z ∘ C.trEmb = sortTrace bitsToNat C.d true k_in)
    (hanc : z ∘ ancEmb = fun _ => false) :
    let embDT := combineEmb54 arrEmb C.trEmb hAT
    let y_out := unrouteSort C.d (sortTrace bitsToNat C.d true k_in) y_p
    act (C.sortKeyC w_k w_p arrEmb ancEmb hAT hAA hTA).adj.unitary (ket z) =
      ket (updateOn embDT z (Fin.append (flatReg C.M (w_k + w_p) fun i => Fin.append (k_in i) (y_out i)) (fun _ => false))) := by
  intro embDT y_out
  let hDTA := C.combineEmb54_disj arrEmb C.trEmb ancEmb hAT hAA hTA
  let embDTA := combineEmb54 embDT ancEmb hDTA
  have hz_comp : z ∘ embDTA =
      packDTA54 C.M (w_k + w_p) C.T w_k
        (fun i => Fin.append (sort bitsToNat C.d true k_in i) (y_p i))
        (sortTrace bitsToNat C.d true k_in) := by
    funext u
    refine Fin.addCases (fun i => ?_) (fun j => ?_) u
    · refine Fin.addCases (fun ia => ?_) (fun it => ?_) i
      · simp only [Function.comp_apply, embDTA, embDT, combineEmb54_castAdd, packDTA54,
          padZero_castAdd, Fin.append_left]
        exact congrFun harr ia
      · simp only [Function.comp_apply, embDTA, embDT, combineEmb54_castAdd, combineEmb54_natAdd,
          packDTA54, padZero_castAdd, Fin.append_right]
        exact congrFun htr it
    · simp only [Function.comp_apply, embDTA, combineEmb54_natAdd, packDTA54, padZero_natAdd]
      exact congrFun hanc j
  have hact_base := C.R.act_bitonicSortKeyCircuit_adj_unroute C.d w_k w_p true k_in y_p
  rw [← hz_comp] at hact_base
  change act ((C.R.bitonicSortKeyCircuit C.d w_k w_p true).mapWires embDTA).adj.unitary (ket z) = _
  rw [mapWires_adj_unitary]
  refine act_mapWires_ket (C.R.bitonicSortKeyCircuit C.d w_k w_p true).adj embDTA z _ hact_base _ ?_ ?_
  · funext u
    refine Fin.addCases (fun i => ?_) (fun j => ?_) u
    · dsimp only [Function.comp_apply, embDTA]
      rw [combineEmb54_castAdd, updateOn_apply_emb]
      simp only [packDTA54, padZero_castAdd]
      rfl
    · have hj_not : ancEmb j ∉ Set.range embDT := by rintro ⟨i, hi⟩; exact hDTA i j hi
      dsimp only [Function.comp_apply, embDTA]
      rw [combineEmb54_natAdd, updateOn_apply_not_mem _ _ _ hj_not]
      simp only [packDTA54, padZero_natAdd]
      exact congrFun hanc j
  · intro i hi
    have hi_dt : i ∉ Set.range embDT := fun ⟨u, hu⟩ => hi ⟨Fin.castAdd w_k u, by simpa [embDTA] using hu⟩
    exact updateOn_apply_not_mem _ _ _ hi_dt

noncomputable def encodeSymC (r : Fin C.N) (ancSym : Fin (C.s - 1) ↪ Fin C.total)
    (hLA : ∀ i j, C.lSlotEmb r i ≠ ancSym j) : LayeredCircuit C.total :=
  (C.O.encodeParticleSym54Circuit C.n C.s rfl).mapWires (combineEmb54 (C.lSlotEmb r) ancSym hLA)

lemma encodeSymC_size (r : Fin C.N) (ancSym : Fin (C.s - 1) ↪ Fin C.total)
    (hLA : ∀ i j, C.lSlotEmb r i ≠ ancSym j) :
    (C.encodeSymC r ancSym hLA).size ≤ 13 * C.s := by
  simpa [encodeSymC] using C.O.encodeParticleSym54Circuit_size C.n C.s rfl

lemma act_encodeSymC (r : Fin C.N) (ancSym : Fin (C.s - 1) ↪ Fin C.total)
    (hLA : ∀ i j, C.lSlotEmb r i ≠ ancSym j)
    (z : Qubits C.total) (j : Fin (C.n + 1))
    (hL : z ∘ C.lSlotEmb r = natToBits C.s j.1)
    (hanc : ∀ k : Fin (C.s - 1), z (ancSym k) = false) :
    act (C.encodeSymC r ancSym hLA).unitary (ket z) =
      ket (updateOn (C.lSlotEmb r) z (particleSym54 C.n C.s j)) := by
  let embSym := combineEmb54 (C.lSlotEmb r) ancSym hLA
  have hz_comp : z ∘ embSym = padZero C.s (C.s - 1) (natToBits C.s j.1) := by
    funext u
    refine Fin.addCases (fun i => ?_) (fun k => ?_) u
    · simp only [Function.comp_apply, embSym, combineEmb54_castAdd, padZero_castAdd]
      exact congrFun hL i
    · simp only [Function.comp_apply, embSym, combineEmb54_natAdd, padZero_natAdd]
      exact hanc k
  have hact_base := C.O.encodeParticleSym54Circuit_act C.n C.s C.hn rfl j
  rw [← hz_comp] at hact_base
  refine act_mapWires_ket (C.O.encodeParticleSym54Circuit C.n C.s rfl) embSym z _ hact_base _ ?_ ?_
  · funext u
    refine Fin.addCases (fun i => ?_) (fun k => ?_) u
    · simp only [Function.comp_apply, embSym, combineEmb54_castAdd, padZero_castAdd]
      rw [updateOn_apply_emb]
    · have hk_not : ancSym k ∉ Set.range (C.lSlotEmb r) := fun ⟨i, hi⟩ => hLA i k hi
      simp only [Function.comp_apply, embSym, combineEmb54_natAdd, padZero_natAdd]
      rw [updateOn_apply_not_mem _ _ _ hk_not, hanc k]
  · intro i hi
    have hi_L : i ∉ Set.range (C.lSlotEmb r) := fun ⟨u, hu⟩ => hi ⟨Fin.castAdd (C.s - 1) u, by simpa [embSym] using hu⟩
    exact updateOn_apply_not_mem _ _ _ hi_L

end OccCtx

end QuantumLTF.Membership.Supplement.StageA


/-! ### Stage A State Packing, Bit Helpers & Single-Region `updateOn` Lemmas -/

namespace QuantumLTF.Membership.Supplement.StageA

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open Thm49Primitives Thm410Router Cslib.BitonicSort

@[simp] lemma flatReg_apply' {N w : ℕ} (x : Fin N → Qubits w) (r : Fin N) (b : Fin w) :
    flatReg N w x (finProdFinEquiv (r, b)) = x r b := by
  simp [flatReg]

lemma natToBitsLSB_zero' (w : ℕ) : natToBitsLSB w 0 = fun _ => false := by
  funext i; simp [natToBitsLSB]

lemma natToBitsLSB_mod_eq' (w x : ℕ) : natToBitsLSB w (x % 2 ^ w) = natToBitsLSB w x := by
  funext i; simp [natToBitsLSB, Nat.testBit_mod_two_pow, i.isLt]

lemma bitsToNatLSB_natToBitsLSB_mod' (w x : ℕ) :
    bitsToNatLSB (natToBitsLSB w x) = x % 2 ^ w := by
  rw [← natToBitsLSB_mod_eq' w x]
  exact bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))

lemma natToBits_eq_pad_natToBitsLSB (O : OccArith54) {q w v : ℕ}
    (hwq : w ≤ q) (hv : v < 2 ^ w) (j : Fin q) :
    natToBits q v j =
      if _ : j.1 < q - w then false else natToBitsLSB w v ⟨q - 1 - j.1, by omega⟩ := by
  have hvq : v < 2 ^ q := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hwq)
  rw [O.natToBits_apply hvq j]
  simp only [natToBitsLSB, Fin.val_rev]
  have hrev : q - (j.1 + 1) = q - 1 - j.1 := by omega
  rw [hrev]
  by_cases h : j.1 < q - w
  · rw [dif_pos h]
    have hpow : 2 ^ w ≤ 2 ^ (q - 1 - j.1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv hpow)
  · rw [dif_neg h]

lemma natToBits_zero_all (O : OccArith54) (q : ℕ) : natToBits q 0 = fun _ => false := by
  funext j
  rw [O.natToBits_apply (Nat.two_pow_pos q) j]
  simp [natToBitsLSB]

namespace OccCtx

variable (C : OccCtx)

lemma q_pos : 0 < C.q := by
  have := C.w_v_ge_two
  have := C.w_v_le_q
  omega

lemma w_v_pos : 0 < C.w_v := by
  have := C.w_v_ge_two
  omega

lemma s_pos : 0 < C.s := by
  dsimp only [s]; omega

lemma w_a_pos : 0 < C.w_a := by
  dsimp only [w_a]; have := C.s_pos; omega

lemma w_rec_pos : 0 < C.w_rec := by
  dsimp only [w_rec, w_k2, w_p2]; have := C.w_a_pos; omega

lemma d_ge_two : 2 ≤ C.d := by
  dsimp only [d, m, N]
  have hn := C.hn; have hK := C.hK
  have hle : C.n + 1 + 2 * C.K ≤ 2 ^ Nat.clog 2 (C.n + 1 + 2 * C.K) :=
    Nat.le_pow_clog (by norm_num : 1 < 2) _
  by_contra hlt
  have hd : Nat.clog 2 (C.n + 1 + 2 * C.K) ≤ 1 := by omega
  have hp : 2 ^ Nat.clog 2 (C.n + 1 + 2 * C.K) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hd
  omega

lemma T_pos : 0 < C.T := by
  have ht := C.R.four_mul_sortTraceSize C.d
  have hd := C.d_ge_two
  have hpow : 4 ≤ 2 ^ C.d := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hd
  have h12 : 2 * 3 ≤ C.d * (C.d + 1) := by nlinarith
  have hmul : 2 * 3 * 4 ≤ C.d * (C.d + 1) * 2 ^ C.d :=
    le_trans (Nat.mul_le_mul_right 4 h12) (Nat.mul_le_mul_left (C.d * (C.d + 1)) hpow)
  dsimp only [T]
  omega

@[simp] lemma kEmbLSB_val (u : Fin C.w_v) : (C.kEmbLSB u).1 = C.offK + u.1 := rfl
@[simp] lemma lSlotEmb_val (r : Fin C.N) (b : Fin C.s) :
    (C.lSlotEmb r b).1 = C.offL + r.1 * C.s + b.1 := by
  change C.offL + r.1 * C.s + 0 + b.1 = _; omega
@[simp] lemma pSlotEmbLSB_val (i : Fin C.n) (u : Fin C.w_v) :
    (C.pSlotEmbLSB i u).1 = C.offP + i.1 * C.w_v + u.1 := by
  change C.offP + i.1 * C.w_v + 0 + u.1 = _; omega
@[simp] lemma trEmb_val (u : Fin C.T) : (C.trEmb u).1 = C.offTr + u.1 := rfl
@[simp] lemma scrEmb_val (off len : ℕ) (h : off + len ≤ C.lenScr) (u : Fin len) :
    (C.scrEmb off len h u).1 = C.offScr + off + u.1 := by
  change (C.offScr + off) + u.1 = _; omega

/-- Pack all Stage A registers `(A, K, L, P, Arr, Tr, Scr)` into `Qubits C.total`.
Upper `q - w_v` bits of each `A[i]` are fixed `false`. -/
def packStage
    (A : Fin C.n → Qubits C.w_v)
    (K : Qubits C.w_v)
    (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v)
    (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T)
    (Scr : Qubits C.lenScr) : Qubits C.total := fun u =>
  if hA : u.1 < C.offK then
    let i : Fin C.n := ⟨u.1 / C.q, Nat.div_lt_of_lt_mul (by
      dsimp [offK, lenA] at hA; rw [mul_comm]; exact hA)⟩
    let j := u.1 % C.q
    if hj : j < C.q - C.w_v then false
    else
      have hq := C.q_pos
      have hj_lt : j < C.q := Nat.mod_lt u.1 hq
      A i ⟨C.q - 1 - j, by omega⟩
  else if hK : u.1 < C.offL then
    K ⟨u.1 - C.offK, by dsimp only [offL, lenK] at hK; omega⟩
  else if hL : u.1 < C.offP then
    let rel := u.1 - C.offL
    have hs := C.s_pos
    have hrel : rel < C.s * C.N := by dsimp only [offP, lenL] at hL; rw [mul_comm]; omega
    L ⟨rel / C.s, Nat.div_lt_of_lt_mul hrel⟩ ⟨rel % C.s, Nat.mod_lt rel hs⟩
  else if hP : u.1 < C.offArr then
    let rel := u.1 - C.offP
    have hw := C.w_v_pos
    have hrel : rel < C.w_v * C.n := by dsimp only [offArr, lenP] at hP; rw [mul_comm]; omega
    P ⟨rel / C.w_v, Nat.div_lt_of_lt_mul hrel⟩ ⟨rel % C.w_v, Nat.mod_lt rel hw⟩
  else if hArr : u.1 < C.offTr then
    let rel := u.1 - C.offArr
    have hwr := C.w_rec_pos
    have hrel : rel < C.w_rec * C.M := by dsimp only [offTr, lenArr] at hArr; rw [mul_comm]; omega
    Arr ⟨rel / C.w_rec, Nat.div_lt_of_lt_mul hrel⟩ ⟨rel % C.w_rec, Nat.mod_lt rel hwr⟩
  else if hTr : u.1 < C.offScr then
    Tr ⟨u.1 - C.offTr, by dsimp only [offScr, lenTr] at hTr; omega⟩
  else
    Scr ⟨u.1 - C.offScr, by
      have hu : u.1 < C.offScr + C.lenScr := by rw [← C.total_eq]; exact u.isLt
      omega⟩

abbrev packState
    (A : Fin C.n → Qubits C.w_v)
    (K : Qubits C.w_v)
    (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v)
    (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) : Qubits C.total :=
  C.packStage A K L P Arr Tr (fun _ => false)

lemma aLowEmbLSB_div_mod (i : Fin C.n) (u : Fin C.w_v) :
    (C.aLowEmbLSB i u).1 < C.offK ∧
      (C.aLowEmbLSB i u).1 / C.q = i.1 ∧
      (C.aLowEmbLSB i u).1 % C.q = C.q - 1 - u.1 ∧
      ¬ ((C.aLowEmbLSB i u).1 % C.q < C.q - C.w_v) := by
  have hi := i.isLt
  have hu := u.isLt
  have hqw := C.w_v_le_q
  have hq := C.q_pos
  have hlt_q : C.q - 1 - u.1 < C.q := by omega
  have hmul : (i.1 + 1) * C.q ≤ C.n * C.q := Nat.mul_le_mul_right C.q hi
  have hstep : i.1 * C.q + C.q ≤ C.n * C.q := by simpa [Nat.succ_mul] using hmul
  have hdiv : (i.1 * C.q + (C.q - 1 - u.1)) / C.q = i.1 := by
    rw [mul_comm i.1 C.q, Nat.mul_add_div hq, Nat.div_eq_of_lt hlt_q, add_zero]
  have hmod : (i.1 * C.q + (C.q - 1 - u.1)) % C.q = C.q - 1 - u.1 := by
    rw [mul_comm i.1 C.q, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt_q]
  simp only [aLowEmbLSB_val, offK, lenA]
  refine ⟨by omega, hdiv, hmod, by rw [hmod]; omega⟩

@[simp] lemma packStage_aLowEmbLSB
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (i : Fin C.n) (u : Fin C.w_v) :
    C.packStage A K L P Arr Tr Scr (C.aLowEmbLSB i u) = A i u := by
  rcases C.aLowEmbLSB_div_mod i u with ⟨hlt, hdiv, hmod, hnot⟩
  have hu := u.isLt; have hqw := C.w_v_le_q
  dsimp only [packStage]
  rw [dif_pos hlt, dif_neg hnot]
  congr 1
  · exact Fin.ext hdiv
  · exact Fin.ext (by simp only [hmod]; omega)

@[simp] lemma packStage_kEmbLSB
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (u : Fin C.w_v) :
    C.packStage A K L P Arr Tr Scr (C.kEmbLSB u) = K u := by
  have hu := u.isLt
  have hval := C.kEmbLSB_val u
  have h1 : ¬ (C.kEmbLSB u).1 < C.offK := by omega
  have h2 : (C.kEmbLSB u).1 < C.offL := by dsimp only [offL, lenK]; omega
  dsimp only [packStage]
  rw [dif_neg h1, dif_pos h2]
  exact congrArg K (Fin.ext (by dsimp only; omega))

@[simp] lemma packStage_lSlotEmb
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (r : Fin C.N) (b : Fin C.s) :
    C.packStage A K L P Arr Tr Scr (C.lSlotEmb r b) = L r b := by
  have hr := r.isLt; have hb := b.isLt; have hs := C.s_pos
  have hval := C.lSlotEmb_val r b
  have h1 : ¬ (C.lSlotEmb r b).1 < C.offK := by dsimp [offL, offK, lenK] at *; omega
  have h2 : ¬ (C.lSlotEmb r b).1 < C.offL := by omega
  have h3 : (C.lSlotEmb r b).1 < C.offP := by
    dsimp only [offP, lenL]
    have hmul : (r.1 + 1) * C.s ≤ C.N * C.s := Nat.mul_le_mul_right C.s hr
    have hstep : r.1 * C.s + C.s ≤ C.N * C.s := by simpa [Nat.succ_mul] using hmul
    omega
  dsimp only [packStage]
  rw [dif_neg h1, dif_neg h2, dif_pos h3]
  have hrel : (C.lSlotEmb r b).1 - C.offL = r.1 * C.s + b.1 := by omega
  have hdiv : ((C.lSlotEmb r b).1 - C.offL) / C.s = r.1 := by
    rw [hrel, mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt hb, add_zero]
  have hmod : ((C.lSlotEmb r b).1 - C.offL) % C.s = b.1 := by
    rw [hrel, mul_comm r.1 C.s, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  congr 1 <;> exact Fin.ext (by first | exact hdiv | exact hmod)

@[simp] lemma packStage_lSlotEmbLSB
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (r : Fin C.N) (u : Fin C.s) :
    C.packStage A K L P Arr Tr Scr (C.lSlotEmbLSB r u) = L r u.rev :=
  C.packStage_lSlotEmb A K L P Arr Tr Scr r u.rev

@[simp] lemma packStage_pSlotEmbLSB
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (i : Fin C.n) (u : Fin C.w_v) :
    C.packStage A K L P Arr Tr Scr (C.pSlotEmbLSB i u) = P i u := by
  have hi := i.isLt; have hu := u.isLt; have hw := C.w_v_pos
  have hval := C.pSlotEmbLSB_val i u
  have h1 : ¬ (C.pSlotEmbLSB i u).1 < C.offK := by
    dsimp [offP, offL, offK, lenL, lenK] at *; omega
  have h2 : ¬ (C.pSlotEmbLSB i u).1 < C.offL := by dsimp [offP, offL, lenL] at *; omega
  have h3 : ¬ (C.pSlotEmbLSB i u).1 < C.offP := by omega
  have h4 : (C.pSlotEmbLSB i u).1 < C.offArr := by
    dsimp only [offArr, lenP]
    have hmul : (i.1 + 1) * C.w_v ≤ C.n * C.w_v := Nat.mul_le_mul_right C.w_v hi
    have hstep : i.1 * C.w_v + C.w_v ≤ C.n * C.w_v := by simpa [Nat.succ_mul] using hmul
    omega
  dsimp only [packStage]
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]
  have hrel : (C.pSlotEmbLSB i u).1 - C.offP = i.1 * C.w_v + u.1 := by omega
  have hdiv : ((C.pSlotEmbLSB i u).1 - C.offP) / C.w_v = i.1 := by
    rw [hrel, mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt hu, add_zero]
  have hmod : ((C.pSlotEmbLSB i u).1 - C.offP) % C.w_v = u.1 := by
    rw [hrel, mul_comm i.1 C.w_v, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
  congr 1 <;> exact Fin.ext (by first | exact hdiv | exact hmod)

@[simp] lemma packStage_arr2AllEmb
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (pos : Fin C.M) (u : Fin C.w_rec) :
    C.packStage A K L P Arr Tr Scr (C.arr2AllEmb (finProdFinEquiv (pos, u))) = Arr pos u := by
  have hp := pos.isLt; have hu := u.isLt; have hwr := C.w_rec_pos
  have hval := C.arr2AllEmb_pair pos u
  have h1 : ¬ (C.arr2AllEmb (finProdFinEquiv (pos, u))).1 < C.offK := by
    dsimp [offArr, offP, offL, offK, lenP, lenL, lenK] at *; omega
  have h2 : ¬ (C.arr2AllEmb (finProdFinEquiv (pos, u))).1 < C.offL := by
    dsimp [offArr, offP, offL, lenP, lenL] at *; omega
  have h3 : ¬ (C.arr2AllEmb (finProdFinEquiv (pos, u))).1 < C.offP := by
    dsimp [offArr, offP, lenP] at *; omega
  have h4 : ¬ (C.arr2AllEmb (finProdFinEquiv (pos, u))).1 < C.offArr := by omega
  have h5 : (C.arr2AllEmb (finProdFinEquiv (pos, u))).1 < C.offTr := by
    dsimp only [offTr, lenArr]
    have hmul : (pos.1 + 1) * C.w_rec ≤ C.M * C.w_rec := Nat.mul_le_mul_right C.w_rec hp
    have hstep : pos.1 * C.w_rec + C.w_rec ≤ C.M * C.w_rec := by simpa [Nat.succ_mul] using hmul
    omega
  dsimp only [packStage]
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_pos h5]
  have hrel : (C.arr2AllEmb (finProdFinEquiv (pos, u))).1 - C.offArr = pos.1 * C.w_rec + u.1 := by omega
  have hdiv : ((C.arr2AllEmb (finProdFinEquiv (pos, u))).1 - C.offArr) / C.w_rec = pos.1 := by
    rw [hrel, mul_comm, Nat.mul_add_div hwr, Nat.div_eq_of_lt hu, add_zero]
  have hmod : ((C.arr2AllEmb (finProdFinEquiv (pos, u))).1 - C.offArr) % C.w_rec = u.1 := by
    rw [hrel, mul_comm pos.1 C.w_rec, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
  congr 1 <;> exact Fin.ext (by first | exact hdiv | exact hmod)

@[simp] lemma packStage_trEmb
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (u : Fin C.T) :
    C.packStage A K L P Arr Tr Scr (C.trEmb u) = Tr u := by
  have hu := u.isLt
  have hval := C.trEmb_val u
  have h1 : ¬ (C.trEmb u).1 < C.offK := by
    dsimp [offTr, offArr, offP, offL, offK, lenArr, lenP, lenL, lenK] at *; omega
  have h2 : ¬ (C.trEmb u).1 < C.offL := by
    dsimp [offTr, offArr, offP, offL, lenArr, lenP, lenL] at *; omega
  have h3 : ¬ (C.trEmb u).1 < C.offP := by
    dsimp [offTr, offArr, offP, lenArr, lenP] at *; omega
  have h4 : ¬ (C.trEmb u).1 < C.offArr := by dsimp [offTr, offArr, lenArr] at *; omega
  have h5 : ¬ (C.trEmb u).1 < C.offTr := by omega
  have h6 : (C.trEmb u).1 < C.offScr := by dsimp only [offScr, lenTr] at *; omega
  dsimp only [packStage]
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_pos h6]
  exact congrArg Tr (Fin.ext (by dsimp only; omega))

@[simp] lemma packStage_scrEmb
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr)
    (off len : ℕ) (h : off + len ≤ C.lenScr) (u : Fin len) :
    C.packStage A K L P Arr Tr Scr (C.scrEmb off len h u) = Scr ⟨off + u.1, by have := u.isLt; omega⟩ := by
  have hu := u.isLt
  have hval := C.scrEmb_val off len h u
  have h1 : ¬ (C.scrEmb off len h u).1 < C.offK := by
    dsimp [offScr, offTr, offArr, offP, offL, offK, lenTr, lenArr, lenP, lenL, lenK] at *; omega
  have h2 : ¬ (C.scrEmb off len h u).1 < C.offL := by
    dsimp [offScr, offTr, offArr, offP, offL, lenTr, lenArr, lenP, lenL] at *; omega
  have h3 : ¬ (C.scrEmb off len h u).1 < C.offP := by
    dsimp [offScr, offTr, offArr, offP, lenTr, lenArr, lenP] at *; omega
  have h4 : ¬ (C.scrEmb off len h u).1 < C.offArr := by
    dsimp [offScr, offTr, offArr, lenTr, lenArr] at *; omega
  have h5 : ¬ (C.scrEmb off len h u).1 < C.offTr := by dsimp [offScr, offTr, lenTr] at *; omega
  have h6 : ¬ (C.scrEmb off len h u).1 < C.offScr := by omega
  dsimp only [packStage]
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6]
  exact congrArg Scr (Fin.ext (by dsimp only; omega))

lemma lenScr_full : 0 + C.lenScr ≤ C.lenScr := by omega

lemma eq_packStage_of_bounds (z : Qubits C.total)
    (hA_top : ∀ u : Fin C.total, u.1 < C.offK → u.1 % C.q < C.q - C.w_v → z u = false) :
    z = C.packStage
      (fun i u => z (C.aLowEmbLSB i u))
      (z ∘ C.kEmbLSB)
      (fun r b => z (C.lSlotEmb r b))
      (fun i u => z (C.pSlotEmbLSB i u))
      (fun pos u => z (C.arr2AllEmb (finProdFinEquiv (pos, u))))
      (z ∘ C.trEmb)
      (z ∘ C.scrEmb 0 C.lenScr C.lenScr_full) := by
  funext u
  dsimp only [packStage]
  by_cases hA : u.1 < C.offK
  · rw [dif_pos hA]
    by_cases hj : u.1 % C.q < C.q - C.w_v
    · rw [dif_pos hj]; exact hA_top u hA hj
    · rw [dif_neg hj]
      have hq := C.q_pos; have hqw := C.w_v_le_q
      have hmod_lt : u.1 % C.q < C.q := Nat.mod_lt u.1 hq
      congr 1; apply Fin.ext
      dsimp only [aLowEmbLSB_val]
      have hdm := Nat.div_add_mod u.1 C.q
      rw [Nat.mul_comm C.q _] at hdm; omega
  · rw [dif_neg hA]
    by_cases hK : u.1 < C.offL
    · rw [dif_pos hK]
      exact congrArg z (Fin.ext (by rw [C.kEmbLSB_val]; dsimp only; omega))
    · rw [dif_neg hK]
      by_cases hL : u.1 < C.offP
      · rw [dif_pos hL]
        have hdm := Nat.div_add_mod (u.1 - C.offL) C.s
        rw [Nat.mul_comm C.s _] at hdm
        exact congrArg z (Fin.ext (by rw [C.lSlotEmb_val]; dsimp only; omega))
      · rw [dif_neg hL]
        by_cases hP : u.1 < C.offArr
        · rw [dif_pos hP]
          have hdm := Nat.div_add_mod (u.1 - C.offP) C.w_v
          rw [Nat.mul_comm C.w_v _] at hdm
          exact congrArg z (Fin.ext (by rw [C.pSlotEmbLSB_val]; dsimp only; omega))
        · rw [dif_neg hP]
          by_cases hArr : u.1 < C.offTr
          · rw [dif_pos hArr]
            have hdm := Nat.div_add_mod (u.1 - C.offArr) C.w_rec
            rw [Nat.mul_comm C.w_rec _] at hdm
            congr 1; apply Fin.ext
            rw [C.arr2AllEmb_pair]; dsimp only; omega
          · rw [dif_neg hArr]
            by_cases hTr : u.1 < C.offScr
            · rw [dif_pos hTr]
              exact congrArg z (Fin.ext (by rw [C.trEmb_val]; dsimp only; omega))
            · rw [dif_neg hTr]
              exact congrArg z (Fin.ext (by rw [C.scrEmb_val]; dsimp only; omega))

lemma packStage_A_top_false
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr)
    (u : Fin C.total) (hA : u.1 < C.offK) (hj : u.1 % C.q < C.q - C.w_v) :
    C.packStage A K L P Arr Tr Scr u = false := by
  dsimp only [packStage]; rw [dif_pos hA, dif_pos hj]

/-- Initial input equality: `padZero (n*q) e_occ (flatReg n q (natToBits q ∘ α))` equals `packState`. -/
lemma padZero_flatReg_eq_packState
    (α : Fin C.n → ℕ) (hα : ∀ i : Fin C.n, α i < 2 ^ C.w_v) :
    padZero (C.n * C.q) C.e_occ (flatReg C.n C.q fun i => natToBits C.q (α i)) =
      C.packState (fun i => natToBitsLSB C.w_v (α i))
        (fun _ => false) (fun _ _ => false) (fun _ _ => false) (fun _ _ => false) (fun _ => false) := by
  funext u
  by_cases hu : u.1 < C.n * C.q
  · have hA : u.1 < C.offK := hu
    rw [C.O.padZero_val_lt _ u hu]
    have hq := C.q_pos
    have hlt_mul : u.1 < C.q * C.n := by simpa [Nat.mul_comm] using hu
    let i : Fin C.n := ⟨u.1 / C.q, Nat.div_lt_of_lt_mul hlt_mul⟩
    let j : Fin C.q := ⟨u.1 % C.q, Nat.mod_lt u.1 hq⟩
    have hpair : finProdFinEquiv (i, j) = ⟨u.1, hu⟩ := by
      apply Fin.ext
      dsimp only [finProdFinEquiv, Equiv.coe_fn_mk, i, j]
      have hdm := Nat.div_add_mod u.1 C.q
      omega
    have hflat : flatReg C.n C.q (fun r => natToBits C.q (α r)) ⟨u.1, hu⟩ =
        natToBits C.q (α i) j := by
      rw [← hpair, flatReg_apply']
    rw [hflat, natToBits_eq_pad_natToBitsLSB C.O C.w_v_le_q (hα i) j]
    dsimp only [packState, packStage]
    rw [dif_pos hA]
  · rw [C.O.padZero_val_ge _ u (by omega)]
    dsimp only [packState, packStage]
    have h1 : ¬ u.1 < C.offK := by dsimp [offK, lenA]; omega
    rw [dif_neg h1]
    split_ifs <;> rfl

/-- Final output equality for `degState_occ k`. -/
lemma embedPartAndDeg54_eq_packState
    (k : ℕ) (L : Fin C.N → Qubits C.s) :
    let degState := C.packState (fun _ _ => false) (natToBitsLSB C.w_v k)
      (fun _ _ => false) (fun _ _ => false) (fun _ _ => false) (fun _ => false)
    embedPartAndDeg54 C.partEmb (ket (flatReg C.N C.s L)) degState =
      ket (C.packState (fun _ _ => false) (natToBitsLSB C.w_v k) L
        (fun _ _ => false) (fun _ _ => false) (fun _ => false)) := by
  intro degState
  refine embedPartAndDeg54_ket_eq C.partEmb (flatReg C.N C.s L) degState _ ?_ ?_
  · intro idx
    rcases finProdFinEquiv.surjective idx with ⟨⟨r, b⟩, rfl⟩
    rw [← C.lSlotEmb_eq_partEmb r b, flatReg_apply']
    exact C.packStage_lSlotEmb _ _ _ _ _ _ _ r b
  · intro a ha
    have hnot : ¬ (C.offL ≤ a.1 ∧ a.1 < C.offP) := by
      rintro ⟨h1, h2⟩
      apply ha
      refine ⟨⟨a.1 - C.offL, by dsimp [offP, lenL] at h2; omega⟩, ?_⟩
      apply Fin.ext; simp only [partEmb, segEmb_val]; omega
    dsimp only [degState, packState, packStage]
    by_cases hA : a.1 < C.offK
    · simp only [hA, ↓reduceDIte]
    · simp only [hA, ↓reduceDIte]
      by_cases hK : a.1 < C.offL
      · simp [hK]
      · simp only [hK, ↓reduceDIte]
        by_cases hL : a.1 < C.offP
        · exfalso; exact hnot ⟨by omega, hL⟩
        · simp [hL]

/-! ### Range Disjointness & `updateOn` Preservation Lemmas for `packStage` -/

lemma emb_disj_of_bounds {a b : ℕ} (ea : Fin a ↪ Fin C.total) (eb : Fin b ↪ Fin C.total)
    (lo₁ hi₁ lo₂ hi₂ : ℕ)
    (h1 : ∀ i, lo₁ ≤ (ea i).1 ∧ (ea i).1 < hi₁)
    (h2 : ∀ j, lo₂ ≤ (eb j).1 ∧ (eb j).1 < hi₂)
    (hdisj : hi₁ ≤ lo₂ ∨ hi₂ ≤ lo₁) : ∀ i j, ea i ≠ eb j := fun i j heq => by
  have := h1 i; have := h2 j; have := congrArg Fin.val heq; omega

lemma emb_disj_symm {a b : ℕ} {ea : Fin a ↪ Fin C.total} {eb : Fin b ↪ Fin C.total}
    (h : ∀ i j, ea i ≠ eb j) : ∀ j i, eb j ≠ ea i := fun j i heq => h i j heq.symm

lemma aLowEmbLSB_bounds (i : Fin C.n) (u : Fin C.w_v) :
    0 ≤ (C.aLowEmbLSB i u).1 ∧ (C.aLowEmbLSB i u).1 < C.offK :=
  ⟨Nat.zero_le _, (C.aLowEmbLSB_div_mod i u).1⟩

lemma kEmbLSB_bounds (u : Fin C.w_v) :
    C.offK ≤ (C.kEmbLSB u).1 ∧ (C.kEmbLSB u).1 < C.offL := by
  have := u.isLt; rw [C.kEmbLSB_val]; dsimp [offL, lenK]; omega

lemma lSlotEmb_bounds (r : Fin C.N) (b : Fin C.s) :
    C.offL ≤ (C.lSlotEmb r b).1 ∧ (C.lSlotEmb r b).1 < C.offP := by
  have hr := r.isLt; have hb := b.isLt
  have hmul : (r.1 + 1) * C.s ≤ C.N * C.s := Nat.mul_le_mul_right C.s hr
  have hstep : r.1 * C.s + C.s ≤ C.N * C.s := by simpa [Nat.succ_mul] using hmul
  rw [C.lSlotEmb_val]; dsimp [offP, lenL]; omega

lemma pSlotEmbLSB_bounds (i : Fin C.n) (u : Fin C.w_v) :
    C.offP ≤ (C.pSlotEmbLSB i u).1 ∧ (C.pSlotEmbLSB i u).1 < C.offArr := by
  have hi := i.isLt; have hu := u.isLt
  have hmul : (i.1 + 1) * C.w_v ≤ C.n * C.w_v := Nat.mul_le_mul_right C.w_v hi
  have hstep : i.1 * C.w_v + C.w_v ≤ C.n * C.w_v := by simpa [Nat.succ_mul] using hmul
  rw [C.pSlotEmbLSB_val]; dsimp [offArr, lenP]; omega

lemma slotSlice_bounds (pos : Fin C.M) (off len : ℕ) (hoff : off + len ≤ C.w_rec)
    (v : Fin len) :
    C.offArr + pos.1 * C.w_rec + off ≤
        (slotSliceEmb C.offArr C.w_rec C.M off len C.total hoff C.offArr_le pos v).1 ∧
      (slotSliceEmb C.offArr C.w_rec C.M off len C.total hoff C.offArr_le pos v).1 <
        C.offArr + pos.1 * C.w_rec + off + len := by
  have hv := v.isLt; rw [slotSliceEmb_val]; omega

lemma slotSlice_in_arr (pos : Fin C.M) (off len : ℕ) (hoff : off + len ≤ C.w_rec)
    (v : Fin len) :
    C.offArr ≤ (slotSliceEmb C.offArr C.w_rec C.M off len C.total hoff C.offArr_le pos v).1 ∧
      (slotSliceEmb C.offArr C.w_rec C.M off len C.total hoff C.offArr_le pos v).1 < C.offTr := by
  have hp := pos.isLt; have hv := v.isLt
  have hmul : (pos.1 + 1) * C.w_rec ≤ C.M * C.w_rec := Nat.mul_le_mul_right C.w_rec hp
  have hstep : pos.1 * C.w_rec + C.w_rec ≤ C.M * C.w_rec := by simpa [Nat.succ_mul] using hmul
  rw [slotSliceEmb_val]; dsimp only [offTr, lenArr]; omega

lemma slotSlice_disj_same_pos (pos : Fin C.M) (off₁ len₁ off₂ len₂ : ℕ)
    (h1 : off₁ + len₁ ≤ C.w_rec) (h2 : off₂ + len₂ ≤ C.w_rec)
    (hdisj : off₁ + len₁ ≤ off₂ ∨ off₂ + len₂ ≤ off₁) :
    let e1 := slotSliceEmb C.offArr C.w_rec C.M off₁ len₁ C.total h1 C.offArr_le pos
    let e2 := slotSliceEmb C.offArr C.w_rec C.M off₂ len₂ C.total h2 C.offArr_le pos
    ∀ i j, e1 i ≠ e2 j :=
  C.emb_disj_of_bounds _ _ _ _ _ _
    (C.slotSlice_bounds pos off₁ len₁ h1) (C.slotSlice_bounds pos off₂ len₂ h2) (by omega)

lemma arr1AllEmb_pair (pos : Fin C.M) (u : Fin C.w_rec1) :
    (C.arr1AllEmb (finProdFinEquiv (pos, u))).1 = C.offArr + pos.1 * C.w_rec + u.1 := by
  change C.offArr + (finProdFinEquiv.symm (finProdFinEquiv (pos, u))).1.1 * C.w_rec +
      (finProdFinEquiv.symm (finProdFinEquiv (pos, u))).2.1 = _
  rw [Equiv.symm_apply_apply]

lemma arr1AllEmb_bounds (u : Fin (C.M * C.w_rec1)) :
    C.offArr ≤ (C.arr1AllEmb u).1 ∧ (C.arr1AllEmb u).1 < C.offTr := by
  rcases finProdFinEquiv.surjective u with ⟨⟨pos, k⟩, rfl⟩
  rw [C.arr1AllEmb_pair pos k]
  have hp := pos.isLt; have hk := k.isLt; have h1 := C.w_rec1_le_w_rec
  have hmul : (pos.1 + 1) * C.w_rec ≤ C.M * C.w_rec := Nat.mul_le_mul_right C.w_rec hp
  have hstep : pos.1 * C.w_rec + C.w_rec ≤ C.M * C.w_rec := by simpa [Nat.succ_mul] using hmul
  dsimp only [offTr, lenArr]; omega

lemma arr2AllEmb_bounds (u : Fin (C.M * C.w_rec)) :
    C.offArr ≤ (C.arr2AllEmb u).1 ∧ (C.arr2AllEmb u).1 < C.offTr := by
  have hu := u.isLt; dsimp only [arr2AllEmb]; rw [segEmb_val]; dsimp only [offTr, lenArr]; omega

lemma trEmb_bounds (u : Fin C.T) :
    C.offTr ≤ (C.trEmb u).1 ∧ (C.trEmb u).1 < C.offScr := by
  have hu := u.isLt; rw [C.trEmb_val]; dsimp only [offScr, lenTr]; omega

lemma scrEmb_bounds (off len : ℕ) (h : off + len ≤ C.lenScr) (u : Fin len) :
    C.offScr + off ≤ (C.scrEmb off len h u).1 ∧ (C.scrEmb off len h u).1 < C.offScr + off + len := by
  have hu := u.isLt; rw [C.scrEmb_val]; omega

lemma scrEmb_full_bounds (u : Fin C.lenScr) :
    C.offScr ≤ (C.scrEmb 0 C.lenScr C.lenScr_full u).1 ∧
      (C.scrEmb 0 C.lenScr C.lenScr_full u).1 < C.offScr + C.lenScr := by
  have h := C.scrEmb_bounds 0 C.lenScr C.lenScr_full u
  omega

lemma scrEmb_disj (off₁ len₁ off₂ len₂ : ℕ) (h1 : off₁ + len₁ ≤ C.lenScr) (h2 : off₂ + len₂ ≤ C.lenScr)
    (hdisj : off₁ + len₁ ≤ off₂ ∨ off₂ + len₂ ≤ off₁) :
    ∀ i j, C.scrEmb off₁ len₁ h1 i ≠ C.scrEmb off₂ len₂ h2 j :=
  C.emb_disj_of_bounds _ _ _ _ _ _
    (C.scrEmb_bounds off₁ len₁ h1) (C.scrEmb_bounds off₂ len₂ h2) (by omega)

lemma hAT_arr1 : ∀ i j, C.arr1AllEmb i ≠ C.trEmb j :=
  C.emb_disj_of_bounds _ _ _ _ _ _ C.arr1AllEmb_bounds C.trEmb_bounds (Or.inl le_rfl)

lemma hAT_arr2 : ∀ i j, C.arr2AllEmb i ≠ C.trEmb j :=
  C.emb_disj_of_bounds _ _ _ _ _ _ C.arr2AllEmb_bounds C.trEmb_bounds (Or.inl le_rfl)

private lemma not_mem_of_disj {a b : ℕ} {ea : Fin a ↪ Fin C.total} {eb : Fin b ↪ Fin C.total}
    (h : ∀ i j, ea i ≠ eb j) (i : Fin a) : ea i ∉ Set.range eb :=
  fun ⟨j, hj⟩ => h i j hj.symm

lemma packStage_update_aLowEmbLSB
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr)
    (i₀ : Fin C.n) (f : Qubits C.w_v) :
    updateOn (C.aLowEmbLSB i₀) (C.packStage A K L P Arr Tr Scr) f =
      C.packStage (Function.update A i₀ f) K L P Arr Tr Scr := by
  let z := updateOn (C.aLowEmbLSB i₀) (C.packStage A K L P Arr Tr Scr) f
  have hA_top : ∀ u : Fin C.total, u.1 < C.offK → u.1 % C.q < C.q - C.w_v → z u = false := by
    intro u hA hj
    have hnot : u ∉ Set.range (C.aLowEmbLSB i₀) := by
      rintro ⟨v, rfl⟩; exact (C.aLowEmbLSB_div_mod i₀ v).2.2.2 hj
    dsimp only [z]; rw [updateOn_apply_not_mem _ _ _ hnot]
    exact C.packStage_A_top_false A K L P Arr Tr Scr u hA hj
  change z = _
  rw [C.eq_packStage_of_bounds z hA_top]
  congr 1
  · funext i u
    by_cases hi : i = i₀
    · subst hi; dsimp only [z]; rw [updateOn_apply_emb, Function.update_self]
    · have hnot : C.aLowEmbLSB i u ∉ Set.range (C.aLowEmbLSB i₀) := by
        rintro ⟨v, hv⟩
        have h1 := (C.aLowEmbLSB_div_mod i u).2.1
        have h2 := (C.aLowEmbLSB_div_mod i₀ v).2.1
        rw [hv] at h2; exact hi (Fin.ext (by omega))
      dsimp only [z]
      rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_aLowEmbLSB, Function.update_of_ne hi]
  · funext u
    have hnot : C.kEmbLSB u ∉ Set.range (C.aLowEmbLSB i₀) := C.not_mem_of_disj
      (C.emb_disj_of_bounds _ _ _ _ _ _ C.kEmbLSB_bounds (C.aLowEmbLSB_bounds i₀) (Or.inr le_rfl)) u
    dsimp only [z, Function.comp_apply]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_kEmbLSB]
  · funext r b
    have hnot : C.lSlotEmb r b ∉ Set.range (C.aLowEmbLSB i₀) := C.not_mem_of_disj
      (C.emb_disj_of_bounds _ _ _ _ _ _ (C.lSlotEmb_bounds r) (C.aLowEmbLSB_bounds i₀)
        (Or.inr (by dsimp [offL]; omega))) b
    dsimp only [z]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_lSlotEmb]
  · funext i u
    have hnot : C.pSlotEmbLSB i u ∉ Set.range (C.aLowEmbLSB i₀) := C.not_mem_of_disj
      (C.emb_disj_of_bounds _ _ _ _ _ _ (C.pSlotEmbLSB_bounds i) (C.aLowEmbLSB_bounds i₀)
        (Or.inr (by dsimp [offP, offL]; omega))) u
    dsimp only [z]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_pSlotEmbLSB]
  · funext pos u
    have hnot : C.arr2AllEmb (finProdFinEquiv (pos, u)) ∉ Set.range (C.aLowEmbLSB i₀) := C.not_mem_of_disj
      (C.emb_disj_of_bounds _ _ _ _ _ _ C.arr2AllEmb_bounds (C.aLowEmbLSB_bounds i₀)
        (Or.inr (by dsimp [offArr, offP, offL]; omega))) _
    dsimp only [z]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_arr2AllEmb]
  · funext u
    have hnot : C.trEmb u ∉ Set.range (C.aLowEmbLSB i₀) := C.not_mem_of_disj
      (C.emb_disj_of_bounds _ _ _ _ _ _ C.trEmb_bounds (C.aLowEmbLSB_bounds i₀)
        (Or.inr (by dsimp [offTr, offArr, offP, offL]; omega))) u
    dsimp only [z, Function.comp_apply]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_trEmb]
  · funext u
    have hnot : C.scrEmb 0 C.lenScr C.lenScr_full u ∉ Set.range (C.aLowEmbLSB i₀) := C.not_mem_of_disj
      (C.emb_disj_of_bounds _ _ _ _ _ _ C.scrEmb_full_bounds (C.aLowEmbLSB_bounds i₀)
        (Or.inr (by dsimp [offScr, offTr, offArr, offP, offL]; omega))) u
    dsimp only [z, Function.comp_apply]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_scrEmb]
    exact congrArg Scr (Fin.ext (by simp))

lemma packStage_update_of_bounds {w : ℕ} (emb : Fin w ↪ Fin C.total)
    (lo hi : ℕ) (hlo : C.offK ≤ lo) (hemb : ∀ v : Fin w, lo ≤ (emb v).1 ∧ (emb v).1 < hi)
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (f : Qubits w) :
    updateOn emb (C.packStage A K L P Arr Tr Scr) f =
      C.packStage A
        (if hi ≤ C.offK ∨ C.offL ≤ lo then K else updateOn emb (C.packStage A K L P Arr Tr Scr) f ∘ C.kEmbLSB)
        (if hi ≤ C.offL ∨ C.offP ≤ lo then L else fun r b => updateOn emb (C.packStage A K L P Arr Tr Scr) f (C.lSlotEmb r b))
        (if hi ≤ C.offP ∨ C.offArr ≤ lo then P else fun i u => updateOn emb (C.packStage A K L P Arr Tr Scr) f (C.pSlotEmbLSB i u))
        (if hi ≤ C.offArr ∨ C.offTr ≤ lo then Arr else fun pos u => updateOn emb (C.packStage A K L P Arr Tr Scr) f (C.arr2AllEmb (finProdFinEquiv (pos, u))))
        (if hi ≤ C.offTr ∨ C.offScr ≤ lo then Tr else updateOn emb (C.packStage A K L P Arr Tr Scr) f ∘ C.trEmb)
        (if hi ≤ C.offScr then Scr else updateOn emb (C.packStage A K L P Arr Tr Scr) f ∘ C.scrEmb 0 C.lenScr C.lenScr_full) := by
  let z := updateOn emb (C.packStage A K L P Arr Tr Scr) f
  have hA_top : ∀ u : Fin C.total, u.1 < C.offK → u.1 % C.q < C.q - C.w_v → z u = false := by
    intro u hA hj
    have hnot : u ∉ Set.range emb := fun ⟨v, hv⟩ => by have := (hemb v).1; omega
    dsimp only [z]; rw [updateOn_apply_not_mem _ _ _ hnot]
    exact C.packStage_A_top_false A K L P Arr Tr Scr u hA hj
  change z = _
  rw [C.eq_packStage_of_bounds z hA_top]
  congr 1
  · funext i u
    have hnot : C.aLowEmbLSB i u ∉ Set.range emb := C.not_mem_of_disj
      (C.emb_disj_of_bounds _ _ _ _ _ _ (C.aLowEmbLSB_bounds i) hemb (Or.inl hlo)) u
    dsimp only [z]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_aLowEmbLSB]
  · split_ifs with h
    · funext u
      have hnot : C.kEmbLSB u ∉ Set.range emb := C.not_mem_of_disj
        (C.emb_disj_of_bounds _ _ _ _ _ _ C.kEmbLSB_bounds hemb (by omega)) u
      dsimp only [z, Function.comp_apply]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_kEmbLSB]
    · rfl
  · split_ifs with h
    · funext r b
      have hnot : C.lSlotEmb r b ∉ Set.range emb := C.not_mem_of_disj
        (C.emb_disj_of_bounds _ _ _ _ _ _ (C.lSlotEmb_bounds r) hemb (by omega)) b
      dsimp only [z]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_lSlotEmb]
    · rfl
  · split_ifs with h
    · funext i u
      have hnot : C.pSlotEmbLSB i u ∉ Set.range emb := C.not_mem_of_disj
        (C.emb_disj_of_bounds _ _ _ _ _ _ (C.pSlotEmbLSB_bounds i) hemb (by omega)) u
      dsimp only [z]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_pSlotEmbLSB]
    · rfl
  · split_ifs with h
    · funext pos u
      have hnot : C.arr2AllEmb (finProdFinEquiv (pos, u)) ∉ Set.range emb := C.not_mem_of_disj
        (C.emb_disj_of_bounds _ _ _ _ _ _ C.arr2AllEmb_bounds hemb (by omega)) _
      dsimp only [z]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_arr2AllEmb]
    · rfl
  · split_ifs with h
    · funext u
      have hnot : C.trEmb u ∉ Set.range emb := C.not_mem_of_disj
        (C.emb_disj_of_bounds _ _ _ _ _ _ C.trEmb_bounds hemb (by omega)) u
      dsimp only [z, Function.comp_apply]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_trEmb]
    · rfl
  · split_ifs with h
    · funext u
      have hnot : C.scrEmb 0 C.lenScr C.lenScr_full u ∉ Set.range emb := C.not_mem_of_disj
        (C.emb_disj_of_bounds _ _ _ _ _ _ C.scrEmb_full_bounds hemb (Or.inr h)) u
      dsimp only [z, Function.comp_apply]; rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_scrEmb]
      exact congrArg Scr (Fin.ext (by simp))
    · rfl

lemma packStage_update_kEmbLSB
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (f : Qubits C.w_v) :
    updateOn C.kEmbLSB (C.packStage A K L P Arr Tr Scr) f =
      C.packStage A f L P Arr Tr Scr := by
  rw [C.packStage_update_of_bounds C.kEmbLSB C.offK C.offL le_rfl C.kEmbLSB_bounds]
  have h1 : ¬ (C.offL ≤ C.offK ∨ C.offL ≤ C.offK) := by dsimp [offL, lenK]; have := C.w_v_pos; omega
  have h2 : C.offL ≤ C.offL ∨ C.offP ≤ C.offK := Or.inl le_rfl
  have h3 : C.offL ≤ C.offP ∨ C.offArr ≤ C.offK := Or.inl (by dsimp [offP, lenL]; omega)
  have h4 : C.offL ≤ C.offArr ∨ C.offTr ≤ C.offK := Or.inl (by dsimp [offArr, offP, lenL, lenP]; omega)
  have h5 : C.offL ≤ C.offTr ∨ C.offScr ≤ C.offK := Or.inl (by dsimp [offTr, offArr, offP, lenArr, lenL, lenP]; omega)
  have h6 : C.offL ≤ C.offScr := by dsimp [offScr, offTr, offArr, offP, lenTr, lenArr, lenL, lenP]; omega
  rw [if_neg h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6]
  congr 1; funext u; simp only [Function.comp_apply, updateOn_apply_emb]

lemma packStage_update_lSlotEmb
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (r₀ : Fin C.N) (f : Qubits C.s) :
    updateOn (C.lSlotEmb r₀) (C.packStage A K L P Arr Tr Scr) f =
      C.packStage A K (Function.update L r₀ f) P Arr Tr Scr := by
  rw [C.packStage_update_of_bounds (C.lSlotEmb r₀) C.offL C.offP (by dsimp [offL]; omega) (C.lSlotEmb_bounds r₀)]
  have h1 : C.offP ≤ C.offK ∨ C.offL ≤ C.offL := Or.inr le_rfl
  have h2 : ¬ (C.offP ≤ C.offL ∨ C.offP ≤ C.offL) := by
    dsimp [offP, lenL]; have := C.hK; have := C.s_pos
    have : 0 < C.N * C.s := Nat.mul_pos (by dsimp [N]; omega) C.s_pos
    omega
  have h3 : C.offP ≤ C.offP ∨ C.offArr ≤ C.offL := Or.inl le_rfl
  have h4 : C.offP ≤ C.offArr ∨ C.offTr ≤ C.offL := Or.inl (by dsimp [offArr, lenP]; omega)
  have h5 : C.offP ≤ C.offTr ∨ C.offScr ≤ C.offL := Or.inl (by dsimp [offTr, offArr, lenArr, lenP]; omega)
  have h6 : C.offP ≤ C.offScr := by dsimp [offScr, offTr, offArr, lenTr, lenArr, lenP]; omega
  rw [if_pos h1, if_neg h2, if_pos h3, if_pos h4, if_pos h5, if_pos h6]
  congr 1; funext r b
  by_cases hr : r = r₀
  · subst hr; rw [updateOn_apply_emb, Function.update_self]
  · have hnot : C.lSlotEmb r b ∉ Set.range (C.lSlotEmb r₀) := by
      rintro ⟨v, hv⟩
      have hb := b.isLt; have hv_lt := v.isLt; have hval := congrArg Fin.val hv
      rw [C.lSlotEmb_val, C.lSlotEmb_val] at hval
      rcases lt_or_gt_of_ne hr with hlt | hlt
      · have hmul : (r.1 + 1) * C.s ≤ r₀.1 * C.s := Nat.mul_le_mul_right C.s hlt
        simp only [Nat.succ_mul] at hmul; omega
      · have hmul : (r₀.1 + 1) * C.s ≤ r.1 * C.s := Nat.mul_le_mul_right C.s hlt
        simp only [Nat.succ_mul] at hmul; omega
    rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_lSlotEmb, Function.update_of_ne hr]

lemma packStage_update_lSlotEmbLSB
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (r₀ : Fin C.N) (f : Qubits C.s) :
    updateOn (C.lSlotEmbLSB r₀) (C.packStage A K L P Arr Tr Scr) f =
      C.packStage A K (Function.update L r₀ (f ∘ Fin.rev)) P Arr Tr Scr := by
  have heq : updateOn (C.lSlotEmbLSB r₀) (C.packStage A K L P Arr Tr Scr) f =
      updateOn (C.lSlotEmb r₀) (C.packStage A K L P Arr Tr Scr) (f ∘ Fin.rev) := by
    funext w
    by_cases hw : w ∈ Set.range (C.lSlotEmb r₀)
    · rcases hw with ⟨b, rfl⟩
      have hb : C.lSlotEmb r₀ b = C.lSlotEmbLSB r₀ b.rev := by rw [lSlotEmbLSB, revEmb_apply]; simp
      conv_lhs => rw [hb, updateOn_apply_emb]
      rw [updateOn_apply_emb]; rfl
    · have hw2 : w ∉ Set.range (C.lSlotEmbLSB r₀) := by rwa [lSlotEmbLSB, range_revEmb]
      rw [updateOn_apply_not_mem _ _ _ hw, updateOn_apply_not_mem _ _ _ hw2]
  rw [heq, C.packStage_update_lSlotEmb]

lemma packStage_update_pSlotEmbLSB
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) (i₀ : Fin C.n) (f : Qubits C.w_v) :
    updateOn (C.pSlotEmbLSB i₀) (C.packStage A K L P Arr Tr Scr) f =
      C.packStage A K L (Function.update P i₀ f) Arr Tr Scr := by
  rw [C.packStage_update_of_bounds (C.pSlotEmbLSB i₀) C.offP C.offArr
    (by dsimp [offP, offL]; omega) (C.pSlotEmbLSB_bounds i₀)]
  have h1 : C.offArr ≤ C.offK ∨ C.offL ≤ C.offP := Or.inr (by dsimp [offP]; omega)
  have h2 : C.offArr ≤ C.offL ∨ C.offP ≤ C.offP := Or.inr le_rfl
  have h3 : ¬ (C.offArr ≤ C.offP ∨ C.offArr ≤ C.offP) := by
    dsimp [offArr, lenP]
    have : 0 < C.n * C.w_v := Nat.mul_pos C.hn C.w_v_pos
    omega
  have h4 : C.offArr ≤ C.offArr ∨ C.offTr ≤ C.offP := Or.inl le_rfl
  have h5 : C.offArr ≤ C.offTr ∨ C.offScr ≤ C.offP := Or.inl (by dsimp [offTr, lenArr]; omega)
  have h6 : C.offArr ≤ C.offScr := by dsimp [offScr, offTr, lenTr, lenArr]; omega
  rw [if_pos h1, if_pos h2, if_neg h3, if_pos h4, if_pos h5, if_pos h6]
  congr 1; funext i u
  by_cases hi : i = i₀
  · subst hi; rw [updateOn_apply_emb, Function.update_self]
  · have hnot : C.pSlotEmbLSB i u ∉ Set.range (C.pSlotEmbLSB i₀) := by
      rintro ⟨v, hv⟩
      have hu := u.isLt; have hv_lt := v.isLt; have hval := congrArg Fin.val hv
      rw [C.pSlotEmbLSB_val, C.pSlotEmbLSB_val] at hval
      rcases lt_or_gt_of_ne hi with hlt | hlt
      · have hmul : (i.1 + 1) * C.w_v ≤ i₀.1 * C.w_v := Nat.mul_le_mul_right C.w_v hlt
        simp only [Nat.succ_mul] at hmul; omega
      · have hmul : (i₀.1 + 1) * C.w_v ≤ i.1 * C.w_v := Nat.mul_le_mul_right C.w_v hlt
        simp only [Nat.succ_mul] at hmul; omega
    rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_pSlotEmbLSB, Function.update_of_ne hi]

lemma packStage_update_scrEmb
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr)
    (off len : ℕ) (h : off + len ≤ C.lenScr) (f : Qubits len) :
    updateOn (C.scrEmb off len h) (C.packStage A K L P Arr Tr Scr) f =
      C.packStage A K L P Arr Tr (updateOn (segEmb off len C.lenScr h) Scr f) := by
  rw [C.packStage_update_of_bounds (C.scrEmb off len h) C.offScr (C.offScr + C.lenScr)
    (by dsimp [offScr, offTr, offArr, offP, offL]; omega)
    (fun v => ⟨by have := (C.scrEmb_bounds off len h v).1; omega,
      by have := (C.scrEmb_bounds off len h v).2; omega⟩)]
  have h1 : C.offScr + C.lenScr ≤ C.offK ∨ C.offL ≤ C.offScr :=
    Or.inr (by dsimp [offScr, offTr, offArr, offP]; omega)
  have h2 : C.offScr + C.lenScr ≤ C.offL ∨ C.offP ≤ C.offScr :=
    Or.inr (by dsimp [offScr, offTr, offArr]; omega)
  have h3 : C.offScr + C.lenScr ≤ C.offP ∨ C.offArr ≤ C.offScr :=
    Or.inr (by dsimp [offScr, offTr]; omega)
  have h4 : C.offScr + C.lenScr ≤ C.offArr ∨ C.offTr ≤ C.offScr :=
    Or.inr (by dsimp [offScr]; omega)
  have h5 : C.offScr + C.lenScr ≤ C.offTr ∨ C.offScr ≤ C.offScr := Or.inr le_rfl
  have h6 : ¬ (C.offScr + C.lenScr ≤ C.offScr) := by dsimp [lenScr]; omega
  rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5, if_neg h6]
  congr 1; funext u
  rw [Function.comp_apply]
  by_cases hu : ∃ v : Fin len, off + v.1 = u.1
  · rcases hu with ⟨v, hv⟩
    have he1 : C.scrEmb 0 C.lenScr C.lenScr_full u = C.scrEmb off len h v := by
      apply Fin.ext; rw [C.scrEmb_val, C.scrEmb_val]; omega
    have he2 : u = segEmb off len C.lenScr h v := Fin.ext (by simp only [segEmb_val]; omega)
    rw [he1, updateOn_apply_emb, he2, updateOn_apply_emb]
  · have hnot1 : C.scrEmb 0 C.lenScr C.lenScr_full u ∉ Set.range (C.scrEmb off len h) := by
      rintro ⟨v, hv⟩; apply hu; have hval := congrArg Fin.val hv
      rw [C.scrEmb_val, C.scrEmb_val] at hval; exact ⟨v, by omega⟩
    have hnot2 : u ∉ Set.range (segEmb off len C.lenScr h) := by
      rintro ⟨v, hv⟩; apply hu; have hval := congrArg Fin.val hv; simp [segEmb_val] at hval; exact ⟨v, by omega⟩
    rw [updateOn_apply_not_mem _ _ _ hnot1, updateOn_apply_not_mem _ _ _ hnot2, C.packStage_scrEmb]
    exact congrArg Scr (Fin.ext (by simp))

lemma packStage_update_slotSliceEmb
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr)
    (pos₀ : Fin C.M) (off len : ℕ) (hoff : off + len ≤ C.w_rec) (f : Qubits len) :
    let subEmb : Fin len ↪ Fin C.w_rec := segEmb off len C.w_rec hoff
    let slotEmb : Fin len ↪ Fin C.total := slotSliceEmb C.offArr C.w_rec C.M off len C.total hoff C.offArr_le pos₀
    updateOn slotEmb (C.packStage A K L P Arr Tr Scr) f =
      C.packStage A K L P (Function.update Arr pos₀ (updateOn subEmb (Arr pos₀) f)) Tr Scr := by
  intro subEmb slotEmb
  rw [C.packStage_update_of_bounds slotEmb C.offArr C.offTr
    (by dsimp [offArr, offP, offL]; omega) (C.slotSlice_in_arr pos₀ off len hoff)]
  have h1 : C.offTr ≤ C.offK ∨ C.offL ≤ C.offArr := Or.inr (by dsimp [offArr, offP]; omega)
  have h2 : C.offTr ≤ C.offL ∨ C.offP ≤ C.offArr := Or.inr (by dsimp [offArr]; omega)
  have h3 : C.offTr ≤ C.offP ∨ C.offArr ≤ C.offArr := Or.inr le_rfl
  have h4 : ¬ (C.offTr ≤ C.offArr ∨ C.offTr ≤ C.offArr) := by
    dsimp [offTr, lenArr]
    have hM : 0 < C.M := by rw [C.M_eq]; exact Nat.two_pow_pos C.d
    have : 0 < C.M * C.w_rec := Nat.mul_pos hM C.w_rec_pos
    omega
  have h5 : C.offTr ≤ C.offTr ∨ C.offScr ≤ C.offArr := Or.inl le_rfl
  have h6 : C.offTr ≤ C.offScr := by dsimp [offScr, lenTr]; omega
  rw [if_pos h1, if_pos h2, if_pos h3, if_neg h4, if_pos h5, if_pos h6]
  congr 1; funext pos u
  by_cases hpos : pos = pos₀
  · subst hpos; rw [Function.update_self]
    by_cases hu : ∃ v : Fin len, off + v.1 = u.1
    · rcases hu with ⟨v, hv⟩
      have he1 : C.arr2AllEmb (finProdFinEquiv (pos, u)) = slotEmb v := by
        apply Fin.ext; rw [C.arr2AllEmb_pair]; dsimp only [slotEmb]; rw [slotSliceEmb_val]; omega
      have he2 : u = subEmb v := Fin.ext (by simp [subEmb]; omega)
      rw [he1, updateOn_apply_emb, he2, updateOn_apply_emb]
    · have hnot1 : C.arr2AllEmb (finProdFinEquiv (pos, u)) ∉ Set.range slotEmb := by
        rintro ⟨v, hv⟩; apply hu
        have hval := congrArg Fin.val hv; rw [C.arr2AllEmb_pair] at hval
        simp only [slotEmb, slotSliceEmb_val] at hval; exact ⟨v, by omega⟩
      have hnot2 : u ∉ Set.range subEmb := by
        rintro ⟨v, hv⟩; apply hu; have hval := congrArg Fin.val hv; simp [subEmb, segEmb_val] at hval; exact ⟨v, by omega⟩
      rw [updateOn_apply_not_mem _ _ _ hnot1, updateOn_apply_not_mem _ _ _ hnot2, C.packStage_arr2AllEmb]
  · rw [Function.update_of_ne hpos]
    have hnot : C.arr2AllEmb (finProdFinEquiv (pos, u)) ∉ Set.range slotEmb := by
      rintro ⟨v, hv⟩
      have hval := congrArg Fin.val hv; rw [C.arr2AllEmb_pair] at hval
      simp only [slotEmb, slotSliceEmb_val] at hval
      have hu := u.isLt; have hv_lt := v.isLt
      rcases lt_or_gt_of_ne hpos with hlt | hlt
      · have hmul : (pos.1 + 1) * C.w_rec ≤ pos₀.1 * C.w_rec := Nat.mul_le_mul_right C.w_rec hlt
        simp only [Nat.succ_mul] at hmul; omega
      · have hmul : (pos₀.1 + 1) * C.w_rec ≤ pos.1 * C.w_rec := Nat.mul_le_mul_right C.w_rec hlt
        simp only [Nat.succ_mul] at hmul; omega
    rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_arr2AllEmb]

lemma packStage_update_slotSliceEmb_rev
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr)
    (pos₀ : Fin C.M) (off len : ℕ) (hoff : off + len ≤ C.w_rec) (f : Qubits len) :
    let subEmb : Fin len ↪ Fin C.w_rec := segEmb off len C.w_rec hoff
    let slotEmb : Fin len ↪ Fin C.total := slotSliceEmb C.offArr C.w_rec C.M off len C.total hoff C.offArr_le pos₀
    updateOn (revEmb slotEmb) (C.packStage A K L P Arr Tr Scr) f =
      C.packStage A K L P (Function.update Arr pos₀ (updateOn subEmb (Arr pos₀) (f ∘ Fin.rev))) Tr Scr := by
  intro subEmb slotEmb
  have heq : updateOn (revEmb slotEmb) (C.packStage A K L P Arr Tr Scr) f =
      updateOn slotEmb (C.packStage A K L P Arr Tr Scr) (f ∘ Fin.rev) := by
    funext w
    by_cases hw : w ∈ Set.range slotEmb
    · rcases hw with ⟨b, rfl⟩
      have hb : slotEmb b = revEmb slotEmb b.rev := by rw [revEmb_apply]; simp
      conv_lhs => rw [hb, updateOn_apply_emb]
      rw [updateOn_apply_emb]; rfl
    · have hw2 : w ∉ Set.range (revEmb slotEmb) := by rwa [range_revEmb]
      rw [updateOn_apply_not_mem _ _ _ hw, updateOn_apply_not_mem _ _ _ hw2]
  rw [heq]
  exact C.packStage_update_slotSliceEmb A K L P Arr Tr Scr pos₀ off len hoff (f ∘ Fin.rev)

lemma packStage_update_arr1_tr
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr)
    (x1' : Fin C.M → Qubits C.w_rec1) (Tr' : Qubits C.T) :
    let embDT := combineEmb54 C.arr1AllEmb C.trEmb C.hAT_arr1
    updateOn embDT (C.packStage A K L P Arr Tr Scr)
        (Fin.append (flatReg C.M C.w_rec1 x1') Tr') =
      C.packStage A K L P
        (fun pos u => if h : u.1 < C.w_rec1 then x1' pos ⟨u.1, h⟩ else Arr pos u)
        Tr' Scr := by
  intro embDT
  have hbounds : ∀ v : Fin (C.M * C.w_rec1 + C.T), C.offArr ≤ (embDT v).1 ∧ (embDT v).1 < C.offScr := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · dsimp only [embDT]; rw [combineEmb54_castAdd]
      have h := C.arr1AllEmb_bounds i; dsimp [offScr, lenTr]; omega
    · dsimp only [embDT]; rw [combineEmb54_natAdd]
      have h := C.trEmb_bounds j; dsimp [offTr] at *; omega
  rw [C.packStage_update_of_bounds embDT C.offArr C.offScr
    (by dsimp [offArr, offP, offL]; omega) hbounds]
  have h1 : C.offScr ≤ C.offK ∨ C.offL ≤ C.offArr := Or.inr (by dsimp [offArr, offP]; omega)
  have h2 : C.offScr ≤ C.offL ∨ C.offP ≤ C.offArr := Or.inr (by dsimp [offArr]; omega)
  have h3 : C.offScr ≤ C.offP ∨ C.offArr ≤ C.offArr := Or.inr le_rfl
  have h4 : ¬ (C.offScr ≤ C.offArr ∨ C.offTr ≤ C.offArr) := by
    have hM : 0 < C.M := by rw [C.M_eq]; exact Nat.two_pow_pos C.d
    have hpos : 0 < C.M * C.w_rec := Nat.mul_pos hM C.w_rec_pos
    dsimp [offScr, offTr, lenTr, lenArr]; omega
  have h5 : ¬ (C.offScr ≤ C.offTr ∨ C.offScr ≤ C.offArr) := by
    have hM : 0 < C.M := by rw [C.M_eq]; exact Nat.two_pow_pos C.d
    have hpos : 0 < C.M * C.w_rec := Nat.mul_pos hM C.w_rec_pos
    have hT := C.T_pos
    dsimp [offScr, offTr, lenTr, lenArr]; omega
  have h6 : C.offScr ≤ C.offScr := le_rfl
  rw [if_pos h1, if_pos h2, if_pos h3, if_neg h4, if_neg h5, if_pos h6]
  congr 1
  · funext pos u
    by_cases hu : u.1 < C.w_rec1
    · rw [dif_pos hu]
      have he : C.arr2AllEmb (finProdFinEquiv (pos, u)) =
          embDT (Fin.castAdd C.T (finProdFinEquiv (pos, ⟨u.1, hu⟩))) := by
        apply Fin.ext; rw [C.arr2AllEmb_pair]; dsimp only [embDT]
        rw [combineEmb54_castAdd, C.arr1AllEmb_pair]
      rw [he, updateOn_apply_emb, Fin.append_left, flatReg_apply']
    · rw [dif_neg hu]
      have hnot : C.arr2AllEmb (finProdFinEquiv (pos, u)) ∉ Set.range embDT := by
        rintro ⟨v, hv⟩
        induction v using Fin.addCases with
        | left iv =>
          dsimp only [embDT] at hv; rw [combineEmb54_castAdd] at hv
          have hval := congrArg Fin.val hv
          rcases finProdFinEquiv.surjective iv with ⟨⟨p', u'⟩, rfl⟩
          rw [C.arr1AllEmb_pair, C.arr2AllEmb_pair] at hval
          have hu' := u'.isLt; have hu_lt := u.isLt; have hle := C.w_rec1_le_w_rec
          rcases lt_or_gt_of_ne (show pos ≠ p' from by rintro rfl; omega) with hlt | hlt
          · have hmul : (pos.1 + 1) * C.w_rec ≤ p'.1 * C.w_rec := Nat.mul_le_mul_right C.w_rec hlt
            simp only [Nat.succ_mul] at hmul; omega
          · have hmul : (p'.1 + 1) * C.w_rec ≤ pos.1 * C.w_rec := Nat.mul_le_mul_right C.w_rec hlt
            simp only [Nat.succ_mul] at hmul; omega
        | right it =>
          dsimp only [embDT] at hv; rw [combineEmb54_natAdd] at hv
          exact C.emb_disj_of_bounds _ _ _ _ _ _ C.arr2AllEmb_bounds C.trEmb_bounds (Or.inl le_rfl)
            (finProdFinEquiv (pos, u)) it hv.symm
      rw [updateOn_apply_not_mem _ _ _ hnot, C.packStage_arr2AllEmb]
  · funext u
    have he : C.trEmb u = embDT (Fin.natAdd (C.M * C.w_rec1) u) := by
      dsimp only [embDT]; rw [combineEmb54_natAdd]
    rw [Function.comp_apply, he, updateOn_apply_emb, Fin.append_right]

lemma packStage_update_arr2_tr
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr)
    (Arr' : Fin C.M → Qubits C.w_rec) (Tr' : Qubits C.T) :
    let embDT := combineEmb54 C.arr2AllEmb C.trEmb C.hAT_arr2
    updateOn embDT (C.packStage A K L P Arr Tr Scr)
        (Fin.append (flatReg C.M C.w_rec Arr') Tr') =
      C.packStage A K L P Arr' Tr' Scr := by
  intro embDT
  have hbounds : ∀ v : Fin (C.M * C.w_rec + C.T), C.offArr ≤ (embDT v).1 ∧ (embDT v).1 < C.offScr := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · dsimp only [embDT]; rw [combineEmb54_castAdd]
      have h := C.arr2AllEmb_bounds i; dsimp [offScr, lenTr]; omega
    · dsimp only [embDT]; rw [combineEmb54_natAdd]
      have h := C.trEmb_bounds j; dsimp [offTr] at *; omega
  rw [C.packStage_update_of_bounds embDT C.offArr C.offScr
    (by dsimp [offArr, offP, offL]; omega) hbounds]
  have h1 : C.offScr ≤ C.offK ∨ C.offL ≤ C.offArr := Or.inr (by dsimp [offArr, offP]; omega)
  have h2 : C.offScr ≤ C.offL ∨ C.offP ≤ C.offArr := Or.inr (by dsimp [offArr]; omega)
  have h3 : C.offScr ≤ C.offP ∨ C.offArr ≤ C.offArr := Or.inr le_rfl
  have h4 : ¬ (C.offScr ≤ C.offArr ∨ C.offTr ≤ C.offArr) := by
    have hM : 0 < C.M := by rw [C.M_eq]; exact Nat.two_pow_pos C.d
    have hpos : 0 < C.M * C.w_rec := Nat.mul_pos hM C.w_rec_pos
    dsimp [offScr, offTr, lenTr, lenArr]; omega
  have h5 : ¬ (C.offScr ≤ C.offTr ∨ C.offScr ≤ C.offArr) := by
    have hM : 0 < C.M := by rw [C.M_eq]; exact Nat.two_pow_pos C.d
    have hpos : 0 < C.M * C.w_rec := Nat.mul_pos hM C.w_rec_pos
    have hT := C.T_pos
    dsimp [offScr, offTr, lenTr, lenArr]; omega
  have h6 : C.offScr ≤ C.offScr := le_rfl
  rw [if_pos h1, if_pos h2, if_pos h3, if_neg h4, if_neg h5, if_pos h6]
  congr 1
  · funext pos u
    have he : C.arr2AllEmb (finProdFinEquiv (pos, u)) = embDT (Fin.castAdd C.T (finProdFinEquiv (pos, u))) := by
      dsimp only [embDT]; rw [combineEmb54_castAdd]
    rw [he, updateOn_apply_emb, Fin.append_left, flatReg_apply']
  · funext u
    have he : C.trEmb u = embDT (Fin.natAdd (C.M * C.w_rec) u) := by
      dsimp only [embDT]; rw [combineEmb54_natAdd]
    rw [Function.comp_apply, he, updateOn_apply_emb, Fin.append_right]

/-! ### Record Constructors and `arr1AllEmb` Evaluation -/

def packRec1 (c : Qubits C.w_v) (a b : Qubits C.w_a) : Qubits C.w_rec1 :=
  Fin.append (Fin.append c a) b

def padRec1 (r : Qubits C.w_rec1) : Qubits C.w_rec :=
  fun u => if h : u.1 < C.w_rec1 then r ⟨u.1, h⟩ else false

def packRec2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) : Qubits C.w_rec :=
  Fin.append (Fin.append (Fin.append b f) ceff) (Fin.append a c)

lemma padRec1_update_arr1_tr
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (x1 x1' : Fin C.M → Qubits C.w_rec1)
    (Tr Tr' : Qubits C.T) (Scr : Qubits C.lenScr) :
    let embDT := combineEmb54 C.arr1AllEmb C.trEmb C.hAT_arr1
    updateOn embDT (C.packStage A K L P (fun pos => C.padRec1 (x1 pos)) Tr Scr)
        (Fin.append (flatReg C.M C.w_rec1 x1') Tr') =
      C.packStage A K L P (fun pos => C.padRec1 (x1' pos)) Tr' Scr := by
  intro embDT
  rw [C.packStage_update_arr1_tr]
  congr 1; funext pos u
  dsimp only [padRec1]
  by_cases hu : u.1 < C.w_rec1 <;> simp [hu]

@[simp] lemma packStage_arr1AllEmb
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (x1 : Fin C.M → Qubits C.w_rec1)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr) :
    C.packStage A K L P (fun pos => C.padRec1 (x1 pos)) Tr Scr ∘ C.arr1AllEmb =
      flatReg C.M C.w_rec1 x1 := by
  funext idx
  rcases finProdFinEquiv.surjective idx with ⟨⟨pos, u⟩, rfl⟩
  have heq : C.arr1AllEmb (finProdFinEquiv (pos, u)) =
      C.arr2AllEmb (finProdFinEquiv (pos, ⟨u.1, lt_of_lt_of_le u.isLt C.w_rec1_le_w_rec⟩)) := by
    apply Fin.ext; rw [C.arr1AllEmb_pair, C.arr2AllEmb_pair]
  simp only [Function.comp_apply, heq, packStage_arr2AllEmb, padRec1, u.isLt, ↓reduceDIte, flatReg_apply']

lemma packRec1_key (c : Qubits C.w_v) (a b : Qubits C.w_a) :
    recKey54 (C.packRec1 c a b) = Fin.append c a := by
  funext i; exact Fin.append_left _ _ i

end OccCtx
end QuantumLTF.Membership.Supplement.StageA


/-! ### Pass 1 (`Forward` & Uncomputation of `P` and `Arr1`) -/

namespace QuantumLTF.Membership.Supplement.StageA

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open Thm49Primitives Thm410Router Cslib.BitonicSort

namespace OccCtx

variable (C : OccCtx)

/-! #### Bit & Combinatorial Helpers for Pass 1 -/

lemma bitsToNatLSB_pad_high_zero {w₁ w₂ : ℕ} (hw : w₁ ≤ w₂) (a : Qubits w₁) :
    bitsToNatLSB (fun u : Fin w₂ => if h : u.1 < w₁ then a ⟨u.1, h⟩ else false) =
      bitsToNatLSB a := by
  dsimp only [bitsToNatLSB]
  have hsub : (∑ u : Fin w₂, if (if h : u.1 < w₁ then a ⟨u.1, h⟩ else false) = true then 2 ^ u.1 else 0) =
      ∑ u ∈ Finset.univ.image (Fin.castLEEmb hw),
        if (if h : u.1 < w₁ then a ⟨u.1, h⟩ else false) = true then 2 ^ u.1 else 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ _)]
    intro u _ hu
    have hnot : ¬ u.1 < w₁ := fun hlt => hu (Finset.mem_image.mpr
      ⟨⟨u.1, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    rw [dif_neg hnot]; simp
  rw [hsub, Finset.sum_image (fun x _ y _ h => (Fin.castLEEmb hw).injective h)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma sum_sub_lt_two_pow_w_v {α : Fin C.n → ℕ} (hα : ∑ i : Fin C.n, α i ≤ C.N) :
    ∀ i : Fin C.n, α i < 2 ^ C.w_v := fun i => by
  have hle : α i ≤ ∑ j : Fin C.n, α j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i)
  have hlt := C.N_add_one_lt_two_pow_w_v
  omega

lemma prefSum_alpha_lt_two_pow {α : Fin C.n → ℕ} (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (i : Fin C.n) : prefSum54 α i < 2 ^ C.w_v := by
  have hle := C.O.prefSum_le_sum α i
  have hlt := C.N_add_one_lt_two_pow_w_v
  omega

lemma prefSum_alpha_last (α : Fin C.n → ℕ) :
    prefSum54 α ⟨C.n - 1, by have := C.hn; omega⟩ = ∑ i : Fin C.n, α i := by
  dsimp only [prefSum54]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := j.isLt
  have hle : j ≤ ⟨C.n - 1, by have := C.hn; omega⟩ := Fin.le_iff_val_le_val.mpr (by dsimp only; omega)
  simp [hle]

lemma prefSum_alpha_succ (α : Fin C.n → ℕ) (k : ℕ) (hk : k + 1 < C.n) :
    prefSum54 α ⟨k + 1, hk⟩ = prefSum54 α ⟨k, by omega⟩ + α ⟨k + 1, hk⟩ := by
  rw [C.O.prefSum_eq_excl_add α ⟨k + 1, hk⟩]
  congr 1
  dsimp only [exclPrefSum54, prefSum54]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hiff : j < (⟨k + 1, hk⟩ : Fin C.n) ↔ j ≤ ⟨k, by omega⟩ := by
    rw [Fin.lt_def, Fin.le_iff_val_le_val]; dsimp only; omega
  simp [hiff]

def extBeta (α : Fin C.n → ℕ) : Fin C.m → ℕ :=
  fun i => if h : i.1 < C.n then α ⟨i.1, h⟩ else C.N - ∑ r : Fin C.n, α r

lemma extBeta_sum {α : Fin C.n → ℕ} (hα : ∑ r : Fin C.n, α r ≤ C.N) :
    ∑ j : Fin C.m, C.extBeta α j = C.N := by
  dsimp only [m]
  rw [Fin.sum_univ_castSucc]
  have h1 : (∑ i : Fin C.n, C.extBeta α i.castSucc) = ∑ i : Fin C.n, α i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [extBeta, i.isLt]
  have h2 : C.extBeta α (Fin.last C.n) = C.N - ∑ r : Fin C.n, α r := by
    simp [extBeta]
  rw [h1, h2]; omega

lemma prefSum_extBeta_lt (α : Fin C.n → ℕ) (i : ℕ) (hi : i < C.n) :
    prefSum54 (C.extBeta α) ⟨i, by dsimp only [m]; omega⟩ = prefSum54 α ⟨i, hi⟩ := by
  have hcast : (⟨i, by dsimp only [m]; omega⟩ : Fin C.m) = Fin.castSucc ⟨i, hi⟩ := Fin.ext rfl
  rw [hcast]
  dsimp only [prefSum54, m]
  rw [Fin.sum_univ_castSucc]
  have hlast : ¬ Fin.last C.n ≤ Fin.castSucc (⟨i, hi⟩ : Fin C.n) := by
    intro h; have hv := Fin.le_iff_val_le_val.mp h; dsimp at hv; omega
  rw [if_neg hlast, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [extBeta, Fin.val_castSucc, j.isLt, ↓reduceDIte, Fin.castSucc_le_castSucc_iff]

lemma prefSum_extBeta_last {α : Fin C.n → ℕ} (hα : ∑ r : Fin C.n, α r ≤ C.N) :
    prefSum54 (C.extBeta α) ⟨C.n, by dsimp only [m]; omega⟩ = C.N := by
  have h := C.O.prefSum_last (C.extBeta α)
  change prefSum54 (C.extBeta α) ⟨C.n, by dsimp only [m]; omega⟩ = ∑ j : Fin (C.n + 1), C.extBeta α j at h
  rw [h]; exact C.extBeta_sum hα

/-! #### Slot Sub-Register Updates for `packRec1` & `packScr1` -/

lemma hoff_c1 : 0 + C.w_v ≤ C.w_rec := by dsimp [w_rec, w_k2, w_p2, w_a, s]; omega
lemma hoff_a1 : C.w_v + C.w_a ≤ C.w_rec := by dsimp [w_rec, w_k2, w_p2, w_a, s]; omega
lemma hoff_b1 : (C.w_v + C.w_a) + C.w_a ≤ C.w_rec := by dsimp [w_rec, w_k2, w_p2, w_a, s]; omega
lemma hoff_b1_low : (C.w_v + C.w_a) + C.s ≤ C.w_rec := by dsimp [w_rec, w_k2, w_p2, w_a, s]; omega

abbrev b1LowEmbLSB (pos : Fin C.M) : Fin C.s ↪ Fin C.total :=
  slotSliceEmb C.offArr C.w_rec C.M (C.w_v + C.w_a) C.s C.total C.hoff_b1_low C.offArr_le pos

lemma padRec1_update_c1 (c c' : Qubits C.w_v) (a b : Qubits C.w_a) :
    updateOn (segEmb 0 C.w_v C.w_rec C.hoff_c1) (C.padRec1 (C.packRec1 c a b)) c' =
      C.padRec1 (C.packRec1 c' a b) := by
  funext u
  by_cases hu : u.1 < C.w_v
  · have he : u = segEmb 0 C.w_v C.w_rec C.hoff_c1 ⟨u.1, hu⟩ := Fin.ext (by simp [segEmb_val])
    rw [he, updateOn_apply_emb]
    have hu1 : (segEmb 0 C.w_v C.w_rec C.hoff_c1 ⟨u.1, hu⟩).1 < C.w_rec1 := by
      simp only [segEmb_val]; dsimp only [w_rec1, w_k1, w_p1]; omega
    dsimp only [padRec1, packRec1]
    rw [dif_pos hu1]
    have h1 : (⟨(segEmb 0 C.w_v C.w_rec C.hoff_c1 ⟨u.1, hu⟩).1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) =
        Fin.castAdd C.w_p1 (Fin.castAdd C.w_a ⟨u.1, hu⟩) := Fin.ext (by simp [segEmb_val])
    rw [h1, Fin.append_left, Fin.append_left]
  · have hnot : u ∉ Set.range (segEmb 0 C.w_v C.w_rec C.hoff_c1) := by
      rintro ⟨v, rfl⟩; exact hu (by simp [segEmb_val, v.isLt])
    rw [updateOn_apply_not_mem _ _ _ hnot]
    dsimp only [padRec1, packRec1]
    by_cases hu1 : u.1 < C.w_rec1
    · rw [dif_pos hu1, dif_pos hu1]
      by_cases hlt1 : u.1 < C.w_k1
      · have ha : (⟨u.1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) = Fin.castAdd C.w_p1 ⟨u.1, hlt1⟩ := rfl
        rw [ha, Fin.append_left, Fin.append_left]
        have h2 : (⟨u.1, hlt1⟩ : Fin (C.w_v + C.w_a)) =
            Fin.natAdd C.w_v ⟨u.1 - C.w_v, by dsimp only [w_k1] at hlt1; omega⟩ :=
          Fin.ext (by simp; omega)
        rw [h2, Fin.append_right, Fin.append_right]
      · have hb : (⟨u.1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) =
            Fin.natAdd C.w_k1 ⟨u.1 - C.w_k1, by dsimp only [w_rec1] at hu1; omega⟩ :=
          Fin.ext (by simp; omega)
        rw [hb, Fin.append_right, Fin.append_right]
    · rw [dif_neg hu1, dif_neg hu1]

lemma padRec1_update_a1 (c : Qubits C.w_v) (a a' b : Qubits C.w_a) :
    updateOn (segEmb C.w_v C.w_a C.w_rec C.hoff_a1) (C.padRec1 (C.packRec1 c a b)) a' =
      C.padRec1 (C.packRec1 c a' b) := by
  funext u
  by_cases hu : C.w_v ≤ u.1 ∧ u.1 < C.w_v + C.w_a
  · have he : u = segEmb C.w_v C.w_a C.w_rec C.hoff_a1 ⟨u.1 - C.w_v, by omega⟩ :=
      Fin.ext (by simp [segEmb_val]; omega)
    rw [he, updateOn_apply_emb]
    have hu1 : (segEmb C.w_v C.w_a C.w_rec C.hoff_a1 ⟨u.1 - C.w_v, by omega⟩).1 < C.w_rec1 := by
      simp only [segEmb_val]; dsimp only [w_rec1, w_k1, w_p1]; omega
    dsimp only [padRec1, packRec1]
    rw [dif_pos hu1]
    have h1 : (⟨(segEmb C.w_v C.w_a C.w_rec C.hoff_a1 ⟨u.1 - C.w_v, by omega⟩).1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) =
        Fin.castAdd C.w_p1 (Fin.natAdd C.w_v ⟨u.1 - C.w_v, by omega⟩) := Fin.ext (by simp [segEmb_val])
    rw [h1, Fin.append_left, Fin.append_right]
  · have hnot : u ∉ Set.range (segEmb C.w_v C.w_a C.w_rec C.hoff_a1) := by
      rintro ⟨v, rfl⟩; exact hu (by simp [segEmb_val, v.isLt])
    rw [updateOn_apply_not_mem _ _ _ hnot]
    dsimp only [padRec1, packRec1]
    by_cases hu1 : u.1 < C.w_rec1
    · rw [dif_pos hu1, dif_pos hu1]
      by_cases hlt1 : u.1 < C.w_k1
      · have hlt_v : u.1 < C.w_v := by dsimp only [w_k1] at hlt1; omega
        have ha : (⟨u.1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) = Fin.castAdd C.w_p1 ⟨u.1, hlt1⟩ := rfl
        rw [ha, Fin.append_left, Fin.append_left]
        have h2 : (⟨u.1, hlt1⟩ : Fin (C.w_v + C.w_a)) = Fin.castAdd C.w_a ⟨u.1, hlt_v⟩ := rfl
        rw [h2, Fin.append_left, Fin.append_left]
      · have hb : (⟨u.1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) =
            Fin.natAdd C.w_k1 ⟨u.1 - C.w_k1, by dsimp only [w_rec1] at hu1; omega⟩ :=
          Fin.ext (by simp; omega)
        rw [hb, Fin.append_right, Fin.append_right]
    · rw [dif_neg hu1, dif_neg hu1]

lemma padRec1_update_b1 (c : Qubits C.w_v) (a b b' : Qubits C.w_a) :
    updateOn (segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1) (C.padRec1 (C.packRec1 c a b)) b' =
      C.padRec1 (C.packRec1 c a b') := by
  funext u
  by_cases hu : C.w_v + C.w_a ≤ u.1 ∧ u.1 < C.w_rec1
  · have he : u = segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1
        ⟨u.1 - (C.w_v + C.w_a), by dsimp only [w_rec1, w_k1, w_p1] at hu; omega⟩ :=
      Fin.ext (by simp [segEmb_val]; omega)
    rw [he, updateOn_apply_emb]
    have hu1 : (segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1
        ⟨u.1 - (C.w_v + C.w_a), by dsimp only [w_rec1, w_k1, w_p1] at hu; omega⟩).1 < C.w_rec1 := by
      simp only [segEmb_val]; dsimp only [w_rec1, w_k1, w_p1] at hu ⊢; omega
    dsimp only [padRec1, packRec1]
    rw [dif_pos hu1]
    have hb : (⟨(segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1 _).1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) =
        Fin.natAdd C.w_k1 ⟨u.1 - (C.w_v + C.w_a), by dsimp only [w_rec1, w_k1, w_p1] at hu ⊢; omega⟩ :=
      Fin.ext (by simp only [segEmb_val, Fin.val_natAdd])
    rw [hb, Fin.append_right]
  · have hnot : u ∉ Set.range (segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1) := by
      rintro ⟨v, rfl⟩; apply hu; refine ⟨by simp [segEmb_val], ?_⟩
      simp only [segEmb_val]; dsimp only [w_rec1, w_k1, w_p1]; have := v.isLt; omega
    rw [updateOn_apply_not_mem _ _ _ hnot]
    dsimp only [padRec1, packRec1]
    by_cases hu1 : u.1 < C.w_rec1
    · rw [dif_pos hu1, dif_pos hu1]
      have hlt1 : u.1 < C.w_k1 := by dsimp only [w_rec1, w_k1, w_p1] at hu1 hu ⊢; omega
      have ha : (⟨u.1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) = Fin.castAdd C.w_p1 ⟨u.1, hlt1⟩ := rfl
      rw [ha, Fin.append_left, Fin.append_left]
    · rw [dif_neg hu1, dif_neg hu1]

lemma padRec1_eval_c1 (c : Qubits C.w_v) (a b : Qubits C.w_a) (u : Fin C.w_v) :
    C.padRec1 (C.packRec1 c a b) (segEmb 0 C.w_v C.w_rec C.hoff_c1 u) = c u := by
  have hu1 : (segEmb 0 C.w_v C.w_rec C.hoff_c1 u).1 < C.w_rec1 := by
    simp only [segEmb_val]; dsimp only [w_rec1, w_k1, w_p1]; have := u.isLt; omega
  dsimp only [padRec1, packRec1]
  rw [dif_pos hu1]
  have h1 : (⟨(segEmb 0 C.w_v C.w_rec C.hoff_c1 u).1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) =
      Fin.castAdd C.w_p1 (Fin.castAdd C.w_a u) := Fin.ext (by simp [segEmb_val])
  rw [h1, Fin.append_left, Fin.append_left]

lemma padRec1_eval_a1 (c : Qubits C.w_v) (a b : Qubits C.w_a) (u : Fin C.w_a) :
    C.padRec1 (C.packRec1 c a b) (segEmb C.w_v C.w_a C.w_rec C.hoff_a1 u) = a u := by
  have hu1 : (segEmb C.w_v C.w_a C.w_rec C.hoff_a1 u).1 < C.w_rec1 := by
    simp only [segEmb_val]; dsimp only [w_rec1, w_k1, w_p1]; have := u.isLt; omega
  dsimp only [padRec1, packRec1]
  rw [dif_pos hu1]
  have h1 : (⟨(segEmb C.w_v C.w_a C.w_rec C.hoff_a1 u).1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) =
      Fin.castAdd C.w_p1 (Fin.natAdd C.w_v u) := Fin.ext (by simp [segEmb_val])
  rw [h1, Fin.append_left, Fin.append_right]

lemma padRec1_eval_b1 (c : Qubits C.w_v) (a b : Qubits C.w_a) (u : Fin C.w_a) :
    C.padRec1 (C.packRec1 c a b) (segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1 u) = b u := by
  have hu1 : (segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1 u).1 < C.w_rec1 := by
    simp only [segEmb_val]; dsimp only [w_rec1, w_k1, w_p1]; have := u.isLt; omega
  dsimp only [padRec1, packRec1]
  rw [dif_pos hu1]
  have h1 : (⟨(segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1 u).1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) =
      Fin.natAdd C.w_k1 u := Fin.ext (by simp only [segEmb_val, Fin.val_natAdd])
  rw [h1, Fin.append_right]

lemma padRec1_eval_b1_low (c : Qubits C.w_v) (a b : Qubits C.w_a) (u : Fin C.s) :
    C.padRec1 (C.packRec1 c a b) (segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low u) =
      b ⟨u.1, by dsimp [w_a]; exact lt_trans u.isLt (Nat.lt_succ_self C.s)⟩ := by
  have he : segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low u =
      segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1 ⟨u.1, by dsimp [w_a]; omega⟩ :=
    Fin.ext (by simp [segEmb_val])
  rw [he]; exact C.padRec1_eval_b1 c a b _

lemma padRec1_update_b1_low (c : Qubits C.w_v) (a b : Qubits C.w_a) (g : Qubits C.s) :
    updateOn (segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low) (C.padRec1 (C.packRec1 c a b)) g =
      C.padRec1 (C.packRec1 c a (fun j : Fin C.w_a => if h : j.1 < C.s then g ⟨j.1, h⟩ else b j)) := by
  funext u
  by_cases hu : C.w_v + C.w_a ≤ u.1 ∧ u.1 < C.w_v + C.w_a + C.s
  · have he : u = segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low ⟨u.1 - (C.w_v + C.w_a), by omega⟩ :=
      Fin.ext (by simp [segEmb_val]; omega)
    rw [he, updateOn_apply_emb]
    have he2 : segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low ⟨u.1 - (C.w_v + C.w_a), by omega⟩ =
        segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1
          ⟨u.1 - (C.w_v + C.w_a), lt_trans (by omega : u.1 - (C.w_v + C.w_a) < C.s) (Nat.lt_succ_self C.s)⟩ :=
      Fin.ext (by simp [segEmb_val])
    rw [he2, C.padRec1_eval_b1]
    simp [show u.1 - (C.w_v + C.w_a) < C.s by omega]
  · have hnot : u ∉ Set.range (segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low) := by
      rintro ⟨v, rfl⟩; exact hu (by simp [segEmb_val, v.isLt])
    rw [updateOn_apply_not_mem _ _ _ hnot]
    by_cases hu1 : u.1 < C.w_rec1
    · by_cases hlt : C.w_v + C.w_a ≤ u.1
      · have hnot2 : ¬ u.1 - (C.w_v + C.w_a) < C.s := by omega
        have he : u = segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1
            ⟨u.1 - (C.w_v + C.w_a), by dsimp only [w_rec1, w_k1, w_p1] at hu1; omega⟩ :=
          Fin.ext (by simp [segEmb_val]; omega)
        conv_lhs => rw [he, C.padRec1_eval_b1]
        conv_rhs => rw [he, C.padRec1_eval_b1]
        simp [hnot2]
      · dsimp only [padRec1, packRec1]
        rw [dif_pos hu1, dif_pos hu1]
        have hlt1 : u.1 < C.w_k1 := by dsimp only [w_k1]; omega
        have ha : (⟨u.1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) = Fin.castAdd C.w_p1 ⟨u.1, hlt1⟩ := rfl
        rw [ha, Fin.append_left, Fin.append_left]
    · dsimp only [padRec1]; rw [dif_neg hu1, dif_neg hu1]

/-- Scratch packing for Pass 1 & Pass 2 (`flag`, `T_reg`, `U_reg`). -/
def packScr1 (flag : Bool) (T U : Qubits C.w_pos) : Qubits C.lenScr := fun u =>
  if h0 : u.1 = 0 then flag
  else if hT : u.1 < 1 + C.w_pos then T ⟨u.1 - 1, by omega⟩
  else if hU : u.1 < 1 + 2 * C.w_pos then U ⟨u.1 - (1 + C.w_pos), by omega⟩
  else false

lemma w_pos_pos : 0 < C.w_pos := by dsimp [w_pos]; omega

lemma packScr1_zero : C.packScr1 false (fun _ => false) (fun _ => false) = fun _ => false := by
  funext u; dsimp only [packScr1]; split_ifs <;> rfl

lemma offScr_flag : 0 + 1 ≤ C.lenScr := by dsimp [lenScr]; omega
lemma offScr_T : 1 + C.w_pos ≤ C.lenScr := by dsimp [lenScr]; omega
lemma offScr_T_wa : 1 + C.w_a ≤ C.lenScr := by have := C.w_a_lt_w_pos; dsimp [lenScr]; omega
lemma offScr_T_wv : 1 + C.w_v ≤ C.lenScr := by have := C.w_v_lt_w_pos; dsimp [lenScr]; omega
lemma offScr_U : 1 + C.w_pos + C.w_pos ≤ C.lenScr := by dsimp [lenScr]; omega
lemma offScr_U_wv : 1 + C.w_pos + C.w_v ≤ C.lenScr := by have := C.w_v_lt_w_pos; dsimp [lenScr]; omega
lemma offScr_U_wa : 1 + C.w_pos + C.w_a ≤ C.lenScr := by have := C.w_a_lt_w_pos; dsimp [lenScr]; omega
lemma offScr_anc_wa : 1 + 2 * C.w_pos + C.w_a ≤ C.lenScr := by dsimp [lenScr]; omega
lemma offScr_anc1 : 1 + 2 * C.w_pos + 1 ≤ C.lenScr := by dsimp [lenScr]; omega
lemma offScr_sort1 : 0 + C.w_k1 ≤ C.lenScr := by
  have := C.w_v_lt_w_pos; have := C.w_a_lt_w_pos; dsimp [lenScr, w_k1, w_k2]; omega
lemma offScr_sort2 : 0 + C.w_k2 ≤ C.lenScr := by dsimp [lenScr]; omega
lemma offScr_sym : 0 + (C.s - 1) ≤ C.lenScr := by dsimp [lenScr]; omega

@[simp] lemma packScr1_flag (flag : Bool) (T U : Qubits C.w_pos) (j : Fin 1) :
    C.packScr1 flag T U (segEmb 0 1 C.lenScr C.offScr_flag j) = flag := by
  have hj0 : j = 0 := Subsingleton.elim j 0; subst hj0
  dsimp only [packScr1]
  rw [dif_pos (by simp [segEmb_val])]

@[simp] lemma packScr1_T (flag : Bool) (T U : Qubits C.w_pos) (j : Fin C.w_pos) :
    C.packScr1 flag T U (segEmb 1 C.w_pos C.lenScr C.offScr_T j) = T j := by
  dsimp only [packScr1]
  rw [dif_neg (by simp [segEmb_val]), dif_pos (by simp [segEmb_val])]
  exact congrArg T (Fin.ext (by simp [segEmb_val]))

@[simp] lemma packScr1_U (flag : Bool) (T U : Qubits C.w_pos) (j : Fin C.w_pos) :
    C.packScr1 flag T U (segEmb (1 + C.w_pos) C.w_pos C.lenScr C.offScr_U j) = U j := by
  dsimp only [packScr1]
  rw [dif_neg (by simp [segEmb_val]), dif_neg (by simp [segEmb_val]),
    dif_pos (by simp [segEmb_val]; have := j.isLt; omega)]
  exact congrArg U (Fin.ext (by simp [segEmb_val]))

@[simp] lemma packScr1_anc_wa (flag : Bool) (T U : Qubits C.w_pos) (j : Fin C.w_a) :
    C.packScr1 flag T U (segEmb (1 + 2 * C.w_pos) C.w_a C.lenScr C.offScr_anc_wa j) = false := by
  dsimp only [packScr1]
  rw [dif_neg (by simp [segEmb_val]), dif_neg (by simp [segEmb_val]; omega),
    dif_neg (by simp [segEmb_val])]

@[simp] lemma packScr1_anc1 (flag : Bool) (T U : Qubits C.w_pos) (j : Fin 1) :
    C.packScr1 flag T U (segEmb (1 + 2 * C.w_pos) 1 C.lenScr C.offScr_anc1 j) = false := by
  dsimp only [packScr1]
  rw [dif_neg (by simp [segEmb_val]), dif_neg (by simp [segEmb_val]; omega),
    dif_neg (by simp [segEmb_val])]

lemma packScr1_update_flag (flag : Bool) (T U : Qubits C.w_pos) (f : Qubits 1) :
    updateOn (segEmb 0 1 C.lenScr C.offScr_flag) (C.packScr1 flag T U) f =
      C.packScr1 (f 0) T U := by
  funext u
  by_cases hu : u.1 = 0
  · have he : u = segEmb 0 1 C.lenScr C.offScr_flag 0 := Fin.ext (by simp [segEmb_val, hu])
    rw [he, updateOn_apply_emb]; dsimp only [packScr1]; rw [dif_pos (by simp [segEmb_val])]
  · have hnot : u ∉ Set.range (segEmb 0 1 C.lenScr C.offScr_flag) := by
      rintro ⟨v, rfl⟩; simp [segEmb_val, Subsingleton.elim v 0] at hu
    rw [updateOn_apply_not_mem _ _ _ hnot]
    dsimp only [packScr1]; rw [dif_neg hu, dif_neg hu]

lemma packScr1_update_T (flag : Bool) (T U T' : Qubits C.w_pos) :
    updateOn (segEmb 1 C.w_pos C.lenScr C.offScr_T) (C.packScr1 flag T U) T' =
      C.packScr1 flag T' U := by
  funext u
  by_cases hu : 1 ≤ u.1 ∧ u.1 < 1 + C.w_pos
  · have he : u = segEmb 1 C.w_pos C.lenScr C.offScr_T ⟨u.1 - 1, by omega⟩ :=
      Fin.ext (by simp [segEmb_val]; omega)
    rw [he, updateOn_apply_emb]
    dsimp only [packScr1]; rw [dif_neg (by simp [segEmb_val]), dif_pos (by simp [segEmb_val]; omega)]
    exact congrArg T' (Fin.ext (by simp [segEmb_val]))
  · have hnot : u ∉ Set.range (segEmb 1 C.w_pos C.lenScr C.offScr_T) := by
      rintro ⟨v, rfl⟩; exact hu (by simp [segEmb_val, v.isLt])
    rw [updateOn_apply_not_mem _ _ _ hnot]
    dsimp only [packScr1]
    split_ifs with h0 hT
    · rfl
    · exfalso; omega
    · rfl
    · rfl

lemma packScr1_update_U_wv (flag : Bool) (T U : Qubits C.w_pos) (f : Qubits C.w_v) :
    updateOn (segEmb (1 + C.w_pos) C.w_v C.lenScr C.offScr_U_wv) (C.packScr1 flag T U) f =
      C.packScr1 flag T (fun j : Fin C.w_pos => if h : j.1 < C.w_v then f ⟨j.1, h⟩ else U j) := by
  funext u
  by_cases hu : 1 + C.w_pos ≤ u.1 ∧ u.1 < 1 + C.w_pos + C.w_v
  · have he : u = segEmb (1 + C.w_pos) C.w_v C.lenScr C.offScr_U_wv ⟨u.1 - (1 + C.w_pos), by omega⟩ :=
      Fin.ext (by simp [segEmb_val]; omega)
    rw [he, updateOn_apply_emb]
    have hU : (segEmb (1 + C.w_pos) C.w_v C.lenScr C.offScr_U_wv ⟨u.1 - (1 + C.w_pos), by omega⟩).1 < 1 + 2 * C.w_pos := by
      simp only [segEmb_val]; have := C.w_v_lt_w_pos; omega
    dsimp only [packScr1]
    rw [dif_neg (by simp [segEmb_val]), dif_neg (by simp [segEmb_val]), dif_pos hU]
    simp [segEmb_val, show u.1 - (1 + C.w_pos) < C.w_v by omega]
  · have hnot : u ∉ Set.range (segEmb (1 + C.w_pos) C.w_v C.lenScr C.offScr_U_wv) := by
      rintro ⟨v, rfl⟩; exact hu (by simp [segEmb_val, v.isLt])
    rw [updateOn_apply_not_mem _ _ _ hnot]
    dsimp only [packScr1]
    by_cases h0 : u.1 = 0
    · rw [dif_pos h0, dif_pos h0]
    · rw [dif_neg h0, dif_neg h0]
      by_cases hT : u.1 < 1 + C.w_pos
      · rw [dif_pos hT, dif_pos hT]
      · rw [dif_neg hT, dif_neg hT]
        by_cases hU : u.1 < 1 + 2 * C.w_pos
        · rw [dif_pos hU, dif_pos hU, dif_neg (by omega)]
        · rw [dif_neg hU, dif_neg hU]

lemma packScr1_update_U_wa (flag : Bool) (T U : Qubits C.w_pos) (f : Qubits C.w_a) :
    updateOn (segEmb (1 + C.w_pos) C.w_a C.lenScr C.offScr_U_wa) (C.packScr1 flag T U) f =
      C.packScr1 flag T (fun j : Fin C.w_pos => if h : j.1 < C.w_a then f ⟨j.1, h⟩ else U j) := by
  funext u
  by_cases hu : 1 + C.w_pos ≤ u.1 ∧ u.1 < 1 + C.w_pos + C.w_a
  · have he : u = segEmb (1 + C.w_pos) C.w_a C.lenScr C.offScr_U_wa ⟨u.1 - (1 + C.w_pos), by omega⟩ :=
      Fin.ext (by simp [segEmb_val]; omega)
    rw [he, updateOn_apply_emb]
    have hU : (segEmb (1 + C.w_pos) C.w_a C.lenScr C.offScr_U_wa ⟨u.1 - (1 + C.w_pos), by omega⟩).1 < 1 + 2 * C.w_pos := by
      simp only [segEmb_val]; have := C.w_a_lt_w_pos; omega
    dsimp only [packScr1]
    rw [dif_neg (by simp [segEmb_val]), dif_neg (by simp [segEmb_val]), dif_pos hU]
    simp [segEmb_val, show u.1 - (1 + C.w_pos) < C.w_a by omega]
  · have hnot : u ∉ Set.range (segEmb (1 + C.w_pos) C.w_a C.lenScr C.offScr_U_wa) := by
      rintro ⟨v, rfl⟩; exact hu (by simp [segEmb_val, v.isLt])
    rw [updateOn_apply_not_mem _ _ _ hnot]
    dsimp only [packScr1]
    by_cases h0 : u.1 = 0
    · rw [dif_pos h0, dif_pos h0]
    · rw [dif_neg h0, dif_neg h0]
      by_cases hT : u.1 < 1 + C.w_pos
      · rw [dif_pos hT, dif_pos hT]
      · rw [dif_neg hT, dif_neg hT]
        by_cases hU : u.1 < 1 + 2 * C.w_pos
        · rw [dif_pos hU, dif_pos hU, dif_neg (by omega)]
        · rw [dif_neg hU, dif_neg hU]

/-! #### 1.1 Prefix Sum Circuit `prefixPC` -/

lemma hdisj_aLow_pSlot (i j : Fin C.n) : ∀ a b, C.aLowEmbLSB i a ≠ C.pSlotEmbLSB j b :=
  C.emb_disj_of_bounds _ _ 0 C.offK C.offP C.offArr
    (fun a => ⟨Nat.zero_le _, (C.aLowEmbLSB_div_mod i a).1⟩)
    (fun b => by
      have hj := j.isLt; have hb := b.isLt
      have hmul : (j.1 + 1) * C.w_v ≤ C.n * C.w_v := Nat.mul_le_mul_right C.w_v hj
      have hstep : j.1 * C.w_v + C.w_v ≤ C.n * C.w_v := by simpa [Nat.succ_mul] using hmul
      rw [C.pSlotEmbLSB_val]; dsimp [offArr, lenP]; omega)
    (Or.inl (by dsimp [offP, offL, lenL, lenK]; omega))

lemma hdisj_pSlot_diff {i j : Fin C.n} (hne : i ≠ j) :
    ∀ a b, C.pSlotEmbLSB i a ≠ C.pSlotEmbLSB j b := fun a b heq => by
  have ha := a.isLt; have hb := b.isLt; have hv := congrArg Fin.val heq
  rw [C.pSlotEmbLSB_val, C.pSlotEmbLSB_val] at hv
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hmul : (i.1 + 1) * C.w_v ≤ j.1 * C.w_v := Nat.mul_le_mul_right C.w_v hlt
    simp only [Nat.succ_mul] at hmul; omega
  · have hmul : (j.1 + 1) * C.w_v ≤ i.1 * C.w_v := Nat.mul_le_mul_right C.w_v hlt
    simp only [Nat.succ_mul] at hmul; omega

lemma hdisj_aLow_scr (i : Fin C.n) (off len : ℕ) (h : off + len ≤ C.lenScr) :
    ∀ a b, C.aLowEmbLSB i a ≠ C.scrEmb off len h b :=
  C.emb_disj_of_bounds _ _ 0 C.offK (C.offScr + off) (C.offScr + off + len)
    (fun a => ⟨Nat.zero_le _, (C.aLowEmbLSB_div_mod i a).1⟩)
    (C.scrEmb_bounds off len h)
    (Or.inl (by dsimp [offScr, offTr, offArr, offP, offL, lenTr, lenArr, lenP, lenL, lenK]; omega))

lemma hdisj_pSlot_scr (i : Fin C.n) (off len : ℕ) (h : off + len ≤ C.lenScr) :
    ∀ a b, C.pSlotEmbLSB i a ≠ C.scrEmb off len h b :=
  C.emb_disj_of_bounds _ _ C.offP C.offArr (C.offScr + off) (C.offScr + off + len)
    (fun a => by
      have hi := i.isLt; have ha := a.isLt
      have hmul : (i.1 + 1) * C.w_v ≤ C.n * C.w_v := Nat.mul_le_mul_right C.w_v hi
      have hstep : i.1 * C.w_v + C.w_v ≤ C.n * C.w_v := by simpa [Nat.succ_mul] using hmul
      rw [C.pSlotEmbLSB_val]; dsimp [offArr, lenP]; omega)
    (C.scrEmb_bounds off len h)
    (Or.inl (by dsimp [offScr, offTr, lenTr, lenArr]; omega))

lemma offScr_one : 0 + 1 ≤ C.lenScr := by dsimp [lenScr]; omega

noncomputable def prefixStepC (i : Fin C.n) : LayeredCircuit C.total :=
  if h0 : i.1 = 0 then
    C.copyRegC C.w_v (C.aLowEmbLSB i) (C.pSlotEmbLSB i) (C.hdisj_aLow_pSlot i i)
  else
    let prev : Fin C.n := ⟨i.1 - 1, by omega⟩
    (C.copyRegC C.w_v (C.pSlotEmbLSB prev) (C.pSlotEmbLSB i)
      (C.hdisj_pSlot_diff (Fin.ne_of_val_ne (by dsimp [prev]; omega)))).seq
      (C.addInPlaceC C.w_v (C.aLowEmbLSB i) (C.pSlotEmbLSB i) (C.scrEmb 0 1 C.offScr_one)
        (C.hdisj_aLow_pSlot i i) (C.hdisj_aLow_scr i 0 1 C.offScr_one)
        (C.hdisj_pSlot_scr i 0 1 C.offScr_one))

lemma prefixStepC_size (i : Fin C.n) : (C.prefixStepC i).size ≤ 15 * C.w_v := by
  dsimp only [prefixStepC]
  split_ifs
  · rw [C.copyRegC_size]; omega
  · rw [LayeredCircuit.seq_size, C.copyRegC_size, C.addInPlaceC_size]; omega

noncomputable def prefixPC : LayeredCircuit C.total :=
  LayeredCircuit.seqList (List.ofFn C.prefixStepC)

lemma prefixPC_size : C.prefixPC.size ≤ C.n * (15 * C.w_v) :=
  seqList_ofFn_size_le C.prefixStepC (15 * C.w_v) C.prefixStepC_size

lemma act_prefixPC (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (Arr : Fin C.M → Qubits C.w_rec) (Tr : Qubits C.T) :
    let A_bits := fun i : Fin C.n => natToBitsLSB C.w_v (α i)
    let P_bits := fun i : Fin C.n => natToBitsLSB C.w_v (prefSum54 α i)
    act C.prefixPC.unitary (ket (C.packState A_bits K L (fun _ _ => false) Arr Tr)) =
      ket (C.packState A_bits K L P_bits Arr Tr) := by
  intro A_bits P_bits
  let zAt : (t : ℕ) → t ≤ C.n → Qubits C.total := fun t _ =>
    C.packState A_bits K L (fun j => if j.1 < t then P_bits j else fun _ => false) Arr Tr
  have hrun := act_seqList_fin_ket C.prefixStepC zAt fun t ht => by
    let cur : Fin C.n := ⟨t, ht⟩
    have hcur_eq : (if cur.1 < t then P_bits cur else fun _ => false) = fun _ => false :=
      if_neg (by dsimp [cur]; omega)
    dsimp only [prefixStepC]
    by_cases ht0 : t = 0
    · have h0' : cur.1 = 0 := ht0
      rw [dif_pos h0', C.act_copyRegC, C.packStage_update_pSlotEmbLSB]
      congr 2
      · funext j
        by_cases hj : j = cur
        · subst hj
          have hpref : prefSum54 α cur = α cur := by
            dsimp only [prefSum54]
            rw [Finset.sum_eq_single cur]
            · simp
            · intro j _ hj'
              rw [if_neg]; intro hle
              exact hj' (Fin.ext (by have := Fin.le_iff_val_le_val.mp hle; dsimp [cur] at *; omega))
            · intro h; exact absurd (Finset.mem_univ cur) h
          rw [Function.update_self, if_pos (by dsimp [cur]; omega)]
          funext u
          simp only [zAt, packState, packStage_pSlotEmbLSB, packStage_aLowEmbLSB, A_bits, P_bits, hpref]
          rw [if_neg (by omega), Bool.false_xor]
        · rw [Function.update_of_ne hj]
          have hlt_iff : j.1 < t ↔ j.1 < t + 1 := by
            have := Fin.val_ne_of_ne hj; dsimp [cur] at this; omega
          simp [hlt_iff]
    · have h0' : cur.1 ≠ 0 := ht0
      rw [dif_neg h0', LayeredCircuit.seq_unitary, act_mul, C.act_copyRegC]
      let prev : Fin C.n := ⟨cur.1 - 1, by omega⟩
      have hprev_lt : prev.1 < t := by dsimp [prev, cur]; omega
      have hmid_val : (fun u => xor ((zAt t (le_of_lt ht)) (C.pSlotEmbLSB cur u))
          ((zAt t (le_of_lt ht)) (C.pSlotEmbLSB prev u))) = P_bits prev := by
        funext u
        simp only [zAt, packState, packStage_pSlotEmbLSB, hprev_lt, ↓reduceIte]
        rw [if_neg (by dsimp [cur]; omega), Bool.false_xor]
      rw [hmid_val, C.packStage_update_pSlotEmbLSB]
      rw [C.act_addInPlaceC _ _ _ _ _ _ _ _ (fun _ => by simp)]
      rw [C.packStage_update_pSlotEmbLSB, Function.update_idem]
      congr 2
      · funext j
        by_cases hj : j = cur
        · subst hj
          rw [Function.update_self, if_pos (by dsimp [cur]; omega)]
          have hA_eq : (C.packStage A_bits K L
              (Function.update (fun j => if j.1 < t then P_bits j else fun _ => false) cur (P_bits prev))
              Arr Tr (fun _ => false)) ∘ C.aLowEmbLSB cur = A_bits cur := by
            funext u; simp only [Function.comp_apply, C.packStage_aLowEmbLSB]
          have hP_eq : (C.packStage A_bits K L
              (Function.update (fun j => if j.1 < t then P_bits j else fun _ => false) cur (P_bits prev))
              Arr Tr (fun _ => false)) ∘ C.pSlotEmbLSB cur = P_bits prev := by
            funext u; simp only [Function.comp_apply, C.packStage_pSlotEmbLSB, Function.update_self]
          rw [hA_eq, hP_eq]
          have hα_lt := C.sum_sub_lt_two_pow_w_v hα cur
          have hp_lt := C.prefSum_alpha_lt_two_pow hα prev
          rw [bitsToNatLSB_natToBitsLSB hα_lt, bitsToNatLSB_natToBitsLSB hp_lt]
          have hsucc : prefSum54 α cur = prefSum54 α prev + α cur := by
            have hcur_eq2 : cur = ⟨(t - 1) + 1, by omega⟩ := Fin.ext (by dsimp [cur]; omega)
            have hprev_eq2 : prev = ⟨t - 1, by omega⟩ := rfl
            rw [hcur_eq2, hprev_eq2, C.prefSum_alpha_succ α (t - 1) (by omega)]
          rw [add_comm (α cur), ← hsucc]
        · rw [Function.update_of_ne hj]
          have hlt_iff : j.1 < t ↔ j.1 < t + 1 := by
            have := Fin.val_ne_of_ne hj; dsimp [cur] at this; omega
          simp [hlt_iff]
  have hz0 : zAt 0 (Nat.zero_le C.n) = C.packState A_bits K L (fun _ _ => false) Arr Tr := by
    dsimp only [zAt]; rfl
  have hzn : zAt C.n le_rfl = C.packState A_bits K L P_bits Arr Tr := by
    dsimp only [zAt]; congr 1; funext j; simp [j.isLt]
  rw [hz0, hzn] at hrun
  exact hrun

/-! #### 1.2 Initialize Pass-1 Array `initArr1C` -/

lemma hdisj_pSlot_c1 (i : Fin C.n) (pos : Fin C.M) :
    ∀ a b, C.pSlotEmbLSB i a ≠ C.c1EmbLSB pos b :=
  C.emb_disj_of_bounds _ _ C.offP C.offArr C.offArr C.offTr
    (fun a => by
      have hi := i.isLt; have ha := a.isLt
      have hmul : (i.1 + 1) * C.w_v ≤ C.n * C.w_v := Nat.mul_le_mul_right C.w_v hi
      have hstep : i.1 * C.w_v + C.w_v ≤ C.n * C.w_v := by simpa [Nat.succ_mul] using hmul
      rw [C.pSlotEmbLSB_val]; dsimp [offArr, lenP]; omega)
    (fun b => by
      rw [c1EmbLSB, revEmb_apply, c1EmbMSB]
      exact C.slotSlice_in_arr pos 0 C.w_v C.hoff_c1 b.rev)
    (Or.inl le_rfl)

noncomputable def initArr1StepC (pos : Fin C.M) : LayeredCircuit C.total :=
  if h1 : pos.1 < C.n then
    (C.setConstC C.w_a pos.1 (C.a1EmbLSB pos)).seq
      (C.copyRegC C.w_v (C.pSlotEmbLSB ⟨pos.1, h1⟩) (C.c1EmbLSB pos) (C.hdisj_pSlot_c1 ⟨pos.1, h1⟩ pos))
  else if _h2 : pos.1 = C.n then
    (C.setConstC C.w_a C.n (C.a1EmbLSB pos)).seq
      (C.setConstC C.w_v C.N (C.c1EmbLSB pos))
  else if _h3 : pos.1 < C.m + C.N then
    (C.setConstC C.w_a C.m (C.a1EmbLSB pos)).seq
      (C.setConstC C.w_v (pos.1 - C.m) (C.c1EmbLSB pos))
  else
    (C.setConstC C.w_a C.m (C.a1EmbLSB pos)).seq
      (C.setConstC C.w_v (C.N + 1) (C.c1EmbLSB pos))

lemma initArr1StepC_size (pos : Fin C.M) : (C.initArr1StepC pos).size ≤ C.w_a + C.w_v := by
  dsimp only [initArr1StepC]
  split_ifs
  · rw [LayeredCircuit.seq_size, C.copyRegC_size]
    exact Nat.add_le_add (C.setConstC_size _ _ _) le_rfl
  all_goals
    rw [LayeredCircuit.seq_size]
    exact Nat.add_le_add (C.setConstC_size _ _ _) (C.setConstC_size _ _ _)

noncomputable def initArr1C : LayeredCircuit C.total :=
  LayeredCircuit.seqList (List.ofFn C.initArr1StepC)

lemma initArr1C_size : C.initArr1C.size ≤ C.M * (C.w_a + C.w_v) :=
  seqList_ofFn_size_le C.initArr1StepC (C.w_a + C.w_v) C.initArr1StepC_size

def liftW2 (β : Fin C.m → ℕ) (pos : Fin C.M) : Sec5Rec54 :=
  if h : pos.1 < C.m + C.N then
    (wtilde2_54 β C.N)[pos.1]'(by rw [C.O.wtilde2_length]; exact h)
  else (C.m, 0, C.N + 1)

def encodeRec1 (t : Sec5Rec54) : Qubits C.w_rec1 :=
  C.packRec1 (natToBits C.w_v t.2.2) (natToBits C.w_a t.1) (fun _ => false)

def w2RecAt (β : Fin C.m → ℕ) (pos : Fin C.M) : Qubits C.w_rec1 :=
  C.encodeRec1 (C.liftW2 β pos)

lemma set_a1_c1_on_zero_slot (a_val c_val : ℕ) (_ha : a_val < 2 ^ C.w_a) (_hc : c_val < 2 ^ C.w_v) :
    let zeroSlot : Qubits C.w_rec := fun _ => false
    let r1 := updateOn (segEmb C.w_v C.w_a C.w_rec C.hoff_a1) zeroSlot (natToBits C.w_a a_val)
    updateOn (segEmb 0 C.w_v C.w_rec C.hoff_c1) r1 (natToBits C.w_v c_val) =
      C.padRec1 (C.packRec1 (natToBits C.w_v c_val) (natToBits C.w_a a_val) (fun _ => false)) := by
  intro zeroSlot r1
  have h0 : zeroSlot = C.padRec1 (C.packRec1 (fun _ => false) (fun _ => false) (fun _ => false)) := by
    funext u; dsimp only [zeroSlot, padRec1, packRec1]
    by_cases hu1 : u.1 < C.w_rec1
    · rw [dif_pos hu1]
      exact Eq.symm (Fin.addCases (fun ik => Fin.addCases (fun _ => by simp) (fun _ => by simp) ik) (fun _ => by simp)
        (⟨u.1, hu1⟩ : Fin (C.w_k1 + C.w_p1)))
    · rw [dif_neg hu1]
  rw [show r1 = updateOn (segEmb C.w_v C.w_a C.w_rec C.hoff_a1)
    (C.padRec1 (C.packRec1 (fun _ => false) (fun _ => false) (fun _ => false))) (natToBits C.w_a a_val) from by rw [← h0]]
  rw [C.padRec1_update_a1, C.padRec1_update_c1]

lemma wtilde2_elem_spec (β : Fin C.m → ℕ) (pos : ℕ) (hpos : pos < C.m + C.N) :
    (wtilde2_54 β C.N)[pos]'(by rw [C.O.wtilde2_length]; exact hpos) =
      if h1 : pos < C.n then (pos, 0, prefSum54 β ⟨pos, by dsimp [m]; omega⟩)
      else if h2 : pos = C.n then (C.n, 0, prefSum54 β ⟨C.n, by dsimp [m]; omega⟩)
      else (C.m, 0, pos - C.m) := by
  dsimp only [wtilde2_54]
  change ((List.map (fun i : Fin C.m => (i.1, 0, prefSum54 β i)) (List.finRange C.m) ++
      List.map (fun j : Fin C.N => (C.m, 0, j.1)) (List.finRange C.N))[pos]'(by simp; exact hpos)) = _
  by_cases hm : pos < C.m
  · rw [List.getElem_append_left (by simp only [List.length_map, List.length_finRange]; exact hm)]
    simp only [List.getElem_map, List.getElem_finRange]
    by_cases h1 : pos < C.n
    · simp [h1]
    · have h2 : pos = C.n := by dsimp only [m] at hm; omega
      simp [h2]
  · rw [List.getElem_append_right (by simp only [List.length_map, List.length_finRange]; omega)]
    simp only [List.length_map, List.length_finRange, List.getElem_map, List.getElem_finRange]
    simp [show ¬ pos < C.n by dsimp only [m] at hm; omega, show pos ≠ C.n by dsimp only [m] at hm; omega]

lemma packStage_eval_slotSliceEmb
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr)
    (pos : Fin C.M) (off len : ℕ) (hoff : off + len ≤ C.w_rec) (v : Fin len) :
    C.packStage A K L P Arr Tr Scr
        (slotSliceEmb C.offArr C.w_rec C.M off len C.total hoff C.offArr_le pos v) =
      Arr pos (segEmb off len C.w_rec hoff v) := by
  have he : slotSliceEmb C.offArr C.w_rec C.M off len C.total hoff C.offArr_le pos v =
      C.arr2AllEmb (finProdFinEquiv (pos, segEmb off len C.w_rec hoff v)) := by
    apply Fin.ext
    rw [slotSliceEmb_val, C.arr2AllEmb_pair, segEmb_val]
    omega
  rw [he, C.packStage_arr2AllEmb]

lemma packStage_eval_slotSliceEmb_rev
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Arr : Fin C.M → Qubits C.w_rec)
    (Tr : Qubits C.T) (Scr : Qubits C.lenScr)
    (pos : Fin C.M) (off len : ℕ) (hoff : off + len ≤ C.w_rec) (v : Fin len) :
    C.packStage A K L P Arr Tr Scr
        (revEmb (slotSliceEmb C.offArr C.w_rec C.M off len C.total hoff C.offArr_le pos) v) =
      Arr pos (segEmb off len C.w_rec hoff v.rev) := by
  rw [revEmb_apply, C.packStage_eval_slotSliceEmb]

lemma natToBitsLSB_comp_rev (O : OccArith54) {w k : ℕ} (hk : k < 2 ^ w) :
    (natToBitsLSB w k ∘ Fin.rev) = natToBits w k := by
  funext i; exact (O.natToBits_apply hk i).symm

lemma act_initArr1C (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (Tr : Qubits C.T) :
    let P_bits := fun i : Fin C.n => natToBitsLSB C.w_v (prefSum54 α i)
    act C.initArr1C.unitary (ket (C.packState A K L P_bits (fun _ _ => false) Tr)) =
      ket (C.packState A K L P_bits (fun pos => C.padRec1 (C.w2RecAt (C.extBeta α) pos)) Tr) := by
  intro P_bits
  let zAt : (t : ℕ) → t ≤ C.M → Qubits C.total := fun t _ =>
    C.packState A K L P_bits
      (fun pos => if pos.1 < t then C.padRec1 (C.w2RecAt (C.extBeta α) pos) else fun _ => false) Tr
  have hrun := act_seqList_fin_ket C.initArr1StepC zAt fun t ht => by
    let cur : Fin C.M := ⟨t, ht⟩
    let Arr_t : Fin C.M → Qubits C.w_rec :=
      fun pos => if pos.1 < t then C.padRec1 (C.w2RecAt (C.extBeta α) pos) else fun _ => false
    have hcur_zero : Arr_t cur = fun _ => false := if_neg (by dsimp [cur]; omega)
    have ha_lt_m : C.m < 2 ^ C.w_a := C.m_lt_two_pow_w_a
    have hN1_lt : C.N + 1 < 2 ^ C.w_v := C.N_add_one_lt_two_pow_w_v
    have step_a1 : ∀ (a_val : ℕ), a_val < 2 ^ C.w_a →
        act (C.setConstC C.w_a a_val (C.a1EmbLSB cur)).unitary (ket (zAt t (le_of_lt ht))) =
          ket (C.packState A K L P_bits
            (Function.update Arr_t cur
              (updateOn (segEmb C.w_v C.w_a C.w_rec C.hoff_a1) (fun _ => false) (natToBits C.w_a a_val)))
            Tr) := by
      intro a_val ha
      rw [C.act_setConstC]
      have ha_fn : setConstFn54 C.w_a a_val (zAt t (le_of_lt ht) ∘ C.a1EmbLSB cur) = natToBitsLSB C.w_a a_val := by
        funext u
        simp only [setConstFn54, Function.comp_apply, zAt, packState, a1EmbLSB, a1EmbMSB]
        rw [C.packStage_eval_slotSliceEmb_rev, if_neg (by dsimp [cur]; omega)]
        simp
      rw [ha_fn]
      change ket (updateOn (revEmb (slotSliceEmb C.offArr C.w_rec C.M C.w_v C.w_a C.total C.hoff_a1 C.offArr_le cur))
          (C.packStage A K L P_bits Arr_t Tr (fun _ => false)) (natToBitsLSB C.w_a a_val)) = _
      rw [C.packStage_update_slotSliceEmb_rev, hcur_zero, natToBitsLSB_comp_rev C.O ha]
    have finish_slot : ∀ (a_val c_val : ℕ), a_val < 2 ^ C.w_a → c_val < 2 ^ C.w_v →
        C.w2RecAt (C.extBeta α) cur = C.packRec1 (natToBits C.w_v c_val) (natToBits C.w_a a_val) (fun _ => false) →
        C.packState A K L P_bits
          (Function.update Arr_t cur (updateOn (segEmb 0 C.w_v C.w_rec C.hoff_c1)
            (updateOn (segEmb C.w_v C.w_a C.w_rec C.hoff_a1) (fun _ => false) (natToBits C.w_a a_val))
            (natToBits C.w_v c_val))) Tr = zAt (t + 1) ht := by
      intro a_val c_val ha hc hw2
      rw [C.set_a1_c1_on_zero_slot a_val c_val ha hc, ← hw2]
      dsimp only [zAt, packState]
      congr 1; funext pos
      by_cases hp : pos = cur
      · subst hp; rw [Function.update_self, if_pos (by dsimp [cur]; omega)]
      · rw [Function.update_of_ne hp]
        have hiff : pos.1 < t ↔ pos.1 < t + 1 := by
          have := Fin.val_ne_of_ne hp; dsimp [cur] at this; omega
        simp [Arr_t, hiff]
    dsimp only [initArr1StepC]
    by_cases h1 : cur.1 < C.n
    · rw [dif_pos h1, LayeredCircuit.seq_unitary, act_mul]
      let idx : Fin C.n := ⟨cur.1, h1⟩
      have hpref_lt : prefSum54 α idx < 2 ^ C.w_v := C.prefSum_alpha_lt_two_pow hα idx
      have hidx_lt : cur.1 < 2 ^ C.w_a := lt_trans (lt_trans h1 (by dsimp only [m]; omega)) ha_lt_m
      have hw2 : C.w2RecAt (C.extBeta α) cur =
          C.packRec1 (natToBits C.w_v (prefSum54 α idx)) (natToBits C.w_a cur.1) (fun _ => false) := by
        have hmN : cur.1 < C.m + C.N := by dsimp only [m]; omega
        dsimp only [w2RecAt, encodeRec1, liftW2]
        rw [dif_pos hmN, C.wtilde2_elem_spec _ cur.1 hmN, dif_pos h1, C.prefSum_extBeta_lt α cur.1 h1]
      rw [step_a1 cur.1 hidx_lt, C.act_copyRegC]
      let Arr_step1 := Function.update Arr_t cur
        (updateOn (segEmb C.w_v C.w_a C.w_rec C.hoff_a1) (fun _ => false) (natToBits C.w_a cur.1))
      have hmid_val : (fun u => xor ((C.packState A K L P_bits Arr_step1 Tr) (C.c1EmbLSB cur u))
          ((C.packState A K L P_bits Arr_step1 Tr) (C.pSlotEmbLSB idx u))) = natToBitsLSB C.w_v (prefSum54 α idx) := by
        funext u
        simp only [packState, packStage_pSlotEmbLSB]
        have hc_false : C.packStage A K L P_bits Arr_step1 Tr (fun _ => false) (C.c1EmbLSB cur u) = false := by
          change C.packStage _ _ _ _ _ _ _
            (revEmb (slotSliceEmb C.offArr C.w_rec C.M 0 C.w_v C.total C.hoff_c1 C.offArr_le cur) u) = false
          rw [C.packStage_eval_slotSliceEmb_rev]; dsimp only [Arr_step1]; rw [Function.update_self]
          have hnot : segEmb 0 C.w_v C.w_rec C.hoff_c1 u.rev ∉ Set.range (segEmb C.w_v C.w_a C.w_rec C.hoff_a1) := by
            rintro ⟨v, hv⟩; have := congrArg Fin.val hv; simp [segEmb_val] at this; have := u.rev.isLt; omega
          rw [updateOn_apply_not_mem _ _ _ hnot]
        rw [hc_false, Bool.false_xor]
      rw [hmid_val]
      change ket (updateOn (revEmb (slotSliceEmb C.offArr C.w_rec C.M 0 C.w_v C.total C.hoff_c1 C.offArr_le cur))
          (C.packStage A K L P_bits Arr_step1 Tr (fun _ => false)) (natToBitsLSB C.w_v (prefSum54 α idx))) = _
      rw [C.packStage_update_slotSliceEmb_rev]; dsimp only [Arr_step1]
      rw [Function.update_self, Function.update_idem, natToBitsLSB_comp_rev C.O hpref_lt]
      exact congrArg ket (finish_slot cur.1 (prefSum54 α idx) hidx_lt hpref_lt hw2)
    · rw [dif_neg h1]
      have set_const_both : ∀ (a_val c_val : ℕ), a_val < 2 ^ C.w_a → c_val < 2 ^ C.w_v →
          C.w2RecAt (C.extBeta α) cur = C.packRec1 (natToBits C.w_v c_val) (natToBits C.w_a a_val) (fun _ => false) →
          act ((C.setConstC C.w_a a_val (C.a1EmbLSB cur)).seq (C.setConstC C.w_v c_val (C.c1EmbLSB cur))).unitary
            (ket (zAt t (le_of_lt ht))) = ket (zAt (t + 1) ht) := by
        intro a_val c_val ha hc hw2
        rw [LayeredCircuit.seq_unitary, act_mul, step_a1 a_val ha, C.act_setConstC]
        let Arr_step := Function.update Arr_t cur
          (updateOn (segEmb C.w_v C.w_a C.w_rec C.hoff_a1) (fun _ => false) (natToBits C.w_a a_val))
        have hc_fn : setConstFn54 C.w_v c_val ((C.packState A K L P_bits Arr_step Tr) ∘ C.c1EmbLSB cur) =
            natToBitsLSB C.w_v c_val := by
          funext u
          dsimp only [setConstFn54, Function.comp_apply, packState]
          have hc_false : C.packStage A K L P_bits Arr_step Tr (fun _ => false) (C.c1EmbLSB cur u) = false := by
            change C.packStage _ _ _ _ _ _ _
              (revEmb (slotSliceEmb C.offArr C.w_rec C.M 0 C.w_v C.total C.hoff_c1 C.offArr_le cur) u) = false
            rw [C.packStage_eval_slotSliceEmb_rev]; dsimp only [Arr_step]; rw [Function.update_self]
            have hnot : segEmb 0 C.w_v C.w_rec C.hoff_c1 u.rev ∉ Set.range (segEmb C.w_v C.w_a C.w_rec C.hoff_a1) := by
              rintro ⟨v, hv⟩; have := congrArg Fin.val hv; simp [segEmb_val] at this; have := u.rev.isLt; omega
            rw [updateOn_apply_not_mem _ _ _ hnot]
          rw [hc_false, Bool.false_xor]
        rw [hc_fn]
        change ket (updateOn (revEmb (slotSliceEmb C.offArr C.w_rec C.M 0 C.w_v C.total C.hoff_c1 C.offArr_le cur))
            (C.packStage A K L P_bits Arr_step Tr (fun _ => false)) (natToBitsLSB C.w_v c_val)) = _
        rw [C.packStage_update_slotSliceEmb_rev]; dsimp only [Arr_step]
        rw [Function.update_self, Function.update_idem, natToBitsLSB_comp_rev C.O hc]
        exact congrArg ket (finish_slot a_val c_val ha hc hw2)
      by_cases h2 : cur.1 = C.n
      · rw [dif_pos h2]
        refine set_const_both C.n C.N (lt_trans (by dsimp only [m]; omega) ha_lt_m) (by omega) ?_
        have hmN : cur.1 < C.m + C.N := by dsimp only [m]; omega
        dsimp only [w2RecAt, encodeRec1, liftW2]
        rw [dif_pos hmN, C.wtilde2_elem_spec _ cur.1 hmN, dif_neg h1, dif_pos h2, C.prefSum_extBeta_last hα]
      · rw [dif_neg h2]
        by_cases h3 : cur.1 < C.m + C.N
        · rw [dif_pos h3]
          refine set_const_both C.m (cur.1 - C.m) ha_lt_m (by omega) ?_
          dsimp only [w2RecAt, encodeRec1, liftW2]
          rw [dif_pos h3, C.wtilde2_elem_spec _ cur.1 h3, dif_neg h1, dif_neg h2]
        · rw [dif_neg h3]
          refine set_const_both C.m (C.N + 1) ha_lt_m hN1_lt ?_
          dsimp only [w2RecAt, encodeRec1, liftW2]
          rw [dif_neg h3]
  have hz0 : zAt 0 (Nat.zero_le C.M) = C.packState A K L P_bits (fun _ _ => false) Tr := by
    dsimp only [zAt]; rfl
  have hzM : zAt C.M le_rfl = C.packState A K L P_bits (fun pos => C.padRec1 (C.w2RecAt (C.extBeta α) pos)) Tr := by
    dsimp only [zAt]; congr 1; funext pos; rw [if_pos pos.isLt]
  rw [hz0, hzM] at hrun
  exact hrun

/-! #### 1.3 Copy Total Particle Count `K := P[n - 1]` (`copyKC`) -/

lemma hdisj_pSlot_k (i : Fin C.n) : ∀ a b, C.pSlotEmbLSB i a ≠ C.kEmbLSB b :=
  C.emb_disj_of_bounds _ _ C.offP C.offArr C.offK C.offL
    (C.pSlotEmbLSB_bounds i) C.kEmbLSB_bounds
    (Or.inr (by dsimp [offP, offL]; omega))

noncomputable def copyKC : LayeredCircuit C.total :=
  C.copyRegC C.w_v (C.pSlotEmbLSB ⟨C.n - 1, by have := C.hn; omega⟩) C.kEmbLSB
    (C.hdisj_pSlot_k ⟨C.n - 1, by have := C.hn; omega⟩)

lemma copyKC_size : C.copyKC.size = C.w_v := C.copyRegC_size _ _ _ _

lemma act_copyKC (α : Fin C.n → ℕ)
    (A : Fin C.n → Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (Arr : Fin C.M → Qubits C.w_rec) (Tr : Qubits C.T) :
    let P_bits := fun i : Fin C.n => natToBitsLSB C.w_v (prefSum54 α i)
    let K_bits := natToBitsLSB C.w_v (∑ i : Fin C.n, α i)
    act C.copyKC.unitary (ket (C.packState A (fun _ => false) L P_bits Arr Tr)) =
      ket (C.packState A K_bits L P_bits Arr Tr) := by
  intro P_bits K_bits
  dsimp only [copyKC]
  rw [C.act_copyRegC]
  have hf : (fun u => xor ((C.packState A (fun _ => false) L P_bits Arr Tr) (C.kEmbLSB u))
      ((C.packState A (fun _ => false) L P_bits Arr Tr) (C.pSlotEmbLSB ⟨C.n - 1, by have := C.hn; omega⟩ u))) = K_bits := by
    funext u
    simp only [packState, packStage_kEmbLSB, packStage_pSlotEmbLSB, Bool.false_xor]
    dsimp only [P_bits, K_bits]
    rw [C.prefSum_alpha_last α]
  rw [hf]
  exact congrArg ket (C.packStage_update_kEmbLSB _ _ _ _ _ _ _ _)

/-! #### 1.4 Pass-1 Bitonic Sort (`sort1C`) & Combinatorial Spec of Sorted `xs1` -/

def rec1C (r : Qubits C.w_rec1) : Qubits C.w_v := fun u => r (Fin.castAdd C.w_p1 (Fin.castAdd C.w_a u))
def rec1A (r : Qubits C.w_rec1) : Qubits C.w_a := fun u => r (Fin.castAdd C.w_p1 (Fin.natAdd C.w_v u))
def rec1B (r : Qubits C.w_rec1) : Qubits C.w_a := fun u => r (Fin.natAdd C.w_k1 u)

def decodeRec1 (r : Qubits C.w_rec1) : Sec5Rec54 :=
  (bitsToNat (C.rec1A r), bitsToNatLSB (C.rec1B r), bitsToNat (C.rec1C r))

@[simp] lemma rec1C_packRec1 (c : Qubits C.w_v) (a b : Qubits C.w_a) :
    C.rec1C (C.packRec1 c a b) = c := by
  funext u; dsimp only [rec1C, packRec1]; rw [Fin.append_left, Fin.append_left]

@[simp] lemma rec1A_packRec1 (c : Qubits C.w_v) (a b : Qubits C.w_a) :
    C.rec1A (C.packRec1 c a b) = a := by
  funext u; dsimp only [rec1A, packRec1]; rw [Fin.append_left, Fin.append_right]

@[simp] lemma rec1B_packRec1 (c : Qubits C.w_v) (a b : Qubits C.w_a) :
    C.rec1B (C.packRec1 c a b) = b := by
  funext u; dsimp only [rec1B, packRec1]; rw [Fin.append_right]

lemma packRec1_rec (r : Qubits C.w_rec1) :
    C.packRec1 (C.rec1C r) (C.rec1A r) (C.rec1B r) = r := by
  funext u
  refine Fin.addCases (fun i => ?_) (fun j => ?_) u
  · refine Fin.addCases (fun ic => ?_) (fun ia => ?_) i
    · simp [packRec1, rec1C]
    · simp [packRec1, rec1A]
  · simp [packRec1, rec1B]

lemma decodeRec1_packRec1 {a c : ℕ} (ha : a < 2 ^ C.w_a) (hc : c < 2 ^ C.w_v) (b : Qubits C.w_a) :
    C.decodeRec1 (C.packRec1 (natToBits C.w_v c) (natToBits C.w_a a) b) = (a, bitsToNatLSB b, c) := by
  dsimp only [decodeRec1]
  rw [C.rec1A_packRec1, C.rec1B_packRec1, C.rec1C_packRec1,
    bitsToNat_natToBits_exact ha, bitsToNat_natToBits_exact hc]

lemma bitsToNat_recKey54_rec1 (r : Qubits C.w_rec1) :
    bitsToNat (recKey54 r) = bitsToNat (C.rec1C r) * 2 ^ C.w_a + bitsToNat (C.rec1A r) := by
  have hk : recKey54 r = Fin.append (C.rec1C r) (C.rec1A r) := by
    funext u
    refine Fin.addCases (fun i => ?_) (fun j => ?_) u
    · simp [recKey54, rec1C]
    · simp [recKey54, rec1A]
  rw [hk, bitsToNat_append]

lemma keyW3_le_of_bitsToNat_recKey1_le {r₁ r₂ : Qubits C.w_rec1}
    (h : bitsToNat (recKey54 r₁) ≤ bitsToNat (recKey54 r₂)) :
    keyW3_54 (C.decodeRec1 r₁) ≤ keyW3_54 (C.decodeRec1 r₂) := by
  rw [C.bitsToNat_recKey54_rec1, C.bitsToNat_recKey54_rec1] at h
  have ha1 := bitsToNat_lt_two_pow (C.rec1A r₁)
  have ha2 := bitsToNat_lt_two_pow (C.rec1A r₂)
  dsimp only [keyW3_54, decodeRec1]
  rcases Nat.lt_trichotomy (bitsToNat (C.rec1C r₁)) (bitsToNat (C.rec1C r₂)) with hlt | heq | hgt
  · exact le_of_lt (Prod.Lex.left _ _ hlt)
  · rw [heq] at h ⊢
    exact Prod.Lex.right _ (by omega)
  · exfalso
    have hmul : (bitsToNat (C.rec1C r₂) + 1) * 2 ^ C.w_a ≤ bitsToNat (C.rec1C r₁) * 2 ^ C.w_a :=
      Nat.mul_le_mul_right (2 ^ C.w_a) hgt
    rw [Nat.succ_mul] at hmul
    omega

lemma hAA_sort1 : ∀ i k, C.arr1AllEmb i ≠ C.scrEmb 0 C.w_k1 C.offScr_sort1 k :=
  C.emb_disj_of_bounds _ _ C.offArr C.offTr C.offScr (C.offScr + C.w_k1)
    C.arr1AllEmb_bounds (C.scrEmb_bounds 0 C.w_k1 C.offScr_sort1)
    (Or.inl (by dsimp [offScr, lenTr]; omega))

lemma hTA_sort1 : ∀ j k, C.trEmb j ≠ C.scrEmb 0 C.w_k1 C.offScr_sort1 k :=
  C.emb_disj_of_bounds _ _ C.offTr C.offScr C.offScr (C.offScr + C.w_k1)
    C.trEmb_bounds (C.scrEmb_bounds 0 C.w_k1 C.offScr_sort1) (Or.inl le_rfl)

noncomputable def sort1C : LayeredCircuit C.total :=
  C.sortKeyC C.w_k1 C.w_p1 C.arr1AllEmb (C.scrEmb 0 C.w_k1 C.offScr_sort1) C.hAT_arr1 C.hAA_sort1 C.hTA_sort1

lemma sort1C_size :
    (C.sort1C.size : ℝ) ≤ C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k1 + C.w_p1 + 1 : ℝ) :=
  C.sortKeyC_size _ _ _ _ _ _ _

noncomputable def xs1 (α : Fin C.n → ℕ) : Fin C.M → Qubits C.w_rec1 :=
  sort (fun r => bitsToNat (recKey54 r)) C.d true (C.w2RecAt (C.extBeta α))

noncomputable def trs1 (α : Fin C.n → ℕ) : Qubits C.T :=
  sortTrace (fun r => bitsToNat (recKey54 r)) C.d true (C.w2RecAt (C.extBeta α))

lemma act_sort1C (α : Fin C.n → ℕ) (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v)
    (L : Fin C.N → Qubits C.s) (P : Fin C.n → Qubits C.w_v) :
    act C.sort1C.unitary
        (ket (C.packState A K L P (fun pos => C.padRec1 (C.w2RecAt (C.extBeta α) pos)) (fun _ => false))) =
      ket (C.packStage A K L P (fun pos => C.padRec1 (C.xs1 α pos)) (C.trs1 α) (fun _ => false)) := by
  dsimp only [sort1C]
  rw [C.act_sortKeyC C.w_k1 C.w_p1 C.arr1AllEmb (C.scrEmb 0 C.w_k1 C.offScr_sort1)
      C.hAT_arr1 C.hAA_sort1 C.hTA_sort1 _ (C.w2RecAt (C.extBeta α))]
  · exact congrArg ket (C.padRec1_update_arr1_tr _ _ _ _ _ _ _ _ _)
  · exact C.packStage_arr1AllEmb _ _ _ _ _ _ _
  · funext u; simp [packState]
  · funext u; simp [packState]

lemma countP_ofFn_eq {α : Type} :
    ∀ (k : ℕ) (f : Fin k → α) (p : α → Bool),
      (List.ofFn f).countP p = (Finset.univ.filter fun i : Fin k => p (f i) = true).card
  | 0, _, _ => by simp
  | k + 1, f, p => by
    rw [List.ofFn_succ, List.countP_cons, countP_ofFn_eq k (fun i : Fin k => f i.succ) p]
    have hdisj : (0 : Fin (k + 1)) ∉ (Finset.univ.filter fun i : Fin k => p (f i.succ) = true).image Fin.succ := by
      simp [Finset.mem_image]
    have hinj : ((Finset.univ.filter fun i : Fin k => p (f i.succ) = true).image Fin.succ).card =
        (Finset.univ.filter fun i : Fin k => p (f i.succ) = true).card :=
      Finset.card_image_of_injective _ (Fin.succ_injective k)
    cases h : p (f 0)
    · have himg : (Finset.univ.filter fun i : Fin (k + 1) => p (f i) = true) =
          (Finset.univ.filter fun i : Fin k => p (f i.succ) = true).image Fin.succ := by
        ext i
        induction i using Fin.cases with
        | zero => simp [h]
        | succ j => simp
      rw [himg, hinj]; simp
    · have himg : (Finset.univ.filter fun i : Fin (k + 1) => p (f i) = true) =
          insert 0 ((Finset.univ.filter fun i : Fin k => p (f i.succ) = true).image Fin.succ) := by
        ext i
        induction i using Fin.cases with
        | zero => simp [h]
        | succ j => simp
      rw [himg, Finset.card_insert_of_notMem hdisj, hinj]; simp [add_comm]

lemma liftW2_bounds {α : Fin C.n → ℕ} (hα : ∑ i : Fin C.n, α i ≤ C.N) (pos : Fin C.M) :
    (C.liftW2 (C.extBeta α) pos).1 ≤ C.m ∧
      (C.liftW2 (C.extBeta α) pos).2.1 = 0 ∧
      (C.liftW2 (C.extBeta α) pos).2.2 ≤ C.N + 1 := by
  dsimp only [liftW2]
  by_cases hpos : pos.1 < C.m + C.N
  · rw [dif_pos hpos, C.wtilde2_elem_spec _ pos.1 hpos]
    by_cases h1 : pos.1 < C.n
    · rw [dif_pos h1]
      refine ⟨by dsimp only [m]; omega, rfl, ?_⟩
      dsimp only; rw [C.prefSum_extBeta_lt α pos.1 h1]; have := C.O.prefSum_le_sum α ⟨pos.1, h1⟩; omega
    · rw [dif_neg h1]
      by_cases h2 : pos.1 = C.n
      · rw [dif_pos h2]
        refine ⟨by dsimp only [m]; omega, rfl, ?_⟩
        dsimp only; rw [C.prefSum_extBeta_last hα]; omega
      · rw [dif_neg h2]
        exact ⟨le_rfl, rfl, by dsimp only; omega⟩
  · rw [dif_neg hpos]; exact ⟨le_rfl, rfl, le_rfl⟩

lemma decodeRec1_w2RecAt {α : Fin C.n → ℕ} (hα : ∑ i : Fin C.n, α i ≤ C.N) (pos : Fin C.M) :
    C.decodeRec1 (C.w2RecAt (C.extBeta α) pos) = C.liftW2 (C.extBeta α) pos := by
  have hb := C.liftW2_bounds hα pos
  have ha : (C.liftW2 (C.extBeta α) pos).1 < 2 ^ C.w_a := lt_of_le_of_lt hb.1 C.m_lt_two_pow_w_a
  have hc : (C.liftW2 (C.extBeta α) pos).2.2 < 2 ^ C.w_v := lt_of_le_of_lt hb.2.2 C.N_add_one_lt_two_pow_w_v
  dsimp only [w2RecAt, encodeRec1]
  rw [C.decodeRec1_packRec1 ha hc, C.O.bitsToNatLSB_all_false]
  exact Prod.ext rfl (Prod.ext hb.2.1.symm rfl)

lemma xs1_mem_props {α : Fin C.n → ℕ} (hα : ∑ i : Fin C.n, α i ≤ C.N) (pos : Fin C.M) :
    C.rec1B (C.xs1 α pos) = (fun _ => false) ∧
      (C.decodeRec1 (C.xs1 α pos)).1 ≤ C.m ∧
      (C.decodeRec1 (C.xs1 α pos)).2.1 = 0 ∧
      (C.decodeRec1 (C.xs1 α pos)).2.2 ≤ C.N + 1 := by
  have hperm := C.R.sort_perm (fun r : Qubits C.w_rec1 => bitsToNat (recKey54 r)) C.d true (C.w2RecAt (C.extBeta α))
  have hmem : C.xs1 α pos ∈ List.ofFn (C.w2RecAt (C.extBeta α)) := by
    rw [← hperm.mem_iff]
    exact List.mem_ofFn.mpr ⟨pos, rfl⟩
  rcases List.mem_ofFn.mp hmem with ⟨p₀, hp₀⟩
  rw [← hp₀]
  have hb := C.liftW2_bounds hα p₀
  refine ⟨?_, ?_⟩
  · dsimp only [w2RecAt, encodeRec1]; exact C.rec1B_packRec1 _ _ _
  · rw [C.decodeRec1_w2RecAt hα p₀]; exact hb

lemma decodeRec1_xs1_prefix {α : Fin C.n → ℕ} (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (pos : ℕ) (hpos : pos < C.m + C.N) :
    C.decodeRec1 (C.xs1 α ⟨pos, lt_of_lt_of_le hpos C.m_add_N_le_M⟩) =
      (wtilde3_54 (C.extBeta α) C.N)[pos]'(by rw [C.O.wtilde3_length]; exact hpos) := by
  refine C.O.wtilde2_sort_prefix (C.extBeta α) (C.extBeta_sum hα) C.M
    (C.decodeRec1 ∘ C.w2RecAt (C.extBeta α)) (C.decodeRec1 ∘ C.xs1 α) C.m_add_N_le_M ?_ ?_ ?_ ?_ pos hpos
  · intro p hp
    dsimp only [Function.comp_apply]
    rw [C.decodeRec1_w2RecAt hα ⟨p, lt_of_lt_of_le hp C.m_add_N_le_M⟩, liftW2, dif_pos hp]
  · intro p hp hge
    dsimp only [Function.comp_apply]
    rw [C.decodeRec1_w2RecAt hα ⟨p, hp⟩, liftW2, dif_neg (by dsimp only; omega)]
  · have hperm := C.R.sort_perm (fun r : Qubits C.w_rec1 => bitsToNat (recKey54 r)) C.d true (C.w2RecAt (C.extBeta α))
    have hmap := List.Perm.map C.decodeRec1 hperm
    rwa [List.map_ofFn, List.map_ofFn] at hmap
  · intro i j hij
    exact C.keyW3_le_of_bitsToNat_recKey1_le
      (C.R.monotone_sort (fun r : Qubits C.w_rec1 => bitsToNat (recKey54 r)) C.d (C.w2RecAt (C.extBeta α)) hij)

lemma xs1_suffix_c_eq {α : Fin C.n → ℕ} (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (pos : Fin C.M) (hge : C.m + C.N ≤ pos.1) :
    (C.decodeRec1 (C.xs1 α pos)).2.2 = C.N + 1 := by
  have hle := (C.xs1_mem_props hα pos).2.2.2
  by_contra hne
  have hc_le : (C.decodeRec1 (C.xs1 α pos)).2.2 ≤ C.N := by omega
  have hperm := C.R.sort_perm (fun r : Qubits C.w_rec1 => bitsToNat (recKey54 r)) C.d true (C.w2RecAt (C.extBeta α))
  let p : Qubits C.w_rec1 → Bool := fun r => decide ((C.decodeRec1 r).2.2 ≤ C.N)
  have hcnt := hperm.countP_eq p
  rw [countP_ofFn_eq, countP_ofFn_eq] at hcnt
  have hcard2 : (Finset.univ.filter fun i : Fin C.M => p (C.w2RecAt (C.extBeta α) i) = true).card = C.m + C.N := by
    have hset : (Finset.univ.filter fun i : Fin C.M => p (C.w2RecAt (C.extBeta α) i) = true) =
        Finset.univ.filter fun i : Fin C.M => i.1 < C.m + C.N := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, decide_eq_true_eq, C.decodeRec1_w2RecAt hα i]
      by_cases hi : i.1 < C.m + C.N
      · simp only [hi, iff_true]
        dsimp only [liftW2]
        rw [dif_pos hi, C.wtilde2_elem_spec _ i.1 hi]
        split_ifs with h1 h2
        · dsimp only; rw [C.prefSum_extBeta_lt α i.1 h1]; exact le_trans (C.O.prefSum_le_sum α ⟨i.1, h1⟩) hα
        · dsimp only; rw [C.prefSum_extBeta_last hα]
        · dsimp only; omega
      · simp only [hi, iff_false]; dsimp only [liftW2]; rw [dif_neg hi]; dsimp only; omega
    rw [hset]
    let emb : Fin (C.m + C.N) ↪ Fin C.M :=
      ⟨fun j => ⟨j.1, lt_of_lt_of_le j.isLt C.m_add_N_le_M⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
    have hinj : (Finset.univ.filter fun i : Fin C.M => i.1 < C.m + C.N) = Finset.univ.map emb := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      exact ⟨fun hi => ⟨⟨i.1, hi⟩, Fin.ext rfl⟩, fun ⟨j, hj⟩ => by rw [← hj]; exact j.isLt⟩
    rw [hinj, Finset.card_map, Finset.card_fin]
  let emb : Fin (C.m + C.N) ↪ Fin C.M :=
    ⟨fun j => ⟨j.1, lt_of_lt_of_le j.isLt C.m_add_N_le_M⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
  have hsub1 : Finset.univ.map emb ∪ {pos} ⊆
      Finset.univ.filter fun i : Fin C.M => p (C.xs1 α i) = true := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, decide_eq_true_eq]
    rcases Finset.mem_union.mp hi with hpre | hsing
    · rcases Finset.mem_map.mp hpre with ⟨j, _, rfl⟩
      have hmono := C.keyW3_le_of_bitsToNat_recKey1_le
        (C.R.monotone_sort (fun r : Qubits C.w_rec1 => bitsToNat (recKey54 r)) C.d (C.w2RecAt (C.extBeta α))
          (Fin.le_iff_val_le_val.mpr (show (emb j).1 ≤ pos.1 from le_trans (le_of_lt j.isLt) hge)))
      have hc_le_mono : (C.decodeRec1 (C.xs1 α (emb j))).2.2 ≤ (C.decodeRec1 (C.xs1 α pos)).2.2 := by
        by_contra hlt
        have hgt : (C.decodeRec1 (C.xs1 α pos)).2.2 < (C.decodeRec1 (C.xs1 α (emb j))).2.2 := by omega
        have hstrict : keyW3_54 (C.decodeRec1 (C.xs1 α pos)) < keyW3_54 (C.decodeRec1 (C.xs1 α (emb j))) :=
          Prod.Lex.left _ _ hgt
        exact absurd hmono (not_le_of_gt hstrict)
      omega
    · rw [Finset.mem_singleton.mp hsing]; exact hc_le
  have hpos_not : pos ∉ Finset.univ.map emb := by
    rw [Finset.mem_map]; rintro ⟨j, _, hj⟩
    have hjv : j.1 = pos.1 := congrArg Fin.val hj
    have := j.isLt; omega
  have hcard_ge := Finset.card_le_card hsub1
  rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hpos_not),
    Finset.card_map, Finset.card_fin, Finset.card_singleton] at hcard_ge
  have hcard1 : (Finset.univ.filter fun i : Fin C.M => p (C.xs1 α i) = true).card = C.m + C.N := by
    have hcnt' : (Finset.univ.filter fun i : Fin C.M => p (C.xs1 α i) = true).card =
        (Finset.univ.filter fun i : Fin C.M => p (C.w2RecAt (C.extBeta α) i) = true).card := by
      dsimp only [xs1]
      (convert hcnt; exact Finset.ext fun _ => Iff.rfl)
    exact hcnt'.trans hcard2
  omega

/-! #### 1.5 Pass-1 Mode Assignment (`fillMode1C`) -/

abbrev posM_of_lt (pos : Fin (C.m + C.N)) : Fin C.M :=
  ⟨pos.1, lt_of_lt_of_le pos.isLt C.m_add_N_le_M⟩

abbrev flagEmb : Fin 1 ↪ Fin C.total := C.scrEmb 0 1 C.offScr_flag
abbrev TEmb : Fin C.w_pos ↪ Fin C.total := C.scrEmb 1 C.w_pos C.offScr_T
abbrev TEmb_wa : Fin C.w_a ↪ Fin C.total := C.scrEmb 1 C.w_a C.offScr_T_wa
abbrev UEmb : Fin C.w_pos ↪ Fin C.total := C.scrEmb (1 + C.w_pos) C.w_pos C.offScr_U
abbrev UEmb_wv : Fin C.w_v ↪ Fin C.total := C.scrEmb (1 + C.w_pos) C.w_v C.offScr_U_wv
abbrev UEmb_wa : Fin C.w_a ↪ Fin C.total := C.scrEmb (1 + C.w_pos) C.w_a C.offScr_U_wa
abbrev anc_wa : Fin C.w_a ↪ Fin C.total := C.scrEmb (1 + 2 * C.w_pos) C.w_a C.offScr_anc_wa
abbrev anc1 : Fin 1 ↪ Fin C.total := C.scrEmb (1 + 2 * C.w_pos) 1 C.offScr_anc1

lemma slotSlice_scr_disj (pos : Fin C.M) (off₁ len₁ off₂ len₂ : ℕ)
    (h1 : off₁ + len₁ ≤ C.w_rec) (h2 : off₂ + len₂ ≤ C.lenScr) :
    ∀ i j, slotSliceEmb C.offArr C.w_rec C.M off₁ len₁ C.total h1 C.offArr_le pos i ≠ C.scrEmb off₂ len₂ h2 j :=
  C.emb_disj_of_bounds _ _ C.offArr C.offTr (C.offScr + off₂) (C.offScr + off₂ + len₂)
    (C.slotSlice_in_arr pos off₁ len₁ h1) (C.scrEmb_bounds off₂ len₂ h2)
    (Or.inl (by dsimp [offScr, lenTr]; omega))

lemma slotSlice_rev_scr_disj (pos : Fin C.M) (off₁ len₁ off₂ len₂ : ℕ)
    (h1 : off₁ + len₁ ≤ C.w_rec) (h2 : off₂ + len₂ ≤ C.lenScr) :
    ∀ i j, revEmb (slotSliceEmb C.offArr C.w_rec C.M off₁ len₁ C.total h1 C.offArr_le pos) i ≠ C.scrEmb off₂ len₂ h2 j :=
  fun i j => C.slotSlice_scr_disj pos off₁ len₁ off₂ len₂ h1 h2 i.rev j

lemma scr_slotSlice_disj (pos : Fin C.M) (off₂ len₂ off₁ len₁ : ℕ)
    (h2 : off₂ + len₂ ≤ C.lenScr) (h1 : off₁ + len₁ ≤ C.w_rec) :
    ∀ i j, C.scrEmb off₂ len₂ h2 i ≠ slotSliceEmb C.offArr C.w_rec C.M off₁ len₁ C.total h1 C.offArr_le pos j :=
  C.emb_disj_symm (C.slotSlice_scr_disj pos off₁ len₁ off₂ len₂ h1 h2)

lemma scr_slotSlice_rev_disj (pos : Fin C.M) (off₂ len₂ off₁ len₁ : ℕ)
    (h2 : off₂ + len₂ ≤ C.lenScr) (h1 : off₁ + len₁ ≤ C.w_rec) :
    ∀ i j, C.scrEmb off₂ len₂ h2 i ≠ revEmb (slotSliceEmb C.offArr C.w_rec C.M off₁ len₁ C.total h1 C.offArr_le pos) j :=
  C.emb_disj_symm (C.slotSlice_rev_scr_disj pos off₁ len₁ off₂ len₂ h1 h2)

noncomputable def fillMode1Prefix (pos : Fin (C.m + C.N)) : LayeredCircuit C.total :=
  let posM := C.posM_of_lt pos
  (C.eqConstC C.w_a C.m (C.a1EmbLSB posM) C.flagEmb C.anc_wa
      (C.slotSlice_rev_scr_disj posM C.w_v C.w_a 0 1 C.hoff_a1 C.offScr_flag)
      (C.slotSlice_rev_scr_disj posM C.w_v C.w_a (1 + 2 * C.w_pos) C.w_a C.hoff_a1 C.offScr_anc_wa)
      (C.scrEmb_disj 0 1 (1 + 2 * C.w_pos) C.w_a C.offScr_flag C.offScr_anc_wa (Or.inl (by omega)))).seq
    ((C.setConstC C.w_pos pos.1 C.TEmb).seq
      ((C.copyRegC C.w_v (C.c1EmbLSB posM) C.UEmb_wv
          (C.slotSlice_rev_scr_disj posM 0 C.w_v (1 + C.w_pos) C.w_v C.hoff_c1 C.offScr_U_wv)).seq
        (C.subInPlaceC C.w_pos C.UEmb C.TEmb C.anc1
          (C.scrEmb_disj (1 + C.w_pos) C.w_pos 1 C.w_pos C.offScr_U C.offScr_T (Or.inr le_rfl))
          (C.scrEmb_disj (1 + C.w_pos) C.w_pos (1 + 2 * C.w_pos) 1 C.offScr_U C.offScr_anc1 (Or.inl (by omega)))
          (C.scrEmb_disj 1 C.w_pos (1 + 2 * C.w_pos) 1 C.offScr_T C.offScr_anc1 (Or.inl (by omega))))))

lemma fillMode1Prefix_size (pos : Fin (C.m + C.N)) :
    (C.fillMode1Prefix pos).size ≤ 14 * C.w_a + 15 * C.w_pos + C.w_v + 12 := by
  dsimp only [fillMode1Prefix]
  rw [LayeredCircuit.seq_size, LayeredCircuit.seq_size, LayeredCircuit.seq_size,
    C.copyRegC_size, C.subInPlaceC_size]
  have h1 := C.eqConstC_size C.w_a C.m (C.a1EmbLSB (C.posM_of_lt pos)) C.flagEmb C.anc_wa
    (C.slotSlice_rev_scr_disj (C.posM_of_lt pos) C.w_v C.w_a 0 1 C.hoff_a1 C.offScr_flag)
    (C.slotSlice_rev_scr_disj (C.posM_of_lt pos) C.w_v C.w_a (1 + 2 * C.w_pos) C.w_a C.hoff_a1 C.offScr_anc_wa)
    (C.scrEmb_disj 0 1 (1 + 2 * C.w_pos) C.w_a C.offScr_flag C.offScr_anc_wa (Or.inl (by omega)))
  have h2 := C.setConstC_size C.w_pos pos.1 C.TEmb
  omega

noncomputable def fillMode1StepC (pos : Fin (C.m + C.N)) : LayeredCircuit C.total :=
  let posM := C.posM_of_lt pos
  (C.fillMode1Prefix pos).seq
    ((C.ctrlCopyRegC C.w_a C.flagEmb C.TEmb_wa (C.b1EmbLSB posM)
        (C.scrEmb_disj 0 1 1 C.w_a C.offScr_flag C.offScr_T_wa (Or.inl le_rfl))
        (C.scr_slotSlice_disj posM 0 1 (C.w_v + C.w_a) C.w_a C.offScr_flag C.hoff_b1)
        (C.scr_slotSlice_disj posM 1 C.w_a (C.w_v + C.w_a) C.w_a C.offScr_T_wa C.hoff_b1)).seq
      (C.fillMode1Prefix pos).adj)

lemma fillMode1StepC_size (pos : Fin (C.m + C.N)) :
    (C.fillMode1StepC pos).size ≤ 33 * C.w_a + 30 * C.w_pos + 2 * C.w_v + 24 := by
  dsimp only [fillMode1StepC]
  rw [LayeredCircuit.seq_size, LayeredCircuit.seq_size, C.ctrlCopyRegC_size, LayeredCircuit.adj_size]
  have h1 := C.fillMode1Prefix_size pos
  omega

noncomputable def fillMode1C : LayeredCircuit C.total :=
  LayeredCircuit.seqList (List.ofFn C.fillMode1StepC)

lemma fillMode1C_size :
    C.fillMode1C.size ≤ (C.m + C.N) * (33 * C.w_a + 30 * C.w_pos + 2 * C.w_v + 24) :=
  seqList_ofFn_size_le C.fillMode1StepC _ C.fillMode1StepC_size

lemma act_fillMode1Prefix (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (x1_rec : Fin C.M → Qubits C.w_rec1) (Tr : Qubits C.T)
    (pos : Fin (C.m + C.N)) (b_cur : Qubits C.w_a)
    (ha_lt : (C.decodeRec1 (x1_rec (C.posM_of_lt pos))).1 < 2 ^ C.w_a)
    (hc_lt : (C.decodeRec1 (x1_rec (C.posM_of_lt pos))).2.2 < 2 ^ C.w_v) :
    let posM := C.posM_of_lt pos
    let a_val := (C.decodeRec1 (x1_rec posM)).1
    let c_val := (C.decodeRec1 (x1_rec posM)).2.2
    let x1' := Function.update x1_rec posM
      (C.packRec1 (natToBits C.w_v c_val) (natToBits C.w_a a_val) b_cur)
    let T_out := natToBitsLSB C.w_pos (2 ^ C.w_pos + pos.1 - c_val)
    let U_out : Qubits C.w_pos := fun j => if h : j.1 < C.w_v then natToBitsLSB C.w_v c_val ⟨j.1, h⟩ else false
    act (C.fillMode1Prefix pos).unitary
        (ket (C.packState A K L P (fun p => C.padRec1 (x1' p)) Tr)) =
      ket (C.packStage A K L P (fun p => C.padRec1 (x1' p)) Tr
        (C.packScr1 (decide (a_val = C.m)) T_out U_out)) := by
  intro posM a_val c_val x1' T_out U_out
  have hArr_posM : C.padRec1 (x1' posM) =
      C.padRec1 (C.packRec1 (natToBits C.w_v c_val) (natToBits C.w_a a_val) b_cur) := by
    dsimp only [x1']; rw [Function.update_self]
  dsimp only [fillMode1Prefix]
  rw [LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary,
    act_mul, act_mul, act_mul]
  -- 1. eqConstC
  rw [C.act_eqConstC _ _ _ _ _ _ _ _ _ (fun j => by simp [packState])]
  have ha_lt' : a_val < 2 ^ C.w_a := ha_lt
  have hc_lt' : c_val < 2 ^ C.w_v := hc_lt
  have hdec_eq : (fun j : Fin 1 => xor ((C.packState A K L P (fun p => C.padRec1 (x1' p)) Tr) (C.flagEmb j))
      (decide (∀ i : Fin C.w_a, (C.packState A K L P (fun p => C.padRec1 (x1' p)) Tr) (C.a1EmbLSB posM i) = natToBitsLSB C.w_a C.m i))) =
      fun _ => decide (a_val = C.m) := by
    funext j
    have hfl : C.packState A K L P (fun p => C.padRec1 (x1' p)) Tr (C.flagEmb j) = false := by simp [packState]
    rw [hfl, Bool.false_xor, decide_eq_decide]
    have ha_bits : (fun i : Fin C.w_a => C.packState A K L P (fun p => C.padRec1 (x1' p)) Tr (C.a1EmbLSB posM i)) = natToBitsLSB C.w_a a_val := by
      funext i
      simp only [packState, a1EmbLSB, a1EmbMSB]
      rw [C.packStage_eval_slotSliceEmb_rev, hArr_posM, C.padRec1_eval_a1]
      simpa using C.O.natToBits_apply ha_lt' i.rev
    constructor
    · intro h
      have hi : natToBitsLSB C.w_a a_val = natToBitsLSB C.w_a C.m := funext fun i => (congrFun ha_bits i).symm.trans (h i)
      have hb := congrArg bitsToNatLSB hi
      rw [bitsToNatLSB_natToBitsLSB ha_lt', bitsToNatLSB_natToBitsLSB C.m_lt_two_pow_w_a] at hb
      exact hb
    · intro h i
      rw [congrFun ha_bits i, h]
  rw [hdec_eq, packState, ← C.packScr1_zero, C.packStage_update_scrEmb, C.packScr1_update_flag]
  -- 2. setConstC
  rw [C.act_setConstC]
  have hpos_lt : pos.1 < 2 ^ C.w_pos := lt_trans (lt_of_lt_of_le pos.isLt C.m_add_N_le_M) C.M_lt_two_pow_w_pos
  have hT_zero : setConstFn54 C.w_pos pos.1 ((C.packStage A K L P (fun p => C.padRec1 (x1' p)) Tr
      (C.packScr1 (decide (a_val = C.m)) (fun _ => false) (fun _ => false))) ∘ C.TEmb) = natToBitsLSB C.w_pos pos.1 := by
    funext j
    simp only [setConstFn54, Function.comp_apply, TEmb, C.packStage_scrEmb]
    have hhj : (⟨1 + j.1, by have := j.isLt; dsimp [lenScr]; omega⟩ : Fin C.lenScr) =
        segEmb 1 C.w_pos C.lenScr C.offScr_T j := Fin.ext (by simp)
    rw [hhj, C.packScr1_T, Bool.false_xor]
  rw [hT_zero, C.packStage_update_scrEmb, C.packScr1_update_T]
  -- 3. copyRegC
  rw [C.act_copyRegC]
  have hc_bits : (fun u : Fin C.w_v => xor ((C.packStage A K L P (fun p => C.padRec1 (x1' p)) Tr
      (C.packScr1 (decide (a_val = C.m)) (natToBitsLSB C.w_pos pos.1) (fun _ => false))) (C.UEmb_wv u))
      ((C.packStage A K L P (fun p => C.padRec1 (x1' p)) Tr
      (C.packScr1 (decide (a_val = C.m)) (natToBitsLSB C.w_pos pos.1) (fun _ => false))) (C.c1EmbLSB posM u))) =
      natToBitsLSB C.w_v c_val := by
    funext u
    have hU0 : C.packStage A K L P (fun p => C.padRec1 (x1' p)) Tr
        (C.packScr1 (decide (a_val = C.m)) (natToBitsLSB C.w_pos pos.1) (fun _ => false))
        (C.UEmb_wv u) = false := by
      simp only [UEmb_wv, C.packStage_scrEmb]
      have hhj : (⟨1 + C.w_pos + u.1, by have := u.isLt; have := C.w_v_lt_w_pos; dsimp [lenScr]; omega⟩ : Fin C.lenScr) =
          segEmb (1 + C.w_pos) C.w_pos C.lenScr C.offScr_U ⟨u.1, lt_trans u.isLt C.w_v_lt_w_pos⟩ := Fin.ext (by simp)
      rw [hhj, C.packScr1_U]
    rw [hU0, Bool.false_xor]
    simp only [c1EmbLSB, c1EmbMSB]
    rw [C.packStage_eval_slotSliceEmb_rev, hArr_posM, C.padRec1_eval_c1]
    simpa using C.O.natToBits_apply hc_lt' u.rev
  rw [hc_bits, C.packStage_update_scrEmb, C.packScr1_update_U_wv]
  -- 4. subInPlaceC
  rw [C.act_subInPlaceC _ _ _ _ _ _ _ _ (fun j => by
    simp only [anc1, C.packStage_scrEmb]
    have hhj : (⟨1 + 2 * C.w_pos + j.1, by have := j.isLt; dsimp [lenScr]; omega⟩ : Fin C.lenScr) =
        segEmb (1 + 2 * C.w_pos) 1 C.lenScr C.offScr_anc1 j := Fin.ext (by simp)
    rw [hhj, C.packScr1_anc1])]
  have hU_val : bitsToNatLSB ((C.packStage A K L P (fun p => C.padRec1 (x1' p)) Tr
      (C.packScr1 (decide (a_val = C.m)) (natToBitsLSB C.w_pos pos.1) U_out)) ∘ C.UEmb) = c_val := by
    have hcomp : (C.packStage A K L P (fun p => C.padRec1 (x1' p)) Tr
        (C.packScr1 (decide (a_val = C.m)) (natToBitsLSB C.w_pos pos.1) U_out)) ∘ C.UEmb = U_out := by
      funext u; simp only [Function.comp_apply, UEmb, C.packStage_scrEmb]
      exact C.packScr1_U _ _ U_out u
    rw [hcomp]
    dsimp only [U_out]
    rw [bitsToNatLSB_pad_high_zero (le_of_lt C.w_v_lt_w_pos), bitsToNatLSB_natToBitsLSB hc_lt']
  have hT_val : bitsToNatLSB ((C.packStage A K L P (fun p => C.padRec1 (x1' p)) Tr
      (C.packScr1 (decide (a_val = C.m)) (natToBitsLSB C.w_pos pos.1) U_out)) ∘ C.TEmb) = pos.1 := by
    have hcomp : (C.packStage A K L P (fun p => C.padRec1 (x1' p)) Tr
        (C.packScr1 (decide (a_val = C.m)) (natToBitsLSB C.w_pos pos.1) U_out)) ∘ C.TEmb =
        natToBitsLSB C.w_pos pos.1 := by
      funext u; simp only [Function.comp_apply, TEmb, C.packStage_scrEmb]
      exact C.packScr1_T _ _ U_out u
    rw [hcomp, bitsToNatLSB_natToBitsLSB hpos_lt]
  change ket (updateOn C.TEmb (C.packStage A K L P (fun p => C.padRec1 (x1' p)) Tr
      (C.packScr1 (decide (a_val = C.m)) (natToBitsLSB C.w_pos pos.1) U_out)) _) = _
  rw [hU_val, hT_val, C.packStage_update_scrEmb, C.packScr1_update_T]

lemma act_fillMode1StepC (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (x1_rec : Fin C.M → Qubits C.w_rec1) (Tr : Qubits C.T)
    (pos : Fin (C.m + C.N))
    (hcur_xs1 : x1_rec (C.posM_of_lt pos) = C.xs1 α (C.posM_of_lt pos)) :
    let posM := C.posM_of_lt pos
    let t := (wtilde3_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde3_length]; exact pos.isLt)
    let b_new : Qubits C.w_a := if t.1 = C.m then natToBitsLSB C.w_a (modeOf54 (C.extBeta α) t.2.2) else fun _ => false
    let x1_next := Function.update x1_rec posM (C.packRec1 (natToBits C.w_v t.2.2) (natToBits C.w_a t.1) b_new)
    act (C.fillMode1StepC pos).unitary (ket (C.packState A K L P (fun p => C.padRec1 (x1_rec p)) Tr)) =
      ket (C.packState A K L P (fun p => C.padRec1 (x1_next p)) Tr) := by
  intro posM t b_new x1_next
  have ht_eq : C.decodeRec1 (C.xs1 α posM) = t := C.decodeRec1_xs1_prefix hα pos.1 pos.isLt
  have hmem := C.xs1_mem_props hα posM
  have ha_le : t.1 ≤ C.m := by rw [← ht_eq]; exact hmem.2.1
  have hc_le : t.2.2 ≤ C.N + 1 := by rw [← ht_eq]; exact hmem.2.2.2
  have ha_lt : t.1 < 2 ^ C.w_a := lt_of_le_of_lt ha_le C.m_lt_two_pow_w_a
  have hc_lt : t.2.2 < 2 ^ C.w_v := lt_of_le_of_lt hc_le C.N_add_one_lt_two_pow_w_v
  have hb0 : C.rec1B (x1_rec posM) = fun _ => false := by rw [hcur_xs1]; exact hmem.1
  have hx1_eq : x1_rec = Function.update x1_rec posM (C.packRec1 (natToBits C.w_v t.2.2) (natToBits C.w_a t.1) (fun _ => false)) := by
    funext p
    by_cases hp : p = posM
    · subst hp; rw [Function.update_self]
      have hrec : x1_rec posM = C.packRec1 (C.rec1C (x1_rec posM)) (C.rec1A (x1_rec posM)) (C.rec1B (x1_rec posM)) :=
        (C.packRec1_rec _).symm
      rw [hb0] at hrec
      have hC : C.rec1C (x1_rec posM) = natToBits C.w_v t.2.2 := by
        have hv : bitsToNat (C.rec1C (x1_rec posM)) = t.2.2 := by rw [← ht_eq, ← hcur_xs1]; rfl
        rw [← hv, natToBits_eq_bitsToNat_iff]
      have hA : C.rec1A (x1_rec posM) = natToBits C.w_a t.1 := by
        have hv : bitsToNat (C.rec1A (x1_rec posM)) = t.1 := by rw [← ht_eq, ← hcur_xs1]; rfl
        rw [← hv, natToBits_eq_bitsToNat_iff]
      rw [hrec, hC, hA]
    · rw [Function.update_of_ne hp]
  have hd_eq : C.decodeRec1 (x1_rec posM) = t := by rw [hcur_xs1]; exact ht_eq
  have hf_fwd := C.act_fillMode1Prefix A K L P x1_rec Tr pos (fun _ => false)
    (by rw [hd_eq]; exact ha_lt) (by rw [hd_eq]; exact hc_lt)
  have hf_bwd := C.act_fillMode1Prefix A K L P x1_rec Tr pos b_new
    (by rw [hd_eq]; exact ha_lt) (by rw [hd_eq]; exact hc_lt)
  dsimp only at hf_fwd hf_bwd
  rw [hd_eq] at hf_fwd hf_bwd
  rw [← hx1_eq] at hf_fwd
  dsimp only [fillMode1StepC]
  rw [LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul, hf_fwd]
  rw [C.act_ctrlCopyRegC]
  let scrMid := C.packScr1 (decide (t.1 = C.m)) (natToBitsLSB C.w_pos (2 ^ C.w_pos + pos.1 - t.2.2))
    (fun j => if h : j.1 < C.w_v then natToBitsLSB C.w_v t.2.2 ⟨j.1, h⟩ else false)
  have hmid : (fun u : Fin C.w_a =>
      if C.packStage A K L P (fun p => C.padRec1 (x1_rec p)) Tr scrMid (C.flagEmb 0) then
        xor (C.packStage A K L P (fun p => C.padRec1 (x1_rec p)) Tr scrMid (C.b1EmbLSB posM u))
          (C.packStage A K L P (fun p => C.padRec1 (x1_rec p)) Tr scrMid (C.TEmb_wa u))
      else C.packStage A K L P (fun p => C.padRec1 (x1_rec p)) Tr scrMid (C.b1EmbLSB posM u)) = b_new := by
    have hfl : C.packStage A K L P (fun p => C.padRec1 (x1_rec p)) Tr scrMid (C.flagEmb 0) =
        decide (t.1 = C.m) := by
      simp only [flagEmb, C.packStage_scrEmb, scrMid]; exact C.packScr1_flag _ _ _ 0
    have hb_read : ∀ u, C.packStage A K L P (fun p => C.padRec1 (x1_rec p)) Tr scrMid (C.b1EmbLSB posM u) = false := by
      intro u
      simp only [b1EmbLSB, C.packStage_eval_slotSliceEmb]
      rw [hx1_eq, Function.update_self, C.padRec1_eval_b1]
    rw [hfl]
    by_cases htm : t.1 = C.m
    · simp only [htm, decide_true, ↓reduceIte, b_new, if_pos htm]
      have hwspec := (C.O.wtilde3_pos_spec (C.extBeta α) (C.extBeta_sum hα) pos.1 (by rw [C.O.wtilde3_length]; exact pos.isLt)).1 htm
      have hsub_val : 2 ^ C.w_pos + pos.1 - t.2.2 = 2 ^ C.w_pos + (pos.1 - t.2.2) := by
        dsimp only [t]; exact Nat.add_sub_assoc hwspec.2.1 (2 ^ C.w_pos)
      funext u
      rw [hb_read u, Bool.false_xor]
      simp only [TEmb_wa, C.packStage_scrEmb]
      have hhj : (⟨1 + u.1, by have := u.isLt; have := C.w_a_lt_w_pos; dsimp [lenScr]; omega⟩ : Fin C.lenScr) =
          segEmb 1 C.w_pos C.lenScr C.offScr_T ⟨u.1, lt_trans u.isLt C.w_a_lt_w_pos⟩ := Fin.ext (by simp)
      dsimp only [scrMid]
      rw [hhj, C.packScr1_T, ← hwspec.2.2, hsub_val]
      dsimp only [natToBitsLSB]
      have hmod : (2 ^ C.w_pos + (pos.1 - t.2.2)) / 2 ^ u.1 % 2 = (pos.1 - t.2.2) / 2 ^ u.1 % 2 := by
        have hpow : 2 ^ C.w_pos = 2 ^ u.1 * 2 ^ (C.w_pos - u.1) := by
          rw [← pow_add, Nat.add_sub_cancel' (le_of_lt (lt_trans u.isLt C.w_a_lt_w_pos))]
        have hpos_ge1 : 1 ≤ C.w_pos - u.1 := by have := u.isLt; have := C.w_a_lt_w_pos; omega
        have heven : 2 ∣ 2 ^ (C.w_pos - u.1) := dvd_pow_self 2 (by omega)
        obtain ⟨q', hq'⟩ := heven
        rw [hpow, hq', show 2 ^ u.1 * (2 * q') + (pos.1 - t.2.2) = (pos.1 - t.2.2) + (2 ^ u.1) * (2 * q') by ring,
          Nat.add_mul_div_left _ _ (Nat.two_pow_pos u.1), Nat.add_mul_mod_self_left]
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hmod]
    · simp only [htm, decide_false, Bool.false_eq_true, ↓reduceIte, b_new, if_neg htm]
      funext u; exact hb_read u
  rw [hmid]
  change act _ (ket (updateOn (slotSliceEmb C.offArr C.w_rec C.M (C.w_v + C.w_a) C.w_a C.total C.hoff_b1 C.offArr_le posM)
      (C.packStage A K L P _ Tr _) b_new)) = _
  rw [C.packStage_update_slotSliceEmb]
  have hup_arr : Function.update (fun p => C.padRec1 (x1_rec p)) posM
      (updateOn (segEmb (C.w_v + C.w_a) C.w_a C.w_rec C.hoff_b1) (C.padRec1 (x1_rec posM)) b_new) =
      fun p => C.padRec1 (x1_next p) := by
    funext p
    by_cases hp : p = posM
    · subst hp; rw [Function.update_self, hx1_eq, Function.update_self, C.padRec1_update_b1]
      dsimp only [x1_next]; rw [Function.update_self]
    · rw [Function.update_of_ne hp]; dsimp only [x1_next]; rw [Function.update_of_ne hp]
  rw [hup_arr]
  exact act_adj_ket_of_act_ket _ hf_bwd

lemma act_fillMode1C (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Tr : Qubits C.T) :
    let ys1 : Fin C.M → Qubits C.w_a := fun pos =>
      let d := C.decodeRec1 (C.xs1 α pos)
      if pos.1 < C.m + C.N ∧ d.1 = C.m then natToBitsLSB C.w_a (modeOf54 (C.extBeta α) d.2.2) else fun _ => false
    let x1_filled : Fin C.M → Qubits C.w_rec1 := fun pos =>
      Fin.append (recKey54 (C.xs1 α pos)) (ys1 pos)
    act C.fillMode1C.unitary
        (ket (C.packState A K L P (fun pos => C.padRec1 (C.xs1 α pos)) Tr)) =
      ket (C.packState A K L P (fun pos => C.padRec1 (x1_filled pos)) Tr) := by
  intro ys1 x1_filled
  let x1At : ℕ → Fin C.M → Qubits C.w_rec1 := fun t pos =>
    if pos.1 < t then x1_filled pos else C.xs1 α pos
  let zAt : (t : ℕ) → t ≤ C.m + C.N → Qubits C.total := fun t _ =>
    C.packState A K L P (fun pos => C.padRec1 (x1At t pos)) Tr
  have hrun := act_seqList_fin_ket C.fillMode1StepC zAt fun t ht => by
    let pos : Fin (C.m + C.N) := ⟨t, ht⟩
    let posM := C.posM_of_lt pos
    have hcur : x1At t posM = C.xs1 α posM := if_neg (by dsimp [posM, posM_of_lt, pos]; omega)
    have hstep := C.act_fillMode1StepC α hα A K L P (x1At t) Tr pos hcur
    have hnext : Function.update (x1At t) posM
        (C.packRec1 (natToBits C.w_v ((wtilde3_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde3_length]; exact pos.isLt)).2.2)
          (natToBits C.w_a ((wtilde3_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde3_length]; exact pos.isLt)).1)
          (if ((wtilde3_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde3_length]; exact pos.isLt)).1 = C.m then
            natToBitsLSB C.w_a (modeOf54 (C.extBeta α) ((wtilde3_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde3_length]; exact pos.isLt)).2.2)
           else fun _ => false)) = x1At (t + 1) := by
      funext p
      by_cases hp : p = posM
      · subst hp
        rw [Function.update_self]
        dsimp only [x1At]
        conv_rhs => rw [if_pos (by dsimp [posM, posM_of_lt, pos]; omega)]
        dsimp only [x1_filled, ys1]
        have hd_eq : C.decodeRec1 (C.xs1 α posM) =
            (wtilde3_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde3_length]; exact pos.isLt) :=
          C.decodeRec1_xs1_prefix hα pos.1 pos.isLt
        have hk_eq : C.packRec1 (natToBits C.w_v ((wtilde3_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde3_length]; exact pos.isLt)).2.2)
            (natToBits C.w_a ((wtilde3_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde3_length]; exact pos.isLt)).1) =
            fun b => Fin.append (recKey54 (C.xs1 α posM)) b := by
          funext b u
          refine Fin.addCases (fun ik => ?_) (fun ib => ?_) u
          · have hC : natToBits C.w_v (C.decodeRec1 (C.xs1 α posM)).2.2 = C.rec1C (C.xs1 α posM) :=
              natToBits_eq_bitsToNat_iff _
            have hA : natToBits C.w_a (C.decodeRec1 (C.xs1 α posM)).1 = C.rec1A (C.xs1 α posM) :=
              natToBits_eq_bitsToNat_iff _
            dsimp only [packRec1]
            rw [Fin.append_left, Fin.append_left, ← hd_eq, hC, hA]
            refine Fin.addCases (fun ic => ?_) (fun ia => ?_) ik
            · simp [recKey54, rec1C]
            · simp [recKey54, rec1A]
          · simp [packRec1]
        have hmN : posM.1 < C.m + C.N := pos.isLt
        rw [hk_eq]
        simp only [hd_eq, hmN, true_and]
      · rw [Function.update_of_ne hp]
        have hiff : p.1 < t ↔ p.1 < t + 1 := by
          have := Fin.val_ne_of_ne hp; dsimp [posM, posM_of_lt, pos] at this; omega
        simp [x1At, hiff]
    dsimp only [zAt]
    rw [hstep, hnext]
  have hz0 : zAt 0 (Nat.zero_le _) = C.packState A K L P (fun pos => C.padRec1 (C.xs1 α pos)) Tr := by
    dsimp only [zAt, x1At]; rfl
  have hzN : zAt (C.m + C.N) le_rfl = C.packState A K L P (fun pos => C.padRec1 (x1_filled pos)) Tr := by
    dsimp only [zAt, x1At]; congr 1; funext pos
    by_cases hp : pos.1 < C.m + C.N
    · rw [if_pos hp]
    · rw [if_neg hp]
      have hrec : C.xs1 α pos = Fin.append (recKey54 (C.xs1 α pos)) (C.rec1B (C.xs1 α pos)) := by
        conv_lhs => rw [← C.packRec1_rec (C.xs1 α pos)]
        funext u; refine Fin.addCases (fun ik => ?_) (fun ib => ?_) u
        · refine Fin.addCases (fun ic => ?_) (fun ia => ?_) ik <;> simp [packRec1, recKey54, rec1C, rec1A]
        · simp [packRec1]
      have hy : ys1 pos = fun _ => false := by dsimp only [ys1]; rw [if_neg (by omega)]
      dsimp only [x1_filled]; rw [hy, ← (C.xs1_mem_props hα pos).1]
      conv_lhs => rw [hrec]
  rw [hz0, hzN] at hrun
  exact hrun

/-! #### 1.6 Pass-1 Unroute (`sort1C.adj`), Copy Modes `L`, & Uncompute `b1` -/

lemma act_sort1C_adj (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) :
    let ys1 : Fin C.M → Qubits C.w_a := fun pos =>
      let d := C.decodeRec1 (C.xs1 α pos)
      if pos.1 < C.m + C.N ∧ d.1 = C.m then natToBitsLSB C.w_a (modeOf54 (C.extBeta α) d.2.2) else fun _ => false
    let x1_filled : Fin C.M → Qubits C.w_rec1 := fun pos =>
      Fin.append (recKey54 (C.xs1 α pos)) (ys1 pos)
    let x1_unrouted : Fin C.M → Qubits C.w_rec1 := fun pos =>
      if _h : C.m ≤ pos.1 ∧ pos.1 < C.m + C.N then
        Fin.append (recKey54 (C.w2RecAt (C.extBeta α) pos)) (natToBitsLSB C.w_a (modeOf54 (C.extBeta α) (pos.1 - C.m)))
      else C.w2RecAt (C.extBeta α) pos
    act C.sort1C.adj.unitary
        (ket (C.packStage A K L P (fun pos => C.padRec1 (x1_filled pos)) (C.trs1 α) (fun _ => false))) =
      ket (C.packState A K L P (fun pos => C.padRec1 (x1_unrouted pos)) (fun _ => false)) := by
  intro ys1 x1_filled x1_unrouted
  let k_in : Fin C.M → Qubits C.w_k1 := recKey54 ∘ C.w2RecAt (C.extBeta α)
  have hsort_k : sort bitsToNat C.d true k_in = recKey54 ∘ C.xs1 α := by
    exact (C.R.sort_of_key_comp bitsToNat (recKey54 : Qubits C.w_rec1 → Qubits C.w_k1)
      C.d true (C.w2RecAt (C.extBeta α))).symm
  have htr_k : sortTrace bitsToNat C.d true k_in = C.trs1 α :=
    (C.R.sortTrace_of_key_comp bitsToNat (recKey54 : Qubits C.w_rec1 → Qubits C.w_k1)
      C.d true (C.w2RecAt (C.extBeta α))).symm
  dsimp only [sort1C]
  rw [C.act_sortKeyC_adj C.w_k1 C.w_p1 C.arr1AllEmb (C.scrEmb 0 C.w_k1 C.offScr_sort1)
      C.hAT_arr1 C.hAA_sort1 C.hTA_sort1 _ k_in ys1]
  · rw [C.padRec1_update_arr1_tr]
    have hy_out : unrouteSort C.d (sortTrace bitsToNat C.d true k_in) ys1 =
        fun pos => if C.m ≤ pos.1 ∧ pos.1 < C.m + C.N then
          natToBitsLSB C.w_a (modeOf54 (C.extBeta α) (pos.1 - C.m)) else fun _ => false := by
      let R1 : Qubits C.w_k1 → Qubits C.w_a → Prop := fun k b =>
        let c := bitsToNat (fun u : Fin C.w_v => k (Fin.castAdd C.w_a u))
        let a := bitsToNat (fun u : Fin C.w_a => k (Fin.natAdd C.w_v u))
        if a = C.m ∧ c < C.N then b = natToBitsLSB C.w_a (modeOf54 (C.extBeta α) c) else b = fun _ => false
      have hpre : ∀ pos : Fin C.M, R1 (sort bitsToNat C.d true k_in pos) (ys1 pos) := by
        intro pos
        have hk_eq : sort bitsToNat C.d true k_in pos = recKey54 (C.xs1 α pos) := congrFun hsort_k pos
        rw [hk_eq]
        have hc_eq : bitsToNat (fun u : Fin C.w_v => recKey54 (C.xs1 α pos) (Fin.castAdd C.w_a u)) =
            (C.decodeRec1 (C.xs1 α pos)).2.2 := rfl
        have ha_eq : bitsToNat (fun u : Fin C.w_a => recKey54 (C.xs1 α pos) (Fin.natAdd C.w_v u)) =
            (C.decodeRec1 (C.xs1 α pos)).1 := rfl
        dsimp only [R1]; rw [hc_eq, ha_eq]
        by_cases hp : pos.1 < C.m + C.N
        · have hd := C.decodeRec1_xs1_prefix hα pos.1 hp
          by_cases htm : (C.decodeRec1 (C.xs1 α pos)).1 = C.m
          · have hwspec := (C.O.wtilde3_pos_spec (C.extBeta α) (C.extBeta_sum hα) pos.1
              (by rw [C.O.wtilde3_length]; exact hp)).1 (by rw [← hd]; exact htm)
            have hc_lt : (C.decodeRec1 (C.xs1 α pos)).2.2 < C.N := by rw [hd]; exact hwspec.1
            rw [if_pos ⟨htm, hc_lt⟩]; dsimp only [ys1]; rw [if_pos ⟨hp, htm⟩]
          · rw [if_neg (fun h => htm h.1)]; dsimp only [ys1]; rw [if_neg (fun h => htm h.2)]
        · have hc_suf := C.xs1_suffix_c_eq hα pos (by omega)
          rw [if_neg (fun h => by omega)]; dsimp only [ys1]; rw [if_neg (fun h => hp h.1)]
      have hpost := C.R.unrouteSort_rel_sort bitsToNat C.d true k_in ys1 R1 hpre
      funext pos
      have hp := hpost pos
      dsimp only [R1, k_in, Function.comp_apply] at hp
      have hdec := C.decodeRec1_w2RecAt hα pos
      have hc_eq : bitsToNat (fun u : Fin C.w_v => recKey54 (C.w2RecAt (C.extBeta α) pos) (Fin.castAdd C.w_a u)) =
          (C.liftW2 (C.extBeta α) pos).2.2 := by rw [← hdec]; rfl
      have ha_eq : bitsToNat (fun u : Fin C.w_a => recKey54 (C.w2RecAt (C.extBeta α) pos) (Fin.natAdd C.w_v u)) =
          (C.liftW2 (C.extBeta α) pos).1 := by rw [← hdec]; rfl
      rw [hc_eq, ha_eq] at hp
      by_cases hmN : C.m ≤ pos.1 ∧ pos.1 < C.m + C.N
      · rw [if_pos hmN]
        have hl : C.liftW2 (C.extBeta α) pos = (C.m, 0, pos.1 - C.m) := by
          dsimp only [liftW2]; rw [dif_pos hmN.2, C.wtilde2_elem_spec _ pos.1 hmN.2,
            dif_neg (by dsimp only [m] at hmN; omega), dif_neg (by dsimp only [m] at hmN; omega)]
        rw [if_pos ⟨by rw [hl], by rw [hl]; dsimp only; omega⟩, hl] at hp
        exact hp
      · rw [if_neg hmN]
        have hnot_cond : ¬ ((C.liftW2 (C.extBeta α) pos).1 = C.m ∧ (C.liftW2 (C.extBeta α) pos).2.2 < C.N) := by
          dsimp only [liftW2]
          by_cases hlt : pos.1 < C.m + C.N
          · rw [dif_pos hlt, C.wtilde2_elem_spec _ pos.1 hlt]
            by_cases h1 : pos.1 < C.n
            · rw [dif_pos h1]; dsimp only; dsimp only [m]; omega
            · rw [dif_neg h1]
              have h2 : pos.1 = C.n := by dsimp only [m] at hmN hlt; omega
              rw [dif_pos h2]; dsimp only; dsimp only [m]; omega
          · rw [dif_neg hlt]; dsimp only; omega
        rw [if_neg hnot_cond] at hp
        exact hp
    rw [hy_out]
    dsimp only [packState]
    congr 2; funext pos; congr 1
    by_cases hmN : C.m ≤ pos.1 ∧ pos.1 < C.m + C.N
    · simp only [x1_unrouted, dif_pos hmN, if_pos hmN, k_in, Function.comp_apply]
    · simp only [x1_unrouted, dif_neg hmN, if_neg hmN]
      rw [← C.packRec1_rec (C.w2RecAt (C.extBeta α) pos)]
      have hb0 : C.rec1B (C.w2RecAt (C.extBeta α) pos) = fun _ => false := by
        dsimp only [w2RecAt, encodeRec1]; exact C.rec1B_packRec1 _ _ _
      rw [hb0]
      funext u; refine Fin.addCases (fun ik => ?_) (fun ib => ?_) u
      · refine Fin.addCases (fun ic => ?_) (fun ia => ?_) ik <;>
          simp [packRec1, k_in, recKey54, rec1C, rec1A]
      · simp [packRec1]
  · rw [C.packStage_arr1AllEmb]; congr 1; funext i; exact congrArg (fun k => Fin.append k (ys1 i)) (congrFun hsort_k i).symm
  · funext i; dsimp only [Function.comp_apply]; rw [C.packStage_trEmb, htr_k]
  · funext u; simp

abbrev partPosM (r : Fin C.N) : Fin C.M :=
  ⟨C.m + r.1, lt_of_lt_of_le (by have := r.isLt; omega) C.m_add_N_le_M⟩

lemma hdisj_b1Low_lSlot (r : Fin C.N) :
    ∀ a b, C.b1LowEmbLSB (C.partPosM r) a ≠ C.lSlotEmbLSB r b :=
  C.emb_disj_of_bounds _ _ C.offArr C.offTr C.offL C.offP
    (C.slotSlice_in_arr (C.partPosM r) (C.w_v + C.w_a) C.s C.hoff_b1_low)
    (fun b => by rw [lSlotEmbLSB, revEmb_apply]; exact C.lSlotEmb_bounds r b.rev)
    (Or.inr (by dsimp [offArr, offP]; omega))

lemma hdisj_lSlot_b1Low (r : Fin C.N) :
    ∀ a b, C.lSlotEmbLSB r a ≠ C.b1LowEmbLSB (C.partPosM r) b :=
  C.emb_disj_symm (C.hdisj_b1Low_lSlot r)

noncomputable def copyL1C : LayeredCircuit C.total :=
  LayeredCircuit.seqList (List.ofFn fun r : Fin C.N =>
    C.copyRegC C.s (C.b1LowEmbLSB (C.partPosM r)) (C.lSlotEmbLSB r) (C.hdisj_b1Low_lSlot r))

lemma copyL1C_size : C.copyL1C.size ≤ C.N * C.s :=
  seqList_ofFn_size_le _ C.s fun _ => le_of_eq (C.copyRegC_size _ _ _ _)

lemma act_copyL1C (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (P : Fin C.n → Qubits C.w_v) :
    let x1_unrouted : Fin C.M → Qubits C.w_rec1 := fun pos =>
      if _h : C.m ≤ pos.1 ∧ pos.1 < C.m + C.N then
        Fin.append (recKey54 (C.w2RecAt (C.extBeta α) pos)) (natToBitsLSB C.w_a (modeOf54 (C.extBeta α) (pos.1 - C.m)))
      else C.w2RecAt (C.extBeta α) pos
    let L_bits : Fin C.N → Qubits C.s := fun r => natToBits C.s (modeOf54 (C.extBeta α) r.1)
    act C.copyL1C.unitary (ket (C.packState A K (fun _ _ => false) P (fun pos => C.padRec1 (x1_unrouted pos)) (fun _ => false))) =
      ket (C.packState A K L_bits P (fun pos => C.padRec1 (x1_unrouted pos)) (fun _ => false)) := by
  intro x1_unrouted L_bits
  let zAt : (t : ℕ) → t ≤ C.N → Qubits C.total := fun t _ =>
    C.packState A K (fun r => if r.1 < t then L_bits r else fun _ => false) P
      (fun pos => C.padRec1 (x1_unrouted pos)) (fun _ => false)
  have hrun := act_seqList_fin_ket (fun r : Fin C.N =>
      C.copyRegC C.s (C.b1LowEmbLSB (C.partPosM r)) (C.lSlotEmbLSB r) (C.hdisj_b1Low_lSlot r)) zAt fun t ht => by
    let r : Fin C.N := ⟨t, ht⟩
    rw [C.act_copyRegC]
    have hmode_lt_m : modeOf54 (C.extBeta α) r.1 < C.m := C.O.modeOf_lt (C.extBeta α) (C.extBeta_sum hα) r.isLt
    have hmode_lt_s : modeOf54 (C.extBeta α) r.1 < 2 ^ C.s := by
      have := C.n_lt_two_pow_s; dsimp only [m] at hmode_lt_m; omega
    have hb_read : (fun u : Fin C.s => xor ((zAt t (le_of_lt ht)) (C.lSlotEmbLSB r u))
        ((zAt t (le_of_lt ht)) (C.b1LowEmbLSB (C.partPosM r) u))) = natToBitsLSB C.s (modeOf54 (C.extBeta α) r.1) := by
      funext u
      have hL0 : zAt t (le_of_lt ht) (C.lSlotEmbLSB r u) = false := by
        simp only [zAt, packState, lSlotEmbLSB, revEmb_apply, packStage_lSlotEmb]
        rw [if_neg (by dsimp [r]; omega)]
      have hb_val : zAt t (le_of_lt ht) (C.b1LowEmbLSB (C.partPosM r) u) =
          natToBitsLSB C.s (modeOf54 (C.extBeta α) r.1) u := by
        simp only [zAt, packState, b1LowEmbLSB, C.packStage_eval_slotSliceEmb]
        have hmN : C.m ≤ (C.partPosM r).1 ∧ (C.partPosM r).1 < C.m + C.N := by
          dsimp only [partPosM]; exact ⟨by omega, by have := r.isLt; omega⟩
        dsimp only [x1_unrouted]
        rw [dif_pos hmN]
        have hseg : (segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low u).1 < C.w_rec1 := by
          simp only [segEmb_val]; dsimp only [w_rec1, w_k1, w_p1, w_a]; have := u.isLt; omega
        dsimp only [padRec1]; rw [dif_pos hseg]
        have hnat : (⟨(segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low u).1, hseg⟩ : Fin (C.w_k1 + C.w_p1)) =
            Fin.natAdd C.w_k1 ⟨u.1, by dsimp only [w_p1, w_a]; exact lt_trans u.isLt (Nat.lt_succ_self C.s)⟩ := by
          apply Fin.ext; simp only [segEmb_val, Fin.val_natAdd]
        rw [hnat, Fin.append_right]
        simp only [Nat.add_sub_cancel_left]
        rfl
      rw [hL0, Bool.false_xor, hb_val]
    rw [hb_read]
    dsimp only [zAt, packState]
    rw [C.packStage_update_lSlotEmbLSB]
    congr 2; funext j
    by_cases hj : j = r
    · subst hj; rw [Function.update_self, if_pos (by dsimp [r]; omega), natToBitsLSB_comp_rev C.O hmode_lt_s]
    · rw [Function.update_of_ne hj]
      have hiff : j.1 < t ↔ j.1 < t + 1 := by
        have := Fin.val_ne_of_ne hj; dsimp [r] at this; omega
      simp [hiff]
  have hz0 : zAt 0 (Nat.zero_le _) = C.packState A K (fun _ _ => false) P (fun pos => C.padRec1 (x1_unrouted pos)) (fun _ => false) := by
    dsimp only [zAt]; rfl
  have hzN : zAt C.N le_rfl = C.packState A K L_bits P (fun pos => C.padRec1 (x1_unrouted pos)) (fun _ => false) := by
    dsimp only [zAt]; congr 1; funext r; rw [if_pos r.isLt]
  rw [hz0, hzN] at hrun
  exact hrun

noncomputable def unxorB1C : LayeredCircuit C.total :=
  LayeredCircuit.seqList (List.ofFn fun r : Fin C.N =>
    C.copyRegC C.s (C.lSlotEmbLSB r) (C.b1LowEmbLSB (C.partPosM r)) (C.hdisj_lSlot_b1Low r))

lemma unxorB1C_size : C.unxorB1C.size ≤ C.N * C.s :=
  seqList_ofFn_size_le _ C.s fun _ => le_of_eq (C.copyRegC_size _ _ _ _)

lemma act_unxorB1C (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (P : Fin C.n → Qubits C.w_v) :
    let x1_unrouted : Fin C.M → Qubits C.w_rec1 := fun pos =>
      if _h : C.m ≤ pos.1 ∧ pos.1 < C.m + C.N then
        Fin.append (recKey54 (C.w2RecAt (C.extBeta α) pos)) (natToBitsLSB C.w_a (modeOf54 (C.extBeta α) (pos.1 - C.m)))
      else C.w2RecAt (C.extBeta α) pos
    let L_bits : Fin C.N → Qubits C.s := fun r => natToBits C.s (modeOf54 (C.extBeta α) r.1)
    act C.unxorB1C.unitary (ket (C.packState A K L_bits P (fun pos => C.padRec1 (x1_unrouted pos)) (fun _ => false))) =
      ket (C.packState A K L_bits P (fun pos => C.padRec1 (C.w2RecAt (C.extBeta α) pos)) (fun _ => false)) := by
  intro x1_unrouted L_bits
  let x1At : ℕ → Fin C.M → Qubits C.w_rec1 := fun t pos =>
    if hmN : C.m ≤ pos.1 ∧ pos.1 < C.m + C.N then
      if pos.1 - C.m < t then C.w2RecAt (C.extBeta α) pos else x1_unrouted pos
    else C.w2RecAt (C.extBeta α) pos
  let zAt : (t : ℕ) → t ≤ C.N → Qubits C.total := fun t _ =>
    C.packState A K L_bits P (fun pos => C.padRec1 (x1At t pos)) (fun _ => false)
  have hrun := act_seqList_fin_ket (fun r : Fin C.N =>
      C.copyRegC C.s (C.lSlotEmbLSB r) (C.b1LowEmbLSB (C.partPosM r)) (C.hdisj_lSlot_b1Low r)) zAt fun t ht => by
    let r : Fin C.N := ⟨t, ht⟩
    let posM := C.partPosM r
    have hmode_lt_m : modeOf54 (C.extBeta α) r.1 < C.m := C.O.modeOf_lt (C.extBeta α) (C.extBeta_sum hα) r.isLt
    have hmode_lt_s : modeOf54 (C.extBeta α) r.1 < 2 ^ C.s := by
      have := C.n_lt_two_pow_s; dsimp only [m] at hmode_lt_m; omega
    have hmN : C.m ≤ posM.1 ∧ posM.1 < C.m + C.N := by
      dsimp only [posM, partPosM]; exact ⟨by omega, by have := r.isLt; omega⟩
    rw [C.act_copyRegC]
    have hzero : (fun u : Fin C.s => xor ((zAt t (le_of_lt ht)) (C.b1LowEmbLSB posM u))
        ((zAt t (le_of_lt ht)) (C.lSlotEmbLSB r u))) = fun _ => false := by
      funext u
      have hL_val : zAt t (le_of_lt ht) (C.lSlotEmbLSB r u) = natToBitsLSB C.s (modeOf54 (C.extBeta α) r.1) u := by
        simp only [zAt, packState, lSlotEmbLSB, revEmb_apply, packStage_lSlotEmb]
        dsimp only [L_bits]; rw [C.O.natToBits_apply hmode_lt_s u.rev]; simp
      have hb_val : zAt t (le_of_lt ht) (C.b1LowEmbLSB posM u) = natToBitsLSB C.s (modeOf54 (C.extBeta α) r.1) u := by
        simp only [zAt, packState, b1LowEmbLSB, C.packStage_eval_slotSliceEmb]
        dsimp only [x1At]
        rw [dif_pos hmN, if_neg (by dsimp [posM, partPosM, r]; omega)]
        dsimp only [x1_unrouted]; rw [dif_pos hmN]
        have hseg : (segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low u).1 < C.w_rec1 := by
          simp only [segEmb_val]; dsimp only [w_rec1, w_k1, w_p1, w_a]; have := u.isLt; omega
        dsimp only [padRec1]; rw [dif_pos hseg]
        have hnat : (⟨(segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low u).1, hseg⟩ : Fin (C.w_k1 + C.w_p1)) =
            Fin.natAdd C.w_k1 ⟨u.1, by dsimp only [w_p1, w_a]; exact lt_trans u.isLt (Nat.lt_succ_self C.s)⟩ := by
          apply Fin.ext; simp only [segEmb_val, Fin.val_natAdd]
        rw [hnat, Fin.append_right]
        simp only [posM, Nat.add_sub_cancel_left]; rfl
      rw [hb_val, hL_val, Bool.xor_self]
    rw [hzero]
    change ket (updateOn (slotSliceEmb C.offArr C.w_rec C.M (C.w_v + C.w_a) C.s C.total C.hoff_b1_low C.offArr_le posM)
        (C.packStage A K L_bits P _ _ _) (fun _ => false)) = _
    rw [C.packStage_update_slotSliceEmb]
    congr 2
    funext pos
    by_cases hp : pos = posM
    · subst hp
      rw [Function.update_self]
      dsimp only [x1At]
      rw [dif_pos hmN, if_neg (by dsimp [posM, partPosM, r]; omega),
        dif_pos hmN, if_pos (by dsimp [posM, partPosM, r]; omega)]
      funext u
      by_cases hu1 : u.1 < C.w_rec1
      · by_cases hge : C.w_v + C.w_a ≤ u.1
        · have hu_s : u.1 - (C.w_v + C.w_a) < C.w_a := by dsimp only [w_rec1, w_k1, w_p1] at hu1; omega
          by_cases hlow : u.1 - (C.w_v + C.w_a) < C.s
          · have he : u = segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low ⟨u.1 - (C.w_v + C.w_a), hlow⟩ :=
              Fin.ext (by simp [segEmb_val]; omega)
            rw [he, updateOn_apply_emb]
            have hseg_lt : (segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low ⟨u.1 - (C.w_v + C.w_a), hlow⟩).1 < C.w_rec1 := by
              simp only [segEmb_val]; dsimp only [w_rec1, w_k1, w_p1, w_a] at *; omega
            dsimp only [padRec1, w2RecAt, encodeRec1, packRec1]
            rw [dif_pos hseg_lt]
            have hb : (⟨(segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low ⟨u.1 - (C.w_v + C.w_a), hlow⟩).1, hseg_lt⟩ :
                Fin (C.w_k1 + C.w_p1)) = Fin.natAdd C.w_k1 ⟨u.1 - (C.w_v + C.w_a), hu_s⟩ :=
              Fin.ext (by simp only [segEmb_val, Fin.val_natAdd])
            rw [hb, Fin.append_right]
          · have hnot : u ∉ Set.range (segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low) := by
              rintro ⟨v, rfl⟩; simp [segEmb_val] at hlow
            rw [updateOn_apply_not_mem _ _ _ hnot]
            dsimp only [padRec1]
            rw [dif_pos hu1, dif_pos hu1]
            dsimp only [x1_unrouted]; rw [dif_pos hmN]
            have htop : u.1 - (C.w_v + C.w_a) = C.s := by dsimp only [w_rec1, w_k1, w_p1, w_a] at hu1 hlow ⊢; omega
            have hb1 : (⟨u.1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) = Fin.natAdd C.w_k1 ⟨C.s, Nat.lt_succ_self C.s⟩ :=
              Fin.ext (by simp only [Fin.val_natAdd]; dsimp only [w_k1]; omega)
            rw [hb1, Fin.append_right]
            have hhigh_false : natToBitsLSB C.w_a (modeOf54 (C.extBeta α) (posM.1 - C.m)) ⟨C.s, Nat.lt_succ_self C.s⟩ = false := by
              dsimp only [natToBitsLSB]
              exact Nat.testBit_lt_two_pow (by simpa [posM, partPosM] using hmode_lt_s)
            rw [hhigh_false]
            dsimp only [w2RecAt, encodeRec1, packRec1]
            rw [Fin.append_right]
        · have hnot : u ∉ Set.range (segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low) := by
            rintro ⟨v, rfl⟩; simp [segEmb_val] at hge
          rw [updateOn_apply_not_mem _ _ _ hnot]
          dsimp only [padRec1]
          rw [dif_pos hu1, dif_pos hu1]
          dsimp only [x1_unrouted]; rw [dif_pos hmN]
          have hk : (⟨u.1, hu1⟩ : Fin (C.w_k1 + C.w_p1)) = Fin.castAdd C.w_p1 ⟨u.1, by dsimp only [w_k1]; omega⟩ := rfl
          rw [hk, Fin.append_left]; rfl
      · have hnot : u ∉ Set.range (segEmb (C.w_v + C.w_a) C.s C.w_rec C.hoff_b1_low) := by
          rintro ⟨v, rfl⟩; apply hu1; simp only [segEmb_val]; dsimp only [w_rec1, w_k1, w_p1, w_a]; have := v.isLt; omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        dsimp only [padRec1]; rw [dif_neg hu1, dif_neg hu1]
    · rw [Function.update_of_ne hp]
      dsimp only [x1At]
      by_cases hmNp : C.m ≤ pos.1 ∧ pos.1 < C.m + C.N
      · have hiff : pos.1 - C.m < t ↔ pos.1 - C.m < t + 1 := by
          have := Fin.val_ne_of_ne hp; dsimp [posM, partPosM, r] at this; omega
        rw [dif_pos hmNp, dif_pos hmNp]; simp [hiff]
      · rw [dif_neg hmNp, dif_neg hmNp]
  have hz0 : zAt 0 (Nat.zero_le _) = C.packState A K L_bits P (fun pos => C.padRec1 (x1_unrouted pos)) (fun _ => false) := by
    dsimp only [zAt, x1At]; congr 1; funext pos
    by_cases hmN : C.m ≤ pos.1 ∧ pos.1 < C.m + C.N
    · rw [dif_pos hmN, if_neg (by omega)]
    · dsimp only [x1_unrouted]; rw [dif_neg hmN, dif_neg hmN]
  have hzN : zAt C.N le_rfl = C.packState A K L_bits P (fun pos => C.padRec1 (C.w2RecAt (C.extBeta α) pos)) (fun _ => false) := by
    dsimp only [zAt, x1At]; congr 1; funext pos
    by_cases hmN : C.m ≤ pos.1 ∧ pos.1 < C.m + C.N
    · rw [dif_pos hmN, if_pos (by omega)]
    · rw [dif_neg hmN]
  rw [hz0, hzN] at hrun
  exact hrun

/-! #### 1.7 Full Pass-1 Circuit `pass1C` -/

noncomputable def pass1C : LayeredCircuit C.total :=
  let pref := C.prefixPC.seq C.initArr1C
  pref.seq (C.copyKC.seq (C.sort1C.seq (C.fillMode1C.seq (C.sort1C.adj.seq (C.copyL1C.seq (C.unxorB1C.seq pref.adj))))))

lemma pass1C_size :
    (C.pass1C.size : ℝ) ≤
      2 * C.n * (15 * C.w_v) + 2 * C.M * (C.w_a + C.w_v) + C.w_v + 2 * C.N * C.s +
        (C.m + C.N) * (33 * C.w_a + 30 * C.w_pos + 2 * C.w_v + 24) +
        2 * (C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k1 + C.w_p1 + 1 : ℝ)) := by
  dsimp only [pass1C]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have h1 : (C.prefixPC.size : ℝ) ≤ C.n * (15 * C.w_v) := by exact_mod_cast C.prefixPC_size
  have h2 : (C.initArr1C.size : ℝ) ≤ C.M * (C.w_a + C.w_v) := by exact_mod_cast C.initArr1C_size
  have h3 : (C.copyKC.size : ℝ) = C.w_v := by exact_mod_cast C.copyKC_size
  have h4 := C.sort1C_size
  have h5 : (C.fillMode1C.size : ℝ) ≤ (C.m + C.N) * (33 * C.w_a + 30 * C.w_pos + 2 * C.w_v + 24) := by
    exact_mod_cast C.fillMode1C_size
  have h6 : (C.copyL1C.size : ℝ) ≤ C.N * C.s := by exact_mod_cast C.copyL1C_size
  have h7 : (C.unxorB1C.size : ℝ) ≤ C.N * C.s := by exact_mod_cast C.unxorB1C_size
  push_cast at *
  linarith

lemma act_pass1C (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N) :
    let A_bits := fun i : Fin C.n => natToBitsLSB C.w_v (α i)
    let K_bits := natToBitsLSB C.w_v (∑ i : Fin C.n, α i)
    let L_bits := fun r : Fin C.N => natToBits C.s (modeOf54 (C.extBeta α) r.1)
    act C.pass1C.unitary
        (ket (C.packState A_bits (fun _ => false) (fun _ _ => false) (fun _ _ => false) (fun _ _ => false) (fun _ => false))) =
      ket (C.packState A_bits K_bits L_bits (fun _ _ => false) (fun _ _ => false) (fun _ => false)) := by
  intro A_bits K_bits L_bits
  let P_bits := fun i : Fin C.n => natToBitsLSB C.w_v (prefSum54 α i)
  let Arr1 := fun pos : Fin C.M => C.padRec1 (C.w2RecAt (C.extBeta α) pos)
  have hpref_bwd : act (C.prefixPC.seq C.initArr1C).adj.unitary
      (ket (C.packState A_bits K_bits L_bits P_bits Arr1 (fun _ => false))) =
      ket (C.packState A_bits K_bits L_bits (fun _ _ => false) (fun _ _ => false) (fun _ => false)) :=
    act_adj_ket_of_act_ket _ (by
      rw [LayeredCircuit.seq_unitary, act_mul, C.act_prefixPC α hα, C.act_initArr1C α hα])
  dsimp only [pass1C]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  rw [C.act_prefixPC α hα, C.act_initArr1C α hα, C.act_copyKC α, C.act_sort1C α, C.act_fillMode1C α hα,
    C.act_sort1C_adj α hα, C.act_copyL1C α hα, C.act_unxorB1C α hα, hpref_bwd]

end OccCtx

end QuantumLTF.Membership.Supplement.StageA


/-! ### Pass 2 (`initArr2C`, `sort2C`, `fillPref2C`, `sort2C.adj`, `uncomputeAC`, & `pass2Prefix.adj`) -/

namespace QuantumLTF.Membership.Supplement.StageA

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open Thm49Primitives Thm410Router Cslib.BitonicSort

namespace OccCtx

variable (C : OccCtx)

/-! #### 2.1 `packRec2` Sub-Register Lemmas & `natToBits` Helpers -/

lemma hoff_b2 : 0 + C.w_a ≤ C.w_rec := by dsimp [w_rec, w_k2, w_p2]; omega
lemma hoff_b2_low : 1 + C.s ≤ C.w_rec := by dsimp [w_rec, w_k2, w_p2, w_a]; omega
lemma hoff_f2 : C.w_a + 1 ≤ C.w_rec := by dsimp [w_rec, w_k2, w_p2]; omega
lemma hoff_ceff2 : (C.w_a + 1) + C.w_v ≤ C.w_rec := by dsimp [w_rec, w_k2, w_p2]; omega
lemma hoff_a2 : C.w_k2 + C.w_a ≤ C.w_rec := by dsimp [w_rec, w_p2]; omega
lemma hoff_c2 : (C.w_k2 + C.w_a) + C.w_v ≤ C.w_rec := by dsimp [w_rec, w_p2]; omega

abbrev b2LowEmbMSB (pos : Fin C.M) : Fin C.s ↪ Fin C.total :=
  slotSliceEmb C.offArr C.w_rec C.M 1 C.s C.total C.hoff_b2_low C.offArr_le pos

abbrev TEmb_wv : Fin C.w_v ↪ Fin C.total := C.scrEmb 1 C.w_v C.offScr_T_wv

lemma natToBits_w_a_zero {v : ℕ} (hv : v < 2 ^ C.s) :
    natToBits C.w_a v ⟨0, C.w_a_pos⟩ = false := by
  have hv_wa : v < 2 ^ C.w_a := lt_trans hv (Nat.pow_lt_pow_right (by norm_num) (by dsimp [w_a]; omega))
  rw [C.O.natToBits_apply hv_wa ⟨0, C.w_a_pos⟩]
  dsimp only [natToBitsLSB, Fin.rev]
  have hsub : C.w_a - (0 + 1) = C.s := rfl
  rw [hsub]
  exact Nat.testBit_lt_two_pow hv

lemma natToBits_w_a_succ {v : ℕ} (hv : v < 2 ^ C.s) (j : Fin C.s) :
    natToBits C.w_a v ⟨1 + j.1, by dsimp [w_a]; have := j.isLt; omega⟩ = natToBits C.s v j := by
  have hv_wa : v < 2 ^ C.w_a := lt_trans hv (Nat.pow_lt_pow_right (by norm_num) (by dsimp [w_a]; omega))
  rw [C.O.natToBits_apply hv_wa, C.O.natToBits_apply hv]
  dsimp only [natToBitsLSB, Fin.rev]
  have hsub : C.w_a - (1 + j.1 + 1) = C.s - (j.1 + 1) := by dsimp [w_a]; omega
  rw [hsub]

lemma packRec2_eval_b2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) (u : Fin C.w_a) :
    C.packRec2 b f ceff a c (segEmb 0 C.w_a C.w_rec C.hoff_b2 u) = b u := by
  have he : segEmb 0 C.w_a C.w_rec C.hoff_b2 u =
      Fin.castAdd C.w_p2 (Fin.castAdd C.w_v (Fin.castAdd 1 u)) := Fin.ext (by simp [segEmb_val])
  dsimp only [packRec2]
  rw [he, Fin.append_left, Fin.append_left, Fin.append_left]

lemma packRec2_eval_b2_low (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) (u : Fin C.s) :
    C.packRec2 b f ceff a c (segEmb 1 C.s C.w_rec C.hoff_b2_low u) =
      b ⟨1 + u.1, by dsimp [w_a]; have := u.isLt; omega⟩ := by
  have he : segEmb 1 C.s C.w_rec C.hoff_b2_low u =
      segEmb 0 C.w_a C.w_rec C.hoff_b2 ⟨1 + u.1, by dsimp [w_a]; have := u.isLt; omega⟩ :=
    Fin.ext (by simp [segEmb_val])
  rw [he]; exact C.packRec2_eval_b2 b f ceff a c _

lemma packRec2_eval_f2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) (u : Fin 1) :
    C.packRec2 b f ceff a c (segEmb C.w_a 1 C.w_rec C.hoff_f2 u) = f u := by
  have he : segEmb C.w_a 1 C.w_rec C.hoff_f2 u =
      Fin.castAdd C.w_p2 (Fin.castAdd C.w_v (Fin.natAdd C.w_a u)) := Fin.ext (by simp [segEmb_val])
  dsimp only [packRec2]
  rw [he, Fin.append_left, Fin.append_left, Fin.append_right]

lemma packRec2_eval_ceff2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) (u : Fin C.w_v) :
    C.packRec2 b f ceff a c (segEmb (C.w_a + 1) C.w_v C.w_rec C.hoff_ceff2 u) = ceff u := by
  have he : segEmb (C.w_a + 1) C.w_v C.w_rec C.hoff_ceff2 u =
      Fin.castAdd C.w_p2 (Fin.natAdd (C.w_a + 1) u) := Fin.ext (by simp [segEmb_val])
  dsimp only [packRec2]
  rw [he, Fin.append_left, Fin.append_right]

lemma packRec2_eval_a2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) (u : Fin C.w_a) :
    C.packRec2 b f ceff a c (segEmb C.w_k2 C.w_a C.w_rec C.hoff_a2 u) = a u := by
  have he : segEmb C.w_k2 C.w_a C.w_rec C.hoff_a2 u =
      Fin.natAdd C.w_k2 (Fin.castAdd C.w_v u) := Fin.ext (by simp [segEmb_val])
  dsimp only [packRec2]
  rw [he, Fin.append_right, Fin.append_left]

lemma packRec2_eval_c2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) (u : Fin C.w_v) :
    C.packRec2 b f ceff a c (segEmb (C.w_k2 + C.w_a) C.w_v C.w_rec C.hoff_c2 u) = c u := by
  have he : segEmb (C.w_k2 + C.w_a) C.w_v C.w_rec C.hoff_c2 u =
      Fin.natAdd C.w_k2 (Fin.natAdd C.w_a u) := Fin.ext (by simp [segEmb_val]; ring)
  dsimp only [packRec2]
  rw [he, Fin.append_right, Fin.append_right]

lemma packRec2_zero :
    (fun _ : Fin C.w_rec => false) =
      C.packRec2 (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) := by
  funext u
  refine Fin.addCases (fun ik => ?_) (fun ip => ?_) u
  · refine Fin.addCases (fun ibf => ?_) (fun ic => ?_) ik
    · refine Fin.addCases (fun ib => ?_) (fun if' => ?_) ibf <;> simp [packRec2]
    · simp [packRec2]
  · refine Fin.addCases (fun ia => ?_) (fun ic => ?_) ip <;> simp [packRec2]

lemma packRec2_update_b2 (b b' : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) :
    updateOn (segEmb 0 C.w_a C.w_rec C.hoff_b2) (C.packRec2 b f ceff a c) b' =
      C.packRec2 b' f ceff a c := by
  funext u
  refine Fin.addCases (fun ik => ?_) (fun ip => ?_) u
  · refine Fin.addCases (fun ibf => ?_) (fun ic => ?_) ik
    · refine Fin.addCases (fun ib => ?_) (fun if' => ?_) ibf
      · have he : Fin.castAdd C.w_p2 (Fin.castAdd C.w_v (Fin.castAdd 1 ib)) =
            segEmb 0 C.w_a C.w_rec C.hoff_b2 ib := Fin.ext (by simp [segEmb_val])
        rw [he, updateOn_apply_emb, C.packRec2_eval_b2]
      · have hnot : Fin.castAdd C.w_p2 (Fin.castAdd C.w_v (Fin.natAdd C.w_a if')) ∉
            Set.range (segEmb 0 C.w_a C.w_rec C.hoff_b2) := by
          rintro ⟨v, hv⟩; have := congrArg Fin.val hv; simp [segEmb_val] at this; have := v.isLt; omega
        rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]
    · have hnot : Fin.castAdd C.w_p2 (Fin.natAdd (C.w_a + 1) ic) ∉
          Set.range (segEmb 0 C.w_a C.w_rec C.hoff_b2) := by
        rintro ⟨v, hv⟩; have := congrArg Fin.val hv; simp [segEmb_val] at this; have := v.isLt; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]
  · have hnot : Fin.natAdd C.w_k2 ip ∉ Set.range (segEmb 0 C.w_a C.w_rec C.hoff_b2) := by
      rintro ⟨v, hv⟩; have := congrArg Fin.val hv; change 0 + v.1 = (C.w_a + 1 + C.w_v) + ip.1 at this
      have := v.isLt; omega
    rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]

lemma packRec2_update_b2_low (b : Qubits C.w_a) (g : Qubits C.s) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) :
    updateOn (segEmb 1 C.s C.w_rec C.hoff_b2_low) (C.packRec2 b f ceff a c) g =
      C.packRec2 (fun j : Fin C.w_a => if h : 1 ≤ j.1 then g ⟨j.1 - 1, by dsimp [w_a] at *; omega⟩ else b j) f ceff a c := by
  funext u
  by_cases hu : 1 ≤ u.1 ∧ u.1 < 1 + C.s
  · have he : u = segEmb 1 C.s C.w_rec C.hoff_b2_low ⟨u.1 - 1, by omega⟩ := Fin.ext (by simp [segEmb_val]; omega)
    rw [he, updateOn_apply_emb]
    have he2 : segEmb 1 C.s C.w_rec C.hoff_b2_low ⟨u.1 - 1, by omega⟩ =
        segEmb 0 C.w_a C.w_rec C.hoff_b2 ⟨u.1, by dsimp [w_a]; omega⟩ := Fin.ext (by simp [segEmb_val]; omega)
    rw [he2, C.packRec2_eval_b2]
    simp [hu.1]
  · have hnot : u ∉ Set.range (segEmb 1 C.s C.w_rec C.hoff_b2_low) := by
      rintro ⟨v, rfl⟩; exact hu (by simp [segEmb_val, v.isLt])
    rw [updateOn_apply_not_mem _ _ _ hnot]
    by_cases hu_a : u.1 < C.w_a
    · have he : u = segEmb 0 C.w_a C.w_rec C.hoff_b2 ⟨u.1, hu_a⟩ := Fin.ext (by simp [segEmb_val])
      rw [he, C.packRec2_eval_b2, C.packRec2_eval_b2]
      have h0 : ¬ 1 ≤ u.1 := by dsimp [w_a] at hu_a; omega
      simp [h0]
    · induction u using Fin.addCases with
      | left ik =>
        induction ik using Fin.addCases with
        | left ibf =>
          induction ibf using Fin.addCases with
          | left ib => exfalso; apply hu_a; simpa using ib.isLt
          | right _ => simp [packRec2]
        | right _ => simp [packRec2]
      | right _ => simp [packRec2]

lemma packRec2_update_f2 (b : Qubits C.w_a) (f f' : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) :
    updateOn (segEmb C.w_a 1 C.w_rec C.hoff_f2) (C.packRec2 b f ceff a c) f' =
      C.packRec2 b f' ceff a c := by
  funext u
  refine Fin.addCases (fun ik => ?_) (fun ip => ?_) u
  · refine Fin.addCases (fun ibf => ?_) (fun ic => ?_) ik
    · refine Fin.addCases (fun ib => ?_) (fun if' => ?_) ibf
      · have hnot : Fin.castAdd C.w_p2 (Fin.castAdd C.w_v (Fin.castAdd 1 ib)) ∉
            Set.range (segEmb C.w_a 1 C.w_rec C.hoff_f2) := by
          rintro ⟨v, hv⟩; have := congrArg Fin.val hv; simp [segEmb_val] at this; have := ib.isLt; omega
        rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]
      · have he : Fin.castAdd C.w_p2 (Fin.castAdd C.w_v (Fin.natAdd C.w_a if')) =
            segEmb C.w_a 1 C.w_rec C.hoff_f2 if' := Fin.ext (by simp [segEmb_val])
        rw [he, updateOn_apply_emb, C.packRec2_eval_f2]
    · have hnot : Fin.castAdd C.w_p2 (Fin.natAdd (C.w_a + 1) ic) ∉
          Set.range (segEmb C.w_a 1 C.w_rec C.hoff_f2) := by
        rintro ⟨v, hv⟩; have := congrArg Fin.val hv; simp [segEmb_val] at this; have := v.isLt; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]
  · have hnot : Fin.natAdd C.w_k2 ip ∉ Set.range (segEmb C.w_a 1 C.w_rec C.hoff_f2) := by
      rintro ⟨v, hv⟩; have := congrArg Fin.val hv; change C.w_a + v.1 = (C.w_a + 1 + C.w_v) + ip.1 at this
      have := v.isLt; omega
    rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]

lemma packRec2_update_ceff2 (b : Qubits C.w_a) (f : Qubits 1) (ceff ceff' : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) :
    updateOn (segEmb (C.w_a + 1) C.w_v C.w_rec C.hoff_ceff2) (C.packRec2 b f ceff a c) ceff' =
      C.packRec2 b f ceff' a c := by
  funext u
  refine Fin.addCases (fun ik => ?_) (fun ip => ?_) u
  · refine Fin.addCases (fun ibf => ?_) (fun ic => ?_) ik
    · have hnot : Fin.castAdd C.w_p2 (Fin.castAdd C.w_v ibf) ∉
          Set.range (segEmb (C.w_a + 1) C.w_v C.w_rec C.hoff_ceff2) := by
        rintro ⟨v, hv⟩; have := congrArg Fin.val hv; simp [segEmb_val] at this; have := ibf.isLt; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]
    · have he : Fin.castAdd C.w_p2 (Fin.natAdd (C.w_a + 1) ic) =
          segEmb (C.w_a + 1) C.w_v C.w_rec C.hoff_ceff2 ic := Fin.ext (by simp [segEmb_val])
      rw [he, updateOn_apply_emb, C.packRec2_eval_ceff2]
  · have hnot : Fin.natAdd C.w_k2 ip ∉ Set.range (segEmb (C.w_a + 1) C.w_v C.w_rec C.hoff_ceff2) := by
      rintro ⟨v, hv⟩; have := congrArg Fin.val hv; change (C.w_a + 1) + v.1 = (C.w_a + 1 + C.w_v) + ip.1 at this
      have := v.isLt; omega
    rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]

lemma packRec2_update_a2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a a' : Qubits C.w_a) (c : Qubits C.w_v) :
    updateOn (segEmb C.w_k2 C.w_a C.w_rec C.hoff_a2) (C.packRec2 b f ceff a c) a' =
      C.packRec2 b f ceff a' c := by
  funext u
  refine Fin.addCases (fun ik => ?_) (fun ip => ?_) u
  · have hnot : Fin.castAdd C.w_p2 ik ∉ Set.range (segEmb C.w_k2 C.w_a C.w_rec C.hoff_a2) := by
      rintro ⟨v, hv⟩; have := congrArg Fin.val hv; simp [segEmb_val] at this; have := ik.isLt; omega
    rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]
  · refine Fin.addCases (fun ia => ?_) (fun ic => ?_) ip
    · have he : Fin.natAdd C.w_k2 (Fin.castAdd C.w_v ia) =
          segEmb C.w_k2 C.w_a C.w_rec C.hoff_a2 ia := Fin.ext (by simp [segEmb_val])
      rw [he, updateOn_apply_emb, C.packRec2_eval_a2]
    · have hnot : Fin.natAdd C.w_k2 (Fin.natAdd C.w_a ic) ∉ Set.range (segEmb C.w_k2 C.w_a C.w_rec C.hoff_a2) := by
        rintro ⟨v, hv⟩; have := congrArg Fin.val hv; simp [segEmb_val] at this; have := v.isLt; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]

lemma packRec2_update_c2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c c' : Qubits C.w_v) :
    updateOn (segEmb (C.w_k2 + C.w_a) C.w_v C.w_rec C.hoff_c2) (C.packRec2 b f ceff a c) c' =
      C.packRec2 b f ceff a c' := by
  funext u
  refine Fin.addCases (fun ik => ?_) (fun ip => ?_) u
  · have hnot : Fin.castAdd C.w_p2 ik ∉ Set.range (segEmb (C.w_k2 + C.w_a) C.w_v C.w_rec C.hoff_c2) := by
      rintro ⟨v, hv⟩; have := congrArg Fin.val hv; simp [segEmb_val] at this; have := ik.isLt; omega
    rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]
  · refine Fin.addCases (fun ia => ?_) (fun ic => ?_) ip
    · have hnot : Fin.natAdd C.w_k2 (Fin.castAdd C.w_v ia) ∉ Set.range (segEmb (C.w_k2 + C.w_a) C.w_v C.w_rec C.hoff_c2) := by
        rintro ⟨v, hv⟩; have := congrArg Fin.val hv; simp [segEmb_val] at this; have := ia.isLt; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]; simp [packRec2]
    · have he : Fin.natAdd C.w_k2 (Fin.natAdd C.w_a ic) =
          segEmb (C.w_k2 + C.w_a) C.w_v C.w_rec C.hoff_c2 ic := Fin.ext (by simp [segEmb_val]; ring)
      rw [he, updateOn_apply_emb, C.packRec2_eval_c2]

/-! #### 2.2 Initialize Pass-2 Array `initArr2C` -/

lemma hdisj_lSlot_b2Low (r : Fin C.N) (pos : Fin C.M) :
    ∀ a b, C.lSlotEmb r a ≠ C.b2LowEmbMSB pos b :=
  C.emb_disj_of_bounds _ _ C.offL C.offP C.offArr C.offTr
    (C.lSlotEmb_bounds r) (C.slotSlice_in_arr pos 1 C.s C.hoff_b2_low)
    (Or.inl (by dsimp [offArr, offP]; omega))

noncomputable def initArr2StepC (pos : Fin C.M) : LayeredCircuit C.total :=
  if h1 : pos.1 < C.m then
    (C.setConstC C.w_a pos.1 (C.b2EmbLSB pos)).seq
      ((C.setConstC 1 1 (C.f2Emb pos)).seq
        (C.setConstC C.w_a pos.1 (C.a2EmbLSB pos)))
  else if h2 : pos.1 < C.m + C.N then
    let r : Fin C.N := ⟨pos.1 - C.m, by omega⟩
    (C.copyRegC C.s (C.lSlotEmb r) (C.b2LowEmbMSB pos) (C.hdisj_lSlot_b2Low r pos)).seq
      ((C.setConstC C.w_v (pos.1 - C.m) (C.ceff2EmbLSB pos)).seq
        (C.setConstC C.w_a C.m (C.a2EmbLSB pos)))
  else
    (C.setConstC C.w_a C.m (C.b2EmbLSB pos)).seq
      (C.setConstC C.w_a C.m (C.a2EmbLSB pos))

lemma initArr2StepC_size (pos : Fin C.M) :
    (C.initArr2StepC pos).size ≤ 2 * C.w_a + C.w_v + C.s + 1 := by
  dsimp only [initArr2StepC]
  split_ifs
  · simp only [LayeredCircuit.seq_size]
    have h1 := C.setConstC_size C.w_a pos.1 (C.b2EmbLSB pos)
    have h2 := C.setConstC_size 1 1 (C.f2Emb pos)
    have h3 := C.setConstC_size C.w_a pos.1 (C.a2EmbLSB pos)
    omega
  · simp only [LayeredCircuit.seq_size, C.copyRegC_size]
    have h1 := C.setConstC_size C.w_v (pos.1 - C.m) (C.ceff2EmbLSB pos)
    have h2 := C.setConstC_size C.w_a C.m (C.a2EmbLSB pos)
    omega
  · simp only [LayeredCircuit.seq_size]
    have h1 := C.setConstC_size C.w_a C.m (C.b2EmbLSB pos)
    have h2 := C.setConstC_size C.w_a C.m (C.a2EmbLSB pos)
    omega

noncomputable def initArr2C : LayeredCircuit C.total :=
  LayeredCircuit.seqList (List.ofFn C.initArr2StepC)

lemma initArr2C_size : C.initArr2C.size ≤ C.M * (2 * C.w_a + C.w_v + C.s + 1) :=
  seqList_ofFn_size_le C.initArr2StepC _ C.initArr2StepC_size

def w2fRecAt (β : Fin C.m → ℕ) (pos : Fin C.M) : Qubits C.w_rec :=
  if _h1 : pos.1 < C.m then
    C.packRec2 (natToBits C.w_a pos.1) (fun _ => true) (fun _ => false) (natToBitsLSB C.w_a pos.1) (fun _ => false)
  else if _h2 : pos.1 < C.m + C.N then
    C.packRec2 (natToBits C.w_a (modeOf54 β (pos.1 - C.m))) (fun _ => false)
      (natToBits C.w_v (pos.1 - C.m)) (natToBitsLSB C.w_a C.m) (fun _ => false)
  else
    C.packRec2 (natToBits C.w_a C.m) (fun _ => false) (fun _ => false) (natToBitsLSB C.w_a C.m) (fun _ => false)

lemma act_initArr2C (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v)
    (P : Fin C.n → Qubits C.w_v) (Tr : Qubits C.T) :
    let L_bits := fun r : Fin C.N => natToBits C.s (modeOf54 (C.extBeta α) r.1)
    act C.initArr2C.unitary (ket (C.packState A K L_bits P (fun _ _ => false) Tr)) =
      ket (C.packState A K L_bits P (C.w2fRecAt (C.extBeta α)) Tr) := by
  intro L_bits
  let zAt : (t : ℕ) → t ≤ C.M → Qubits C.total := fun t _ =>
    C.packState A K L_bits P (fun pos => if pos.1 < t then C.w2fRecAt (C.extBeta α) pos else fun _ => false) Tr
  have hrun := act_seqList_fin_ket C.initArr2StepC zAt fun t ht => by
    let cur : Fin C.M := ⟨t, ht⟩
    let Arr_t : Fin C.M → Qubits C.w_rec :=
      fun pos => if pos.1 < t then C.w2fRecAt (C.extBeta α) pos else fun _ => false
    have hcur0 : Arr_t cur = fun _ => false := if_neg (by dsimp [cur]; omega)
    dsimp only [initArr2StepC]
    by_cases h1 : cur.1 < C.m
    · rw [dif_pos h1, LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul]
      have ha_lt : cur.1 < 2 ^ C.w_a := lt_trans h1 C.m_lt_two_pow_w_a
      -- 1. b2EmbLSB := cur.1
      rw [C.act_setConstC]
      have hb_fn : setConstFn54 C.w_a cur.1 (zAt t (le_of_lt ht) ∘ C.b2EmbLSB cur) = natToBitsLSB C.w_a cur.1 := by
        funext u; simp only [setConstFn54, Function.comp_apply, zAt, packState, b2EmbLSB, b2EmbMSB]
        rw [C.packStage_eval_slotSliceEmb_rev, if_neg (by dsimp [cur]; omega)]; simp
      rw [hb_fn]
      dsimp only [zAt, packState]
      rw [show (fun pos : Fin C.M => if pos.1 < t then C.w2fRecAt (C.extBeta α) pos else fun _ => false) = Arr_t from rfl]
      rw [C.packStage_update_slotSliceEmb_rev, hcur0, C.packRec2_zero, natToBitsLSB_comp_rev C.O ha_lt, C.packRec2_update_b2]
      let Arr1 := Function.update Arr_t cur
        (C.packRec2 (natToBits C.w_a cur.1) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false))
      -- 2. f2Emb := 1
      rw [C.act_setConstC]
      have hf_fn : setConstFn54 1 1 ((C.packState A K L_bits P Arr1 Tr) ∘ C.f2Emb cur) = fun _ => true := by
        funext u; have hu0 : u = 0 := Subsingleton.elim u 0; subst hu0
        simp only [setConstFn54, Function.comp_apply, packState, Arr1, f2Emb, C.packStage_eval_slotSliceEmb,
          Function.update_self, C.packRec2_eval_f2]
        rfl
      rw [hf_fn]
      rw [C.packStage_update_slotSliceEmb, Function.update_self, Function.update_idem, C.packRec2_update_f2]
      let Arr2 := Function.update Arr_t cur
        (C.packRec2 (natToBits C.w_a cur.1) (fun _ => true) (fun _ => false) (fun _ => false) (fun _ => false))
      -- 3. a2EmbLSB := cur.1
      rw [C.act_setConstC]
      have ha_fn : setConstFn54 C.w_a cur.1 ((C.packState A K L_bits P Arr2 Tr) ∘ C.a2EmbLSB cur) = natToBitsLSB C.w_a cur.1 := by
        funext u
        simp only [setConstFn54, Function.comp_apply, packState, Arr2, a2EmbLSB, C.packStage_eval_slotSliceEmb,
          Function.update_self, C.packRec2_eval_a2, Bool.false_xor]
      rw [ha_fn]
      rw [C.packStage_update_slotSliceEmb, Function.update_self, Function.update_idem, C.packRec2_update_a2]
      congr 2; funext pos
      by_cases hp : pos = cur
      · subst hp; rw [Function.update_self, if_pos (by dsimp [cur]; omega)]; dsimp only [w2fRecAt]; rw [dif_pos h1]
      · rw [Function.update_of_ne hp]
        have hiff : pos.1 < t ↔ pos.1 < t + 1 := by
          have := Fin.val_ne_of_ne hp; dsimp [cur] at this; omega
        simp [Arr_t, hiff, ← C.packRec2_zero]
    · rw [dif_neg h1]
      by_cases h2 : cur.1 < C.m + C.N
      · rw [dif_pos h2, LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul]
        let r : Fin C.N := ⟨cur.1 - C.m, by omega⟩
        have hm_lt : modeOf54 (C.extBeta α) r.1 < C.m := C.O.modeOf_lt (C.extBeta α) (C.extBeta_sum hα) r.isLt
        have hs_lt : modeOf54 (C.extBeta α) r.1 < 2 ^ C.s := by
          have := C.n_lt_two_pow_s; dsimp only [m] at hm_lt; omega
        -- 1. b2LowEmbMSB := L[r]
        rw [C.act_copyRegC]
        have hL_val : (fun u : Fin C.s => xor ((zAt t (le_of_lt ht)) (C.b2LowEmbMSB cur u))
            ((zAt t (le_of_lt ht)) (C.lSlotEmb r u))) = L_bits r := by
          funext u
          simp only [zAt, packState, b2LowEmbMSB, C.packStage_eval_slotSliceEmb, packStage_lSlotEmb]
          rw [if_neg (by dsimp [cur]; omega), Bool.false_xor]
        rw [hL_val]
        dsimp only [zAt, packState]
        rw [show (fun pos : Fin C.M => if pos.1 < t then C.w2fRecAt (C.extBeta α) pos else fun _ => false) = Arr_t from rfl]
        rw [C.packStage_update_slotSliceEmb, hcur0, C.packRec2_zero, C.packRec2_update_b2_low]
        have hb_eq : (fun j : Fin C.w_a => if h : 1 ≤ j.1 then L_bits r ⟨j.1 - 1, by dsimp [w_a] at *; omega⟩ else false) =
            natToBits C.w_a (modeOf54 (C.extBeta α) r.1) := by
          funext j
          by_cases hj : 1 ≤ j.1
          · rw [dif_pos hj]; dsimp only [L_bits]
            have he : j = ⟨1 + (j.1 - 1), by have := j.isLt; dsimp [w_a] at this ⊢; omega⟩ := Fin.ext (by simp; omega)
            conv_rhs => rw [he, C.natToBits_w_a_succ hs_lt ⟨j.1 - 1, by dsimp [w_a] at *; omega⟩]
          · rw [dif_neg hj]
            have hj0 : j = ⟨0, C.w_a_pos⟩ := Fin.ext (show j.1 = 0 by omega)
            rw [hj0, C.natToBits_w_a_zero hs_lt]
        rw [hb_eq]
        let Arr1 := Function.update Arr_t cur
          (C.packRec2 (natToBits C.w_a (modeOf54 (C.extBeta α) r.1)) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false))
        -- 2. ceff2EmbLSB := r.1
        rw [C.act_setConstC]
        have hc_fn : setConstFn54 C.w_v r.1 ((C.packState A K L_bits P Arr1 Tr) ∘ C.ceff2EmbLSB cur) = natToBitsLSB C.w_v r.1 := by
          funext u
          simp only [setConstFn54, Function.comp_apply, packState, Arr1, ceff2EmbLSB, ceff2EmbMSB,
            C.packStage_eval_slotSliceEmb_rev, Function.update_self, C.packRec2_eval_ceff2, Bool.false_xor]
        rw [hc_fn]
        have hr_lt : r.1 < 2 ^ C.w_v := lt_trans (by dsimp [r]; omega) C.N_add_one_lt_two_pow_w_v
        rw [C.packStage_update_slotSliceEmb_rev, Function.update_self, Function.update_idem,
          natToBitsLSB_comp_rev C.O hr_lt, C.packRec2_update_ceff2]
        let Arr2 := Function.update Arr_t cur
          (C.packRec2 (natToBits C.w_a (modeOf54 (C.extBeta α) r.1)) (fun _ => false) (natToBits C.w_v r.1) (fun _ => false) (fun _ => false))
        -- 3. a2EmbLSB := m
        rw [C.act_setConstC]
        have ha_fn : setConstFn54 C.w_a C.m ((C.packState A K L_bits P Arr2 Tr) ∘ C.a2EmbLSB cur) = natToBitsLSB C.w_a C.m := by
          funext u
          simp only [setConstFn54, Function.comp_apply, packState, Arr2, a2EmbLSB,
            C.packStage_eval_slotSliceEmb, Function.update_self, C.packRec2_eval_a2, Bool.false_xor]
        rw [ha_fn]
        rw [C.packStage_update_slotSliceEmb, Function.update_self, Function.update_idem, C.packRec2_update_a2]
        congr 2; funext pos
        by_cases hp : pos = cur
        · subst hp; rw [Function.update_self, if_pos (by dsimp [cur]; omega)]; dsimp only [w2fRecAt]; rw [dif_neg h1, dif_pos h2]
        · rw [Function.update_of_ne hp]
          have hiff : pos.1 < t ↔ pos.1 < t + 1 := by
            have := Fin.val_ne_of_ne hp; dsimp [cur] at this; omega
          simp [Arr_t, hiff, ← C.packRec2_zero]
      · rw [dif_neg h2, LayeredCircuit.seq_unitary, act_mul]
        -- 1. b2EmbLSB := m
        rw [C.act_setConstC]
        have hb_fn : setConstFn54 C.w_a C.m (zAt t (le_of_lt ht) ∘ C.b2EmbLSB cur) = natToBitsLSB C.w_a C.m := by
          funext u; simp only [setConstFn54, Function.comp_apply, zAt, packState, b2EmbLSB, b2EmbMSB]
          rw [C.packStage_eval_slotSliceEmb_rev, if_neg (by dsimp [cur]; omega)]; simp
        rw [hb_fn]
        dsimp only [zAt, packState]
        rw [show (fun pos : Fin C.M => if pos.1 < t then C.w2fRecAt (C.extBeta α) pos else fun _ => false) = Arr_t from rfl]
        rw [C.packStage_update_slotSliceEmb_rev, hcur0, C.packRec2_zero,
          natToBitsLSB_comp_rev C.O C.m_lt_two_pow_w_a, C.packRec2_update_b2]
        let Arr1 := Function.update Arr_t cur
          (C.packRec2 (natToBits C.w_a C.m) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false))
        -- 2. a2EmbLSB := m
        rw [C.act_setConstC]
        have ha_fn : setConstFn54 C.w_a C.m ((C.packState A K L_bits P Arr1 Tr) ∘ C.a2EmbLSB cur) = natToBitsLSB C.w_a C.m := by
          funext u
          simp only [setConstFn54, Function.comp_apply, packState, Arr1, a2EmbLSB,
            C.packStage_eval_slotSliceEmb, Function.update_self, C.packRec2_eval_a2, Bool.false_xor]
        rw [ha_fn]
        rw [C.packStage_update_slotSliceEmb, Function.update_self, Function.update_idem, C.packRec2_update_a2]
        congr 2; funext pos
        by_cases hp : pos = cur
        · subst hp; rw [Function.update_self, if_pos (by dsimp [cur]; omega)]; dsimp only [w2fRecAt]; rw [dif_neg h1, dif_neg h2]
        · rw [Function.update_of_ne hp]
          have hiff : pos.1 < t ↔ pos.1 < t + 1 := by
            have := Fin.val_ne_of_ne hp; dsimp [cur] at this; omega
          simp [Arr_t, hiff, ← C.packRec2_zero]
  have hz0 : zAt 0 (Nat.zero_le C.M) = C.packState A K L_bits P (fun _ _ => false) Tr := by
    dsimp only [zAt]; rfl
  have hzM : zAt C.M le_rfl = C.packState A K L_bits P (C.w2fRecAt (C.extBeta α)) Tr := by
    dsimp only [zAt]; congr 1; funext pos; rw [if_pos pos.isLt]
  rw [hz0, hzM] at hrun
  exact hrun

/-! #### 2.3 Pass-2 Bitonic Sort (`sort2C`) & Combinatorial Spec of `xs2` -/

def rec2B (r : Qubits C.w_rec) : Qubits C.w_a :=
  fun u => r (Fin.castAdd C.w_p2 (Fin.castAdd C.w_v (Fin.castAdd 1 u)))
def rec2F (r : Qubits C.w_rec) : Qubits 1 :=
  fun u => r (Fin.castAdd C.w_p2 (Fin.castAdd C.w_v (Fin.natAdd C.w_a u)))
def rec2Ceff (r : Qubits C.w_rec) : Qubits C.w_v :=
  fun u => r (Fin.castAdd C.w_p2 (Fin.natAdd (C.w_a + 1) u))
def rec2A (r : Qubits C.w_rec) : Qubits C.w_a :=
  fun u => r (Fin.natAdd C.w_k2 (Fin.castAdd C.w_v u))
def rec2C (r : Qubits C.w_rec) : Qubits C.w_v :=
  fun u => r (Fin.natAdd C.w_k2 (Fin.natAdd C.w_a u))

def decodeRec2 (r : Qubits C.w_rec) : Sec5Rec54 :=
  (bitsToNatLSB (C.rec2A r), bitsToNat (C.rec2B r), bitsToNat (C.rec2Ceff r))

@[simp] lemma rec2B_packRec2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) : C.rec2B (C.packRec2 b f ceff a c) = b := by
  funext u; dsimp only [rec2B, packRec2]; rw [Fin.append_left, Fin.append_left, Fin.append_left]

@[simp] lemma rec2F_packRec2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) : C.rec2F (C.packRec2 b f ceff a c) = f := by
  funext u; dsimp only [rec2F, packRec2]; rw [Fin.append_left, Fin.append_left, Fin.append_right]

@[simp] lemma rec2Ceff_packRec2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) : C.rec2Ceff (C.packRec2 b f ceff a c) = ceff := by
  funext u; dsimp only [rec2Ceff, packRec2]; rw [Fin.append_left, Fin.append_right]

@[simp] lemma rec2A_packRec2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) : C.rec2A (C.packRec2 b f ceff a c) = a := by
  funext u; dsimp only [rec2A, packRec2]; rw [Fin.append_right, Fin.append_left]

@[simp] lemma rec2C_packRec2 (b : Qubits C.w_a) (f : Qubits 1) (ceff : Qubits C.w_v)
    (a : Qubits C.w_a) (c : Qubits C.w_v) : C.rec2C (C.packRec2 b f ceff a c) = c := by
  funext u; dsimp only [rec2C, packRec2]; rw [Fin.append_right, Fin.append_right]

lemma packRec2_rec (r : Qubits C.w_rec) :
    C.packRec2 (C.rec2B r) (C.rec2F r) (C.rec2Ceff r) (C.rec2A r) (C.rec2C r) = r := by
  funext u
  refine Fin.addCases (fun ik => ?_) (fun ip => ?_) u
  · refine Fin.addCases (fun ibf => ?_) (fun ic => ?_) ik
    · refine Fin.addCases (fun ib => ?_) (fun if' => ?_) ibf <;> simp [packRec2, rec2B, rec2F]
    · simp [packRec2, rec2Ceff]
  · refine Fin.addCases (fun ia => ?_) (fun ic => ?_) ip <;> simp [packRec2, rec2A, rec2C]

def validRec2 (r : Qubits C.w_rec) : Prop :=
  (C.rec2F r 0 = decide (bitsToNatLSB (C.rec2A r) < C.m)) ∧
    (C.rec2F r 0 = true → bitsToNat (C.rec2Ceff r) = 0) ∧
    C.rec2C r = (fun _ => false)

lemma bitsToNat_recKey54_rec2 (r : Qubits C.w_rec) :
    bitsToNat (recKey54 r) =
      (bitsToNat (C.rec2B r) * 2 + (if C.rec2F r 0 then 1 else 0)) * 2 ^ C.w_v +
        bitsToNat (C.rec2Ceff r) := by
  have hk : recKey54 r = Fin.append (Fin.append (C.rec2B r) (C.rec2F r)) (C.rec2Ceff r) := by
    funext u
    refine Fin.addCases (fun ibf => ?_) (fun ic => ?_) u
    · refine Fin.addCases (fun ib => ?_) (fun if' => ?_) ibf <;> simp [recKey54, rec2B, rec2F]
    · simp [recKey54, rec2Ceff]
  rw [hk, bitsToNat_append, bitsToNat_append]
  have hf : bitsToNat (C.rec2F r) = if C.rec2F r 0 then 1 else 0 := by
    dsimp only [bitsToNat]
    rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_one, dif_pos Nat.zero_lt_one]
    simp
  rw [hf, pow_one]

lemma keyW8_0_le_of_bitsToNat_recKey2_le {r₁ r₂ : Qubits C.w_rec}
    (hv1 : C.validRec2 r₁) (hv2 : C.validRec2 r₂)
    (h : bitsToNat (recKey54 r₁) ≤ bitsToNat (recKey54 r₂)) :
    keyW8_0_54 C.m (C.decodeRec2 r₁) ≤ keyW8_0_54 C.m (C.decodeRec2 r₂) := by
  rw [C.bitsToNat_recKey54_rec2, C.bitsToNat_recKey54_rec2] at h
  have hc1 := bitsToNat_lt_two_pow (C.rec2Ceff r₁)
  have hc2 := bitsToNat_lt_two_pow (C.rec2Ceff r₂)
  dsimp only [keyW8_0_54, decodeRec2]
  have hf1 : (if bitsToNatLSB (C.rec2A r₁) < C.m then 1 else 0) = if C.rec2F r₁ 0 then 1 else 0 := by
    by_cases hlt : bitsToNatLSB (C.rec2A r₁) < C.m <;> simp [hv1.1, hlt]
  have hf2 : (if bitsToNatLSB (C.rec2A r₂) < C.m then 1 else 0) = if C.rec2F r₂ 0 then 1 else 0 := by
    by_cases hlt : bitsToNatLSB (C.rec2A r₂) < C.m <;> simp [hv2.1, hlt]
  have hz1 : (if bitsToNatLSB (C.rec2A r₁) < C.m then 0 else bitsToNat (C.rec2Ceff r₁)) =
      bitsToNat (C.rec2Ceff r₁) := by
    by_cases hlt : bitsToNatLSB (C.rec2A r₁) < C.m
    · rw [if_pos hlt]; exact (hv1.2.1 (by rw [hv1.1]; simp [hlt])).symm
    · rw [if_neg hlt]
  have hz2 : (if bitsToNatLSB (C.rec2A r₂) < C.m then 0 else bitsToNat (C.rec2Ceff r₂)) =
      bitsToNat (C.rec2Ceff r₂) := by
    by_cases hlt : bitsToNatLSB (C.rec2A r₂) < C.m
    · rw [if_pos hlt]; exact (hv2.2.1 (by rw [hv2.1]; simp [hlt])).symm
    · rw [if_neg hlt]
  rw [hf1, hf2, hz1, hz2]
  rcases Nat.lt_trichotomy (bitsToNat (C.rec2B r₁)) (bitsToNat (C.rec2B r₂)) with hlt | heq | hgt
  · exact le_of_lt (Prod.Lex.left _ _ hlt)
  · rw [heq] at h ⊢
    set f₁ := if C.rec2F r₁ 0 then 1 else 0
    set f₂ := if C.rec2F r₂ 0 then 1 else 0
    rcases Nat.lt_trichotomy f₁ f₂ with hflt | hfeq | hfgt
    · exact Prod.Lex.right _ (le_of_lt (Prod.Lex.left _ _ hflt))
    · have hc_le : bitsToNat (C.rec2Ceff r₁) ≤ bitsToNat (C.rec2Ceff r₂) := by
        change f₁ = f₂ at hfeq; rw [hfeq] at h; omega
      exact Prod.Lex.right _ (by change f₁ = f₂ at hfeq; rw [hfeq]; exact Prod.Lex.right _ hc_le)
    · exfalso
      have hmul : ((bitsToNat (C.rec2B r₂) * 2 + f₂) + 1) * 2 ^ C.w_v ≤
          (bitsToNat (C.rec2B r₂) * 2 + f₁) * 2 ^ C.w_v :=
        Nat.mul_le_mul_right (2 ^ C.w_v) (by omega)
      rw [Nat.succ_mul] at hmul; dsimp only [f₁, f₂] at hmul h; omega
  · exfalso
    have hb_mul : (bitsToNat (C.rec2B r₂) * 2 + (if C.rec2F r₂ 0 then 1 else 0)) + 1 ≤
        bitsToNat (C.rec2B r₁) * 2 + (if C.rec2F r₁ 0 then 1 else 0) := by
      cases h₁ : C.rec2F r₁ 0 <;> cases h₂ : C.rec2F r₂ 0 <;>
        simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    have hmul := Nat.mul_le_mul_right (2 ^ C.w_v) hb_mul
    rw [Nat.succ_mul] at hmul; omega

lemma hAA_sort2 : ∀ i k, C.arr2AllEmb i ≠ C.scrEmb 0 C.w_k2 C.offScr_sort2 k :=
  C.emb_disj_of_bounds _ _ C.offArr C.offTr C.offScr (C.offScr + C.w_k2)
    C.arr2AllEmb_bounds (C.scrEmb_bounds 0 C.w_k2 C.offScr_sort2)
    (Or.inl (by dsimp [offScr, lenTr]; omega))

lemma hTA_sort2 : ∀ j k, C.trEmb j ≠ C.scrEmb 0 C.w_k2 C.offScr_sort2 k :=
  C.emb_disj_of_bounds _ _ C.offTr C.offScr C.offScr (C.offScr + C.w_k2)
    C.trEmb_bounds (C.scrEmb_bounds 0 C.w_k2 C.offScr_sort2) (Or.inl le_rfl)

noncomputable def sort2C : LayeredCircuit C.total :=
  C.sortKeyC C.w_k2 C.w_p2 C.arr2AllEmb (C.scrEmb 0 C.w_k2 C.offScr_sort2) C.hAT_arr2 C.hAA_sort2 C.hTA_sort2

lemma sort2C_size :
    (C.sort2C.size : ℝ) ≤ C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k2 + C.w_p2 + 1 : ℝ) :=
  C.sortKeyC_size _ _ _ _ _ _ _

noncomputable def xs2 (α : Fin C.n → ℕ) : Fin C.M → Qubits C.w_rec :=
  sort (fun r => bitsToNat (recKey54 r)) C.d true (C.w2fRecAt (C.extBeta α))

noncomputable def trs2 (α : Fin C.n → ℕ) : Qubits C.T :=
  sortTrace (fun r => bitsToNat (recKey54 r)) C.d true (C.w2fRecAt (C.extBeta α))

lemma act_sort2C (α : Fin C.n → ℕ) (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v)
    (L : Fin C.N → Qubits C.s) (P : Fin C.n → Qubits C.w_v) :
    act C.sort2C.unitary
        (ket (C.packState A K L P (C.w2fRecAt (C.extBeta α)) (fun _ => false))) =
      ket (C.packStage A K L P (C.xs2 α) (C.trs2 α) (fun _ => false)) := by
  dsimp only [sort2C]
  rw [C.act_sortKeyC C.w_k2 C.w_p2 C.arr2AllEmb (C.scrEmb 0 C.w_k2 C.offScr_sort2)
      C.hAT_arr2 C.hAA_sort2 C.hTA_sort2 _ (C.w2fRecAt (C.extBeta α))]
  · exact congrArg ket (C.packStage_update_arr2_tr _ _ _ _ _ _ _ _ _)
  · funext idx; rcases finProdFinEquiv.surjective idx with ⟨⟨pos, u⟩, rfl⟩
    simp [packState, flatReg_apply']
  · funext u; simp [packState]
  · funext u; simp [packState]

lemma w2fRecAt_props {α : Fin C.n → ℕ} (hα : ∑ i : Fin C.n, α i ≤ C.N) (pos : Fin C.M) :
    C.validRec2 (C.w2fRecAt (C.extBeta α) pos) ∧
      ((hpos : pos.1 < C.m + C.N) → C.decodeRec2 (C.w2fRecAt (C.extBeta α) pos) =
        (wtildef_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtildef_length]; exact hpos)) ∧
      (pos.1 < C.m + C.N → (C.decodeRec2 (C.w2fRecAt (C.extBeta α) pos)).2.1 < C.m) ∧
      (C.m + C.N ≤ pos.1 → C.decodeRec2 (C.w2fRecAt (C.extBeta α) pos) = (C.m, C.m, 0) ∧
        C.rec2F (C.w2fRecAt (C.extBeta α) pos) 0 = false) := by
  dsimp only [w2fRecAt]
  by_cases h1 : pos.1 < C.m
  · rw [dif_pos h1]
    have ha_lt : pos.1 < 2 ^ C.w_a := lt_trans h1 C.m_lt_two_pow_w_a
    let r := C.packRec2 (natToBits C.w_a pos.1) (fun _ => true) (fun _ => false)
      (natToBitsLSB C.w_a pos.1) (fun _ => false)
    have hv : C.validRec2 r := by
      refine ⟨?_, fun _ => by simp [r, bitsToNat], C.rec2C_packRec2 _ _ _ _ _⟩
      simp [r, bitsToNatLSB_natToBitsLSB ha_lt, h1]
    have hdec : C.decodeRec2 r = (pos.1, pos.1, 0) := by
      dsimp only [decodeRec2, r]
      rw [C.rec2A_packRec2, C.rec2B_packRec2, C.rec2Ceff_packRec2, bitsToNatLSB_natToBitsLSB ha_lt,
        bitsToNat_natToBits_exact ha_lt]
      simp [bitsToNat]
    change C.validRec2 r ∧ _
    refine ⟨hv, fun hp => ?_, fun _ => by rw [hdec]; exact h1, fun hge => by omega⟩
    rw [hdec, show (wtildef_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtildef_length]; exact hp) =
        (List.map (fun i : Fin C.m => (i.1, i.1, 0)) (List.finRange C.m) ++
          List.map (fun j : Fin C.N => (C.m, modeOf54 (C.extBeta α) j.1, j.1)) (List.finRange C.N))[pos.1]'(by simp; exact hp)
      from rfl, List.getElem_append_left (by simpa [List.length_map, List.length_finRange] using h1)]
    simp
  · rw [dif_neg h1]
    by_cases h2 : pos.1 < C.m + C.N
    · rw [dif_pos h2]
      have hm_lt : modeOf54 (C.extBeta α) (pos.1 - C.m) < C.m :=
        C.O.modeOf_lt (C.extBeta α) (C.extBeta_sum hα) (by omega)
      have hb_lt : modeOf54 (C.extBeta α) (pos.1 - C.m) < 2 ^ C.w_a := lt_trans hm_lt C.m_lt_two_pow_w_a
      have hc_lt : pos.1 - C.m < 2 ^ C.w_v := lt_trans (by omega) C.N_add_one_lt_two_pow_w_v
      let r := C.packRec2 (natToBits C.w_a (modeOf54 (C.extBeta α) (pos.1 - C.m))) (fun _ => false)
        (natToBits C.w_v (pos.1 - C.m)) (natToBitsLSB C.w_a C.m) (fun _ => false)
      have hv : C.validRec2 r := by
        refine ⟨?_, fun hf => by simp [r] at hf, C.rec2C_packRec2 _ _ _ _ _⟩
        simp [r, bitsToNatLSB_natToBitsLSB C.m_lt_two_pow_w_a]
      have hdec : C.decodeRec2 r = (C.m, modeOf54 (C.extBeta α) (pos.1 - C.m), pos.1 - C.m) := by
        dsimp only [decodeRec2, r]
        rw [C.rec2A_packRec2, C.rec2B_packRec2, C.rec2Ceff_packRec2,
          bitsToNatLSB_natToBitsLSB C.m_lt_two_pow_w_a, bitsToNat_natToBits_exact hb_lt,
          bitsToNat_natToBits_exact hc_lt]
      change C.validRec2 r ∧ _
      refine ⟨hv, fun hlt2 => ?_, fun _ => by rw [hdec]; exact hm_lt, fun hge => by omega⟩
      rw [hdec, show (wtildef_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtildef_length]; exact hlt2) =
          (List.map (fun i : Fin C.m => (i.1, i.1, 0)) (List.finRange C.m) ++
            List.map (fun j : Fin C.N => (C.m, modeOf54 (C.extBeta α) j.1, j.1)) (List.finRange C.N))[pos.1]'(by simp; exact hlt2)
        from rfl, List.getElem_append_right (by simpa [List.length_map, List.length_finRange] using Nat.not_lt.mp h1)]
      simp
    · rw [dif_neg h2]
      let r := C.packRec2 (natToBits C.w_a C.m) (fun _ => false) (fun _ => false)
        (natToBitsLSB C.w_a C.m) (fun _ => false)
      have hv : C.validRec2 r := by
        refine ⟨?_, fun hf => by simp [r] at hf, C.rec2C_packRec2 _ _ _ _ _⟩
        simp [r, bitsToNatLSB_natToBitsLSB C.m_lt_two_pow_w_a]
      have hdec : C.decodeRec2 r = (C.m, C.m, 0) := by
        dsimp only [decodeRec2, r]
        rw [C.rec2A_packRec2, C.rec2B_packRec2, C.rec2Ceff_packRec2,
          bitsToNatLSB_natToBitsLSB C.m_lt_two_pow_w_a, bitsToNat_natToBits_exact C.m_lt_two_pow_w_a]
        simp [bitsToNat]
      change C.validRec2 r ∧ _
      exact ⟨hv, fun hp => by omega, fun hp => by omega, fun _ => ⟨hdec, by simp⟩⟩

lemma xs2_mem_valid {α : Fin C.n → ℕ} (hα : ∑ i : Fin C.n, α i ≤ C.N) (pos : Fin C.M) :
    C.validRec2 (C.xs2 α pos) := by
  have hperm := C.R.sort_perm (fun r : Qubits C.w_rec => bitsToNat (recKey54 r)) C.d true (C.w2fRecAt (C.extBeta α))
  have hmem : C.xs2 α pos ∈ List.ofFn (C.w2fRecAt (C.extBeta α)) := by
    rw [← hperm.mem_iff]; exact List.mem_ofFn.mpr ⟨pos, rfl⟩
  rcases List.mem_ofFn.mp hmem with ⟨p₀, hp₀⟩
  rw [← hp₀]; exact (C.w2fRecAt_props hα p₀).1

lemma decodeRec2_xs2_prefix {α : Fin C.n → ℕ} (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (pos : ℕ) (hpos : pos < C.m + C.N) :
    C.decodeRec2 (C.xs2 α ⟨pos, lt_of_lt_of_le hpos C.m_add_N_le_M⟩) =
      (wtilde8_54 (C.extBeta α) C.N)[pos]'(by rw [C.O.wtilde8_length]; exact hpos) := by
  refine C.O.wtildef_sort_prefix (C.extBeta α) (C.extBeta_sum hα) C.M
    (C.decodeRec2 ∘ C.w2fRecAt (C.extBeta α)) (C.decodeRec2 ∘ C.xs2 α) C.m_add_N_le_M ?_ ?_ ?_ ?_ pos hpos
  · intro p hp
    exact (C.w2fRecAt_props hα ⟨p, lt_of_lt_of_le hp C.m_add_N_le_M⟩).2.1 hp
  · intro p hp hge
    dsimp only [Function.comp_apply]
    rw [(C.w2fRecAt_props hα ⟨p, hp⟩).2.2.2 hge |>.1]
  · have hperm := C.R.sort_perm (fun r : Qubits C.w_rec => bitsToNat (recKey54 r)) C.d true (C.w2fRecAt (C.extBeta α))
    have hmap := List.Perm.map C.decodeRec2 hperm
    rwa [List.map_ofFn, List.map_ofFn] at hmap
  · intro i j hij
    exact C.keyW8_0_le_of_bitsToNat_recKey2_le (C.xs2_mem_valid hα i) (C.xs2_mem_valid hα j)
      (C.R.monotone_sort (fun r : Qubits C.w_rec => bitsToNat (recKey54 r)) C.d (C.w2fRecAt (C.extBeta α)) hij)

lemma xs2_suffix_props {α : Fin C.n → ℕ} (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (pos : Fin C.M) (hge : C.m + C.N ≤ pos.1) :
    (C.decodeRec2 (C.xs2 α pos)).2.1 = C.m ∧ C.rec2F (C.xs2 α pos) 0 = false := by
  have hperm := C.R.sort_perm (fun r : Qubits C.w_rec => bitsToNat (recKey54 r)) C.d true (C.w2fRecAt (C.extBeta α))
  have hmem : C.xs2 α pos ∈ List.ofFn (C.w2fRecAt (C.extBeta α)) := by
    rw [← hperm.mem_iff]; exact List.mem_ofFn.mpr ⟨pos, rfl⟩
  rcases List.mem_ofFn.mp hmem with ⟨p₀, hp₀⟩
  have hb_le : (C.decodeRec2 (C.xs2 α pos)).2.1 ≤ C.m := by
    rw [← hp₀]
    by_cases hp : p₀.1 < C.m + C.N
    · exact le_of_lt ((C.w2fRecAt_props hα p₀).2.2.1 hp)
    · rw [(C.w2fRecAt_props hα p₀).2.2.2 (by omega) |>.1]
  have hm_eq : (C.decodeRec2 (C.xs2 α pos)).2.1 = C.m := by
    by_contra hne
    have hb_lt : (C.decodeRec2 (C.xs2 α pos)).2.1 < C.m := by omega
    let pred : Qubits C.w_rec → Bool := fun r => decide ((C.decodeRec2 r).2.1 < C.m)
    have hcnt := hperm.countP_eq pred
    rw [countP_ofFn_eq, countP_ofFn_eq] at hcnt
    have hcard2 : (Finset.univ.filter fun i : Fin C.M => pred (C.w2fRecAt (C.extBeta α) i) = true).card = C.m + C.N := by
      have hset : (Finset.univ.filter fun i : Fin C.M => pred (C.w2fRecAt (C.extBeta α) i) = true) =
          Finset.univ.filter fun i : Fin C.M => i.1 < C.m + C.N := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, pred, decide_eq_true_eq]
        by_cases hi : i.1 < C.m + C.N
        · exact iff_of_true ((C.w2fRecAt_props hα i).2.2.1 hi) hi
        · rw [iff_false_right hi, (C.w2fRecAt_props hα i).2.2.2 (by omega) |>.1]
          exact lt_irrefl C.m
      rw [hset]
      let emb : Fin (C.m + C.N) ↪ Fin C.M :=
        ⟨fun j => ⟨j.1, lt_of_lt_of_le j.isLt C.m_add_N_le_M⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
      have hinj : (Finset.univ.filter fun i : Fin C.M => i.1 < C.m + C.N) = Finset.univ.map emb := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
        exact ⟨fun hi => ⟨⟨i.1, hi⟩, Fin.ext rfl⟩, fun ⟨j, hj⟩ => by rw [← hj]; exact j.isLt⟩
      rw [hinj, Finset.card_map, Finset.card_fin]
    let emb : Fin (C.m + C.N) ↪ Fin C.M :=
      ⟨fun j => ⟨j.1, lt_of_lt_of_le j.isLt C.m_add_N_le_M⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
    have hsub1 : Finset.univ.map emb ∪ {pos} ⊆
        Finset.univ.filter fun i : Fin C.M => pred (C.xs2 α i) = true := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pred, decide_eq_true_eq]
      rcases Finset.mem_union.mp hi with hpre | hsing
      · rcases Finset.mem_map.mp hpre with ⟨j, _, rfl⟩
        have hmono := C.keyW8_0_le_of_bitsToNat_recKey2_le
          (C.xs2_mem_valid hα (emb j)) (C.xs2_mem_valid hα pos)
          (C.R.monotone_sort (fun r : Qubits C.w_rec => bitsToNat (recKey54 r)) C.d (C.w2fRecAt (C.extBeta α))
            (Fin.le_iff_val_le_val.mpr (show (emb j).1 ≤ pos.1 from le_trans (le_of_lt j.isLt) hge)))
        dsimp only [keyW8_0_54] at hmono
        by_contra hnot_lt
        have hgt : (C.decodeRec2 (C.xs2 α pos)).2.1 < (C.decodeRec2 (C.xs2 α (emb j))).2.1 := by omega
        have hstrict : keyW8_0_54 C.m (C.decodeRec2 (C.xs2 α pos)) < keyW8_0_54 C.m (C.decodeRec2 (C.xs2 α (emb j))) :=
          Prod.Lex.left _ _ hgt
        exact absurd hmono (not_le_of_gt hstrict)
      · rw [Finset.mem_singleton.mp hsing]; exact hb_lt
    have hpos_not : pos ∉ Finset.univ.map emb := by
      rw [Finset.mem_map]; rintro ⟨j, _, hj⟩
      have hjv : j.1 = pos.1 := congrArg Fin.val hj
      have := j.isLt; omega
    have hcard_ge := Finset.card_le_card hsub1
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hpos_not),
      Finset.card_map, Finset.card_fin, Finset.card_singleton] at hcard_ge
    have hcard1 : (Finset.univ.filter fun i : Fin C.M => pred (C.xs2 α i) = true).card = C.m + C.N := by
      have hcnt' : (Finset.univ.filter fun i : Fin C.M => pred (C.xs2 α i) = true).card =
          (Finset.univ.filter fun i : Fin C.M => pred (C.w2fRecAt (C.extBeta α) i) = true).card := by
        dsimp only [xs2]
        (convert hcnt; exact Finset.ext fun _ => Iff.rfl)
      exact hcnt'.trans hcard2
    omega
  refine ⟨hm_eq, ?_⟩
  have hnot : ¬ p₀.1 < C.m + C.N := fun hp => by
    have hlt := (C.w2fRecAt_props hα p₀).2.2.1 hp
    rw [hp₀] at hlt; omega
  rw [← hp₀]; exact (C.w2fRecAt_props hα p₀).2.2.2 (by omega) |>.2

/-! #### 2.4 Pass-2 Prefix-Sum Extraction (`fillPref2C`) -/

noncomputable def fillPref2Prefix (pos : Fin (C.m + C.N)) : LayeredCircuit C.total :=
  let posM := C.posM_of_lt pos
  (C.setConstC C.w_pos pos.1 C.TEmb).seq
    ((C.copyRegC C.w_a (C.a2EmbLSB posM) C.UEmb_wa
        (C.slotSlice_scr_disj posM C.w_k2 C.w_a (1 + C.w_pos) C.w_a C.hoff_a2 C.offScr_U_wa)).seq
      (C.subInPlaceC C.w_pos C.UEmb C.TEmb C.anc1
        (C.scrEmb_disj (1 + C.w_pos) C.w_pos 1 C.w_pos C.offScr_U C.offScr_T (Or.inr le_rfl))
        (C.scrEmb_disj (1 + C.w_pos) C.w_pos (1 + 2 * C.w_pos) 1 C.offScr_U C.offScr_anc1 (Or.inl (by omega)))
        (C.scrEmb_disj 1 C.w_pos (1 + 2 * C.w_pos) 1 C.offScr_T C.offScr_anc1 (Or.inl (by omega)))))

lemma fillPref2Prefix_size (pos : Fin (C.m + C.N)) :
    (C.fillPref2Prefix pos).size ≤ 15 * C.w_pos + C.w_a := by
  dsimp only [fillPref2Prefix]
  rw [LayeredCircuit.seq_size, LayeredCircuit.seq_size, C.copyRegC_size, C.subInPlaceC_size]
  have h1 := C.setConstC_size C.w_pos pos.1 C.TEmb
  omega

noncomputable def fillPref2StepC (pos : Fin (C.m + C.N)) : LayeredCircuit C.total :=
  let posM := C.posM_of_lt pos
  (C.fillPref2Prefix pos).seq
    ((C.ctrlCopyRegC C.w_v (C.f2Emb posM) C.TEmb_wv (C.c2EmbLSB posM)
        (C.slotSlice_scr_disj posM C.w_a 1 1 C.w_v C.hoff_f2 C.offScr_T_wv)
        (C.slotSlice_disj_same_pos posM C.w_a 1 (C.w_k2 + C.w_a) C.w_v C.hoff_f2 C.hoff_c2
          (Or.inl (by dsimp [w_k2]; omega)))
        (C.scr_slotSlice_disj posM 1 C.w_v (C.w_k2 + C.w_a) C.w_v C.offScr_T_wv C.hoff_c2)).seq
      (C.fillPref2Prefix pos).adj)

lemma fillPref2StepC_size (pos : Fin (C.m + C.N)) :
    (C.fillPref2StepC pos).size ≤ 30 * C.w_pos + 2 * C.w_a + 5 * C.w_v := by
  dsimp only [fillPref2StepC]
  rw [LayeredCircuit.seq_size, LayeredCircuit.seq_size, C.ctrlCopyRegC_size, LayeredCircuit.adj_size]
  have h1 := C.fillPref2Prefix_size pos
  omega

noncomputable def fillPref2C : LayeredCircuit C.total :=
  LayeredCircuit.seqList (List.ofFn C.fillPref2StepC)

lemma fillPref2C_size :
    C.fillPref2C.size ≤ (C.m + C.N) * (30 * C.w_pos + 2 * C.w_a + 5 * C.w_v) :=
  seqList_ofFn_size_le C.fillPref2StepC _ C.fillPref2StepC_size

lemma act_fillPref2Prefix (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (x2_rec : Fin C.M → Qubits C.w_rec) (Tr : Qubits C.T)
    (pos : Fin (C.m + C.N)) (c_cur : Qubits C.w_v) :
    let posM := C.posM_of_lt pos
    let r0 := x2_rec posM
    let r' := C.packRec2 (C.rec2B r0) (C.rec2F r0) (C.rec2Ceff r0) (C.rec2A r0) c_cur
    let x2' := Function.update x2_rec posM r'
    let a_val := bitsToNatLSB (C.rec2A r0)
    let T_out := natToBitsLSB C.w_pos (2 ^ C.w_pos + pos.1 - a_val)
    let U_out : Qubits C.w_pos := fun j => if h : j.1 < C.w_a then C.rec2A r0 ⟨j.1, h⟩ else false
    act (C.fillPref2Prefix pos).unitary (ket (C.packState A K L P x2' Tr)) =
      ket (C.packStage A K L P x2' Tr (C.packScr1 false T_out U_out)) := by
  intro posM r0 r' x2' a_val T_out U_out
  have hx2_pos : x2' posM = r' := Function.update_self posM r' x2_rec
  have hpos_lt : pos.1 < 2 ^ C.w_pos := lt_trans (lt_of_lt_of_le pos.isLt C.m_add_N_le_M) C.M_lt_two_pow_w_pos
  dsimp only [fillPref2Prefix]
  rw [LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul]
  -- 1. setConstC T := pos.1
  rw [C.act_setConstC]
  have hT0 : setConstFn54 C.w_pos pos.1 ((C.packState A K L P x2' Tr) ∘ C.TEmb) = natToBitsLSB C.w_pos pos.1 := by
    funext j; simp only [setConstFn54, Function.comp_apply, packState, TEmb, C.packStage_scrEmb, Bool.false_xor]
  rw [hT0, packState, ← C.packScr1_zero, C.packStage_update_scrEmb, C.packScr1_update_T]
  -- 2. copyRegC U := a2
  rw [C.act_copyRegC]
  have ha_read : (fun u : Fin C.w_a => xor ((C.packStage A K L P x2' Tr
      (C.packScr1 false (natToBitsLSB C.w_pos pos.1) (fun _ => false))) (C.UEmb_wa u))
      ((C.packStage A K L P x2' Tr
      (C.packScr1 false (natToBitsLSB C.w_pos pos.1) (fun _ => false))) (C.a2EmbLSB posM u))) = C.rec2A r0 := by
    funext u
    have hU0 : C.packStage A K L P x2' Tr (C.packScr1 false (natToBitsLSB C.w_pos pos.1) (fun _ => false)) (C.UEmb_wa u) = false := by
      simp only [UEmb_wa, C.packStage_scrEmb]
      have hhj : (⟨1 + C.w_pos + u.1, by have := u.isLt; have := C.w_a_lt_w_pos; dsimp [lenScr]; omega⟩ : Fin C.lenScr) =
          segEmb (1 + C.w_pos) C.w_pos C.lenScr C.offScr_U ⟨u.1, lt_trans u.isLt C.w_a_lt_w_pos⟩ := Fin.ext (by simp)
      rw [hhj, C.packScr1_U]
    rw [hU0, Bool.false_xor]
    simp only [a2EmbLSB, C.packStage_eval_slotSliceEmb, hx2_pos]
    exact C.packRec2_eval_a2 _ _ _ _ _ u
  rw [ha_read, C.packStage_update_scrEmb, C.packScr1_update_U_wa]
  -- 3. subInPlaceC T := 2^w_pos + pos.1 - a_val
  rw [C.act_subInPlaceC _ _ _ _ _ _ _ _ (fun j => by
    simp only [anc1, C.packStage_scrEmb]
    have hhj : (⟨1 + 2 * C.w_pos + j.1, by have := j.isLt; dsimp [lenScr]; omega⟩ : Fin C.lenScr) =
        segEmb (1 + 2 * C.w_pos) 1 C.lenScr C.offScr_anc1 j := Fin.ext (by simp)
    rw [hhj, C.packScr1_anc1])]
  have hU_val : bitsToNatLSB ((C.packStage A K L P x2' Tr
      (C.packScr1 false (natToBitsLSB C.w_pos pos.1) U_out)) ∘ C.UEmb) = a_val := by
    have hcomp : (C.packStage A K L P x2' Tr (C.packScr1 false (natToBitsLSB C.w_pos pos.1) U_out)) ∘ C.UEmb = U_out := by
      funext u; simp only [Function.comp_apply, UEmb, C.packStage_scrEmb]; exact C.packScr1_U _ _ U_out u
    rw [hcomp]; dsimp only [U_out]; rw [bitsToNatLSB_pad_high_zero (le_of_lt C.w_a_lt_w_pos)]
  have hT_val : bitsToNatLSB ((C.packStage A K L P x2' Tr
      (C.packScr1 false (natToBitsLSB C.w_pos pos.1) U_out)) ∘ C.TEmb) = pos.1 := by
    have hcomp : (C.packStage A K L P x2' Tr (C.packScr1 false (natToBitsLSB C.w_pos pos.1) U_out)) ∘ C.TEmb =
        natToBitsLSB C.w_pos pos.1 := by
      funext u; simp only [Function.comp_apply, TEmb, C.packStage_scrEmb]; exact C.packScr1_T _ _ U_out u
    rw [hcomp, bitsToNatLSB_natToBitsLSB hpos_lt]
  rw [hU_val, hT_val, C.packStage_update_scrEmb, C.packScr1_update_T]

lemma act_fillPref2C (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) (Tr : Qubits C.T) :
    let ys2 : Fin C.M → Qubits C.w_p2 := fun pos =>
      let r := C.xs2 α pos
      let c_new : Qubits C.w_v :=
        if h : pos.1 < C.m + C.N ∧ C.rec2F r 0 = true then
          let t := (wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact h.1)
          have htm : t.1 < C.m := by
            have hd := C.decodeRec2_xs2_prefix hα pos.1 h.1
            have hv1 := (C.xs2_mem_valid hα pos).1
            change C.rec2F r 0 = _ at hv1
            rw [h.2] at hv1
            have hlt : bitsToNatLSB (C.rec2A r) < C.m := decide_eq_true_eq.mp hv1.symm
            have hd' : C.decodeRec2 r =
                (wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact h.1) := hd
            dsimp only [t]; rw [← hd']; exact hlt
          natToBitsLSB C.w_v (prefSum54 (C.extBeta α) ⟨t.1, htm⟩)
        else fun _ => false
      Fin.append (C.rec2A r) c_new
    let x2_filled : Fin C.M → Qubits C.w_rec := fun pos =>
      Fin.append (recKey54 (C.xs2 α pos)) (ys2 pos)
    act C.fillPref2C.unitary (ket (C.packState A K L P (C.xs2 α) Tr)) =
      ket (C.packState A K L P x2_filled Tr) := by
  intro ys2 x2_filled
  let x2At : ℕ → Fin C.M → Qubits C.w_rec := fun t pos =>
    if pos.1 < t then x2_filled pos else C.xs2 α pos
  let zAt : (t : ℕ) → t ≤ C.m + C.N → Qubits C.total := fun t _ =>
    C.packState A K L P (x2At t) Tr
  have hrun := act_seqList_fin_ket C.fillPref2StepC zAt fun t ht => by
    let pos : Fin (C.m + C.N) := ⟨t, ht⟩
    let posM := C.posM_of_lt pos
    let r0 := C.xs2 α posM
    have hx_cur : x2At t posM = r0 := if_neg (by dsimp [posM, posM_of_lt, pos]; omega)
    have hr0_eq : r0 = C.packRec2 (C.rec2B r0) (C.rec2F r0) (C.rec2Ceff r0) (C.rec2A r0) (C.rec2C r0) :=
      (C.packRec2_rec r0).symm
    have hvalid := C.xs2_mem_valid hα posM
    have hc0 : C.rec2C r0 = fun _ => false := hvalid.2.2
    let c_new : Qubits C.w_v :=
      if hf : C.rec2F r0 0 = true then
        let t8 := (wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact pos.isLt)
        have htm : t8.1 < C.m := by
          have hd := C.decodeRec2_xs2_prefix hα pos.1 pos.isLt
          have hv1 := hvalid.1; rw [hf] at hv1
          have hlt : bitsToNatLSB (C.rec2A r0) < C.m := decide_eq_true_eq.mp hv1.symm
          have hd' : C.decodeRec2 r0 =
              (wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact pos.isLt) := hd
          dsimp only [t8]; rw [← hd']; exact hlt
        natToBitsLSB C.w_v (prefSum54 (C.extBeta α) ⟨t8.1, htm⟩)
      else fun _ => false
    have hf_fwd := C.act_fillPref2Prefix A K L P (x2At t) Tr pos (C.rec2C r0)
    have hf_bwd := C.act_fillPref2Prefix A K L P (x2At t) Tr pos c_new
    dsimp only at hf_fwd
    rw [show x2At t (C.posM_of_lt pos) = r0 from hx_cur, C.packRec2_rec] at hf_fwd
    have hupd_self : Function.update (x2At t) (C.posM_of_lt pos) r0 = x2At t := by
      rw [← hx_cur]; exact Function.update_eq_self _ _
    rw [hupd_self] at hf_fwd
    dsimp only [fillPref2StepC]
    rw [LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul, hf_fwd]
    rw [C.act_ctrlCopyRegC]
    let scrMid := C.packScr1 false (natToBitsLSB C.w_pos (2 ^ C.w_pos + pos.1 - bitsToNatLSB (C.rec2A r0)))
      (fun j => if h : j.1 < C.w_a then C.rec2A r0 ⟨j.1, h⟩ else false)
    have hctrl_val : (fun u : Fin C.w_v =>
        if C.packStage A K L P (x2At t) Tr scrMid (C.f2Emb posM 0) then
          xor (C.packStage A K L P (x2At t) Tr scrMid (C.c2EmbLSB posM u))
            (C.packStage A K L P (x2At t) Tr scrMid (C.TEmb_wv u))
        else C.packStage A K L P (x2At t) Tr scrMid (C.c2EmbLSB posM u)) = c_new := by
      have hf_read : C.packStage A K L P (x2At t) Tr scrMid (C.f2Emb posM 0) = C.rec2F r0 0 := by
        simp only [f2Emb, C.packStage_eval_slotSliceEmb, hx_cur]
        conv_lhs => rw [hr0_eq]
        exact C.packRec2_eval_f2 _ _ _ _ _ 0
      have hc_read : ∀ u, C.packStage A K L P (x2At t) Tr scrMid (C.c2EmbLSB posM u) = false := by
        intro u
        simp only [c2EmbLSB, C.packStage_eval_slotSliceEmb, hx_cur]
        conv_lhs => rw [hr0_eq]
        rw [C.packRec2_eval_c2, hc0]
      rw [hf_read]
      by_cases hf : C.rec2F r0 0 = true
      · dsimp only [c_new]; rw [dif_pos hf]
        let t8 := (wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact pos.isLt)
        have hd := C.decodeRec2_xs2_prefix hα pos.1 pos.isLt
        have hv1 := hvalid.1; rw [hf] at hv1
        have ha_lt_m : bitsToNatLSB (C.rec2A r0) < C.m := decide_eq_true_eq.mp hv1.symm
        have hd' : C.decodeRec2 r0 = t8 := hd
        have htm : t8.1 < C.m := by rw [← hd']; exact ha_lt_m
        have hw8 := (C.O.wtilde8_pos_spec (C.extBeta α) (C.extBeta_sum hα) pos.1
          (by rw [C.O.wtilde8_length]; exact pos.isLt)).1 htm
        rcases hw8 with ⟨hi, _, hpos_ge, hsub⟩
        have ha_eq : bitsToNatLSB (C.rec2A r0) = t8.1 := by rw [← hd']; rfl
        have hle' : t8.1 ≤ pos.1 := hpos_ge
        have hsub_val : 2 ^ C.w_pos + pos.1 - bitsToNatLSB (C.rec2A r0) =
            2 ^ C.w_pos + (pos.1 - t8.1) := by
          rw [ha_eq]; exact Nat.add_sub_assoc hle' (2 ^ C.w_pos)
        funext u
        rw [if_pos hf, hc_read u, Bool.false_xor]
        simp only [TEmb_wv, C.packStage_scrEmb]
        have hhj : (⟨1 + u.1, by have := u.isLt; have := C.w_v_lt_w_pos; dsimp [lenScr]; omega⟩ : Fin C.lenScr) =
            segEmb 1 C.w_pos C.lenScr C.offScr_T ⟨u.1, lt_trans u.isLt C.w_v_lt_w_pos⟩ := Fin.ext (by simp)
        dsimp only [scrMid]
        rw [hhj, C.packScr1_T, hsub_val, hsub]
        have hmod : (2 ^ C.w_pos + prefSum54 (C.extBeta α) ⟨t8.1, hi⟩) / 2 ^ u.1 % 2 =
            prefSum54 (C.extBeta α) ⟨t8.1, hi⟩ / 2 ^ u.1 % 2 := by
          have hpow : 2 ^ C.w_pos = 2 ^ u.1 * 2 ^ (C.w_pos - u.1) := by
            rw [← pow_add, Nat.add_sub_cancel' (le_of_lt (lt_trans u.isLt C.w_v_lt_w_pos))]
          have hpos_ge1 : 1 ≤ C.w_pos - u.1 := by have := u.isLt; have := C.w_v_lt_w_pos; omega
          obtain ⟨q', hq'⟩ := dvd_pow_self 2 (by omega : C.w_pos - u.1 ≠ 0)
          rw [hpow, hq', show 2 ^ u.1 * (2 * q') + prefSum54 (C.extBeta α) ⟨t8.1, hi⟩ =
              prefSum54 (C.extBeta α) ⟨t8.1, hi⟩ + 2 ^ u.1 * (2 * q') by ring,
            Nat.add_mul_div_left _ _ (Nat.two_pow_pos u.1), Nat.add_mul_mod_self_left]
        dsimp only [natToBitsLSB]
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
        dsimp only [t8] at hmod ⊢
        rw [hmod]
      · dsimp only [c_new]; rw [dif_neg hf]
        funext u; rw [if_neg hf]; exact hc_read u
    rw [hctrl_val]
    rw [C.packStage_update_slotSliceEmb]
    have hup_eq : Function.update (x2At t) posM
        (updateOn (segEmb (C.w_k2 + C.w_a) C.w_v C.w_rec C.hoff_c2) (x2At t posM) c_new) =
        Function.update (x2At t) posM (C.packRec2 (C.rec2B r0) (C.rec2F r0) (C.rec2Ceff r0) (C.rec2A r0) c_new) := by
      congr 1; conv_lhs => rw [hx_cur, hr0_eq, C.packRec2_update_c2]
    dsimp only at hf_bwd
    rw [show x2At t (C.posM_of_lt pos) = r0 from hx_cur] at hf_bwd
    rw [hup_eq, act_adj_ket_of_act_ket _ hf_bwd]
    dsimp only [zAt, packState]
    congr 2; funext pos'
    by_cases hp : pos' = posM
    · subst hp; rw [Function.update_self]
      dsimp only [x2At]
      conv_rhs => rw [if_pos (by dsimp [posM, posM_of_lt, pos]; omega)]
      dsimp only [x2_filled, ys2]
      have hpre : posM.1 < C.m + C.N := pos.isLt
      have hc_eq : (if h : posM.1 < C.m + C.N ∧ C.rec2F r0 0 = true then
          let t' := (wtilde8_54 (C.extBeta α) C.N)[posM.1]'(by rw [C.O.wtilde8_length]; exact h.1)
          have htm' : t'.1 < C.m := by
            have hd := C.decodeRec2_xs2_prefix hα posM.1 h.1
            have hv1 := (C.xs2_mem_valid hα posM).1
            change C.rec2F r0 0 = _ at hv1
            rw [h.2] at hv1
            have hlt : bitsToNatLSB (C.rec2A r0) < C.m := decide_eq_true_eq.mp hv1.symm
            have hd' : C.decodeRec2 r0 = t' := by
              simpa [posM, posM_of_lt] using hd
            dsimp only [t'] at hd' ⊢; rw [← hd']; exact hlt
          natToBitsLSB C.w_v (prefSum54 (C.extBeta α) ⟨t'.1, htm'⟩)
          else fun _ => false) = c_new := by
        dsimp only [c_new]; by_cases hf : C.rec2F r0 0 = true
        · rw [dif_pos ⟨hpre, hf⟩, dif_pos hf]
        · rw [dif_neg (fun h => hf h.2), dif_neg hf]
      rw [hc_eq]
      dsimp only [r0]
      funext u; refine Fin.addCases (fun ik => ?_) (fun ip => ?_) u
      · rw [Fin.append_left]
        refine Fin.addCases (fun ibf => ?_) (fun ic => ?_) ik
        · refine Fin.addCases (fun ib => ?_) (fun if' => ?_) ibf <;>
            simp [packRec2, recKey54, rec2B, rec2F]
        · simp [packRec2, recKey54, rec2Ceff]
      · refine Fin.addCases (fun ia => ?_) (fun ic => ?_) ip <;> simp [packRec2]
    · rw [Function.update_of_ne hp]
      have hiff : pos'.1 < t ↔ pos'.1 < t + 1 := by
        have := Fin.val_ne_of_ne hp; dsimp [posM, posM_of_lt, pos] at this; omega
      simp [x2At, hiff]
  have hz0 : zAt 0 (Nat.zero_le _) = C.packState A K L P (C.xs2 α) Tr := by
    dsimp only [zAt, x2At]; rfl
  have hzN : zAt (C.m + C.N) le_rfl = C.packState A K L P x2_filled Tr := by
    dsimp only [zAt, x2At]; congr 1; funext pos
    by_cases hp : pos.1 < C.m + C.N
    · rw [if_pos hp]
    · rw [if_neg hp]
      dsimp only [x2_filled, ys2]
      have hc0 : (C.xs2 α pos) = Fin.append (recKey54 (C.xs2 α pos)) (Fin.append (C.rec2A (C.xs2 α pos)) (fun _ => false)) := by
        have hvalid := C.xs2_mem_valid hα pos
        conv_lhs => rw [← C.packRec2_rec (C.xs2 α pos), hvalid.2.2]
        funext u; refine Fin.addCases (fun ik => ?_) (fun ip => ?_) u
        · refine Fin.addCases (fun ibf => ?_) (fun ic => ?_) ik
          · refine Fin.addCases (fun ib => ?_) (fun if' => ?_) ibf <;>
              simp [packRec2, recKey54, rec2B, rec2F]
          · simp [packRec2, recKey54, rec2Ceff]
        · refine Fin.addCases (fun ia => ?_) (fun ic => ?_) ip <;> simp [packRec2]
      rw [dif_neg (by omega)]; exact hc0
  rw [hz0, hzN] at hrun
  exact hrun

/-! #### 2.5 Pass-2 Unroute (`sort2C.adj`) & `pass2PrefixC` -/

def x2Unrouted (β : Fin C.m → ℕ) (pos : Fin C.M) : Qubits C.w_rec :=
  if h1 : pos.1 < C.m then
    C.packRec2 (natToBits C.w_a pos.1) (fun _ => true) (fun _ => false)
      (natToBitsLSB C.w_a pos.1) (natToBitsLSB C.w_v (prefSum54 β ⟨pos.1, h1⟩))
  else if _h2 : pos.1 < C.m + C.N then
    C.packRec2 (natToBits C.w_a (modeOf54 β (pos.1 - C.m))) (fun _ => false)
      (natToBits C.w_v (pos.1 - C.m)) (natToBitsLSB C.w_a C.m) (fun _ => false)
  else
    C.packRec2 (natToBits C.w_a C.m) (fun _ => false) (fun _ => false) (natToBitsLSB C.w_a C.m) (fun _ => false)

lemma act_sort2C_adj (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s)
    (P : Fin C.n → Qubits C.w_v) :
    let ys2 : Fin C.M → Qubits C.w_p2 := fun pos =>
      let r := C.xs2 α pos
      let c_new : Qubits C.w_v :=
        if h : pos.1 < C.m + C.N ∧ C.rec2F r 0 = true then
          let t := (wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact h.1)
          have htm : t.1 < C.m := by
            have hd := C.decodeRec2_xs2_prefix hα pos.1 h.1
            have hv1 := (C.xs2_mem_valid hα pos).1
            change C.rec2F r 0 = _ at hv1
            rw [h.2] at hv1
            have hlt : bitsToNatLSB (C.rec2A r) < C.m := decide_eq_true_eq.mp hv1.symm
            have hd' : C.decodeRec2 r = t := hd
            dsimp only [t] at hd' ⊢; rw [← hd']; exact hlt
          natToBitsLSB C.w_v (prefSum54 (C.extBeta α) ⟨t.1, htm⟩)
        else fun _ => false
      Fin.append (C.rec2A r) c_new
    let x2_filled : Fin C.M → Qubits C.w_rec := fun pos => Fin.append (recKey54 (C.xs2 α pos)) (ys2 pos)
    act C.sort2C.adj.unitary (ket (C.packStage A K L P x2_filled (C.trs2 α) (fun _ => false))) =
      ket (C.packState A K L P (C.x2Unrouted (C.extBeta α)) (fun _ => false)) := by
  intro ys2 x2_filled
  let k_in : Fin C.M → Qubits C.w_k2 := recKey54 ∘ C.w2fRecAt (C.extBeta α)
  have hsort_k : sort bitsToNat C.d true k_in = recKey54 ∘ C.xs2 α :=
    (C.R.sort_of_key_comp bitsToNat (recKey54 : Qubits C.w_rec → Qubits C.w_k2)
      C.d true (C.w2fRecAt (C.extBeta α))).symm
  have htr_k : sortTrace bitsToNat C.d true k_in = C.trs2 α :=
    (C.R.sortTrace_of_key_comp bitsToNat (recKey54 : Qubits C.w_rec → Qubits C.w_k2)
      C.d true (C.w2fRecAt (C.extBeta α))).symm
  dsimp only [sort2C]
  rw [C.act_sortKeyC_adj C.w_k2 C.w_p2 C.arr2AllEmb (C.scrEmb 0 C.w_k2 C.offScr_sort2)
      C.hAT_arr2 C.hAA_sort2 C.hTA_sort2 _ k_in ys2]
  · rw [C.packStage_update_arr2_tr]
    let keyB : Qubits C.w_k2 → ℕ := fun k => bitsToNat (fun u : Fin C.w_a => k (Fin.castAdd C.w_v (Fin.castAdd 1 u)))
    let keyF : Qubits C.w_k2 → Bool := fun k => k (Fin.castAdd C.w_v (Fin.natAdd C.w_a 0))
    let R2 : Qubits C.w_k2 → Qubits C.w_p2 → Prop := fun k p =>
      let a_p := fun u : Fin C.w_a => p (Fin.castAdd C.w_v u)
      let c_p := fun u : Fin C.w_v => p (Fin.natAdd C.w_a u)
      if keyF k then
        ∃ h : keyB k < C.m, a_p = natToBitsLSB C.w_a (keyB k) ∧ c_p = natToBitsLSB C.w_v (prefSum54 (C.extBeta α) ⟨keyB k, h⟩)
      else a_p = natToBitsLSB C.w_a C.m ∧ c_p = fun _ => false
    have hpre : ∀ pos : Fin C.M, R2 (sort bitsToNat C.d true k_in pos) (ys2 pos) := by
      intro pos
      have hk_eq : sort bitsToNat C.d true k_in pos = recKey54 (C.xs2 α pos) := congrFun hsort_k pos
      rw [hk_eq]
      have hvalid := C.xs2_mem_valid hα pos
      have ha_p : (fun u : Fin C.w_a => ys2 pos (Fin.castAdd C.w_v u)) = C.rec2A (C.xs2 α pos) := by
        funext u; simp [ys2]
      have hc_p : (fun u : Fin C.w_v => ys2 pos (Fin.natAdd C.w_a u)) = fun u =>
          (if h : pos.1 < C.m + C.N ∧ C.rec2F (C.xs2 α pos) 0 = true then
            let t := (wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact h.1)
            have htm : t.1 < C.m := by
              have hd := C.decodeRec2_xs2_prefix hα pos.1 h.1
              have hv1 := hvalid.1; rw [h.2] at hv1
              have hlt : bitsToNatLSB (C.rec2A (C.xs2 α pos)) < C.m := decide_eq_true_eq.mp hv1.symm
              have hd' : C.decodeRec2 (C.xs2 α pos) = t := hd
              dsimp only [t] at hd' ⊢; rw [← hd']; exact hlt
            natToBitsLSB C.w_v (prefSum54 (C.extBeta α) ⟨t.1, htm⟩)
           else fun _ => false) u := by
        funext u; simp [ys2]
      have hkeyF : keyF (recKey54 (C.xs2 α pos)) = C.rec2F (C.xs2 α pos) 0 := rfl
      have hkeyB : keyB (recKey54 (C.xs2 α pos)) = bitsToNat (C.rec2B (C.xs2 α pos)) := rfl
      dsimp only [R2]; rw [ha_p, hc_p, hkeyF, hkeyB]
      by_cases hf : C.rec2F (C.xs2 α pos) 0 = true
      · rw [if_pos hf]
        have hp_lt : pos.1 < C.m + C.N := by
          by_contra hge; have hf0 := (C.xs2_suffix_props hα pos (by omega)).2; rw [hf] at hf0; cases hf0
        have hd := C.decodeRec2_xs2_prefix hα pos.1 hp_lt
        rw [show (⟨pos.1, lt_of_lt_of_le hp_lt C.m_add_N_le_M⟩ : Fin C.M) = pos from Fin.ext rfl] at hd
        have hv1 := hvalid.1; rw [hf] at hv1
        have ha_lt_m : bitsToNatLSB (C.rec2A (C.xs2 α pos)) < C.m := decide_eq_true_eq.mp hv1.symm
        have hd' : C.decodeRec2 (C.xs2 α pos) =
            (wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact hp_lt) := hd
        have htm : ((wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact hp_lt)).1 < C.m := by
          rw [← hd']; exact ha_lt_m
        have hw8 := (C.O.wtilde8_pos_spec (C.extBeta α) (C.extBeta_sum hα) pos.1
          (by rw [C.O.wtilde8_length]; exact hp_lt)).1 htm
        rcases hw8 with ⟨hi, ht_eq, _, _⟩
        have ht21 : ((wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact hp_lt)).2.1 =
            ((wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact hp_lt)).1 := by
          rw [ht_eq]
        have hb_eq : bitsToNat (C.rec2B (C.xs2 α pos)) =
            ((wtilde8_54 (C.extBeta α) C.N)[pos.1]'(by rw [C.O.wtilde8_length]; exact hp_lt)).1 := by
          have := congrArg (fun t : Sec5Rec54 => t.2.1) hd; exact this.trans ht21
        have ha_eq : bitsToNatLSB (C.rec2A (C.xs2 α pos)) = bitsToNat (C.rec2B (C.xs2 α pos)) := by
          have := congrArg (fun t : Sec5Rec54 => t.1) hd
          change bitsToNatLSB (C.rec2A (C.xs2 α pos)) = _ at this
          rw [this, hb_eq]
        have hperm := C.R.sort_perm (fun r : Qubits C.w_rec => bitsToNat (recKey54 r)) C.d true (C.w2fRecAt (C.extBeta α))
        have hmem : C.xs2 α pos ∈ List.ofFn (C.w2fRecAt (C.extBeta α)) := by
          rw [← hperm.mem_iff]; exact List.mem_ofFn.mpr ⟨pos, rfl⟩
        rcases List.mem_ofFn.mp hmem with ⟨p₀, hp₀⟩
        have hrecA_bits : C.rec2A (C.xs2 α pos) = natToBitsLSB C.w_a (bitsToNatLSB (C.rec2A (C.xs2 α pos))) := by
          rw [← hp₀]; dsimp only [w2fRecAt]
          split_ifs
          · rw [C.rec2A_packRec2, bitsToNatLSB_natToBitsLSB (lt_trans (by assumption) C.m_lt_two_pow_w_a)]
          · rw [C.rec2A_packRec2, bitsToNatLSB_natToBitsLSB C.m_lt_two_pow_w_a]
          · rw [C.rec2A_packRec2, bitsToNatLSB_natToBitsLSB C.m_lt_two_pow_w_a]
        refine ⟨by rw [hb_eq]; exact hi, ?_, ?_⟩
        · rw [← ha_eq]; exact hrecA_bits
        · rw [dif_pos ⟨hp_lt, hf⟩]
          exact congrArg (fun idx : Fin C.m => natToBitsLSB C.w_v (prefSum54 (C.extBeta α) idx)) (Fin.ext hb_eq.symm)
      · rw [if_neg hf]
        have hperm := C.R.sort_perm (fun r : Qubits C.w_rec => bitsToNat (recKey54 r)) C.d true (C.w2fRecAt (C.extBeta α))
        have hmem : C.xs2 α pos ∈ List.ofFn (C.w2fRecAt (C.extBeta α)) := by
          rw [← hperm.mem_iff]; exact List.mem_ofFn.mpr ⟨pos, rfl⟩
        rcases List.mem_ofFn.mp hmem with ⟨p₀, hp₀⟩
        have hrecA_eq : C.rec2A (C.xs2 α pos) = natToBitsLSB C.w_a C.m := by
          rw [← hp₀]; dsimp only [w2fRecAt]
          by_cases h1 : p₀.1 < C.m
          · exfalso; apply hf; rw [← hp₀]; dsimp only [w2fRecAt]; rw [dif_pos h1, C.rec2F_packRec2]
          · rw [dif_neg h1]; split_ifs <;> exact C.rec2A_packRec2 _ _ _ _ _
        refine ⟨hrecA_eq, ?_⟩
        funext u; simp [hf]
    have hpost := C.R.unrouteSort_rel_sort bitsToNat C.d true k_in ys2 R2 hpre
    dsimp only [packState]; congr 2; funext pos
    have hp := hpost pos
    dsimp only [R2, k_in, Function.comp_apply] at hp
    let y_out := unrouteSort C.d (sortTrace bitsToNat C.d true k_in) ys2
    have hk_append : ∀ b f ceff a₀ c₀ a c,
        Fin.append (recKey54 (C.packRec2 b f ceff a₀ c₀)) (Fin.append a c) = C.packRec2 b f ceff a c := by
      intro b f ceff a₀ c₀ a c; funext u
      refine Fin.addCases (fun ik => ?_) (fun ip => ?_) u
      · refine Fin.addCases (fun ibf => ?_) (fun ic => ?_) ik
        · refine Fin.addCases (fun ib => ?_) (fun if' => ?_) ibf <;>
            simp [packRec2, recKey54]
        · simp [packRec2, recKey54]
      · refine Fin.addCases (fun ia => ?_) (fun ic => ?_) ip <;> simp [packRec2]
    dsimp only [w2fRecAt] at hp
    dsimp only [w2fRecAt, x2Unrouted]
    by_cases h1 : pos.1 < C.m
    · simp only [dif_pos h1] at hp; rw [dif_pos h1]
      have hf1 : keyF (recKey54 (C.packRec2 (natToBits C.w_a pos.1) (fun _ => true) (fun _ => false)
          (natToBitsLSB C.w_a pos.1) (fun _ => false))) = true := by
        change C.rec2F (C.packRec2 (natToBits C.w_a pos.1) (fun _ => true) (fun _ => false)
          (natToBitsLSB C.w_a pos.1) (fun _ => false)) 0 = true
        rw [C.rec2F_packRec2]
      have hb1 : keyB (recKey54 (C.packRec2 (natToBits C.w_a pos.1) (fun _ => true) (fun _ => false)
          (natToBitsLSB C.w_a pos.1) (fun _ => false))) = pos.1 := by
        have hb1_fun : (fun u : Fin C.w_a => recKey54 (C.packRec2 (natToBits C.w_a pos.1) (fun _ => true)
            (fun _ => false) (natToBitsLSB C.w_a pos.1) (fun _ => false)) (Fin.castAdd C.w_v (Fin.castAdd 1 u))) =
            natToBits C.w_a pos.1 := by
          funext u
          change C.rec2B (C.packRec2 (natToBits C.w_a pos.1) (fun _ => true) (fun _ => false)
            (natToBitsLSB C.w_a pos.1) (fun _ => false)) u = natToBits C.w_a pos.1 u
          rw [C.rec2B_packRec2]
        dsimp only [keyB]; rw [hb1_fun]
        exact bitsToNat_natToBits_exact (lt_trans h1 C.m_lt_two_pow_w_a)
      rw [hf1, if_pos rfl] at hp
      simp only [hb1] at hp
      rcases hp with ⟨_, ha_eq, hc_eq⟩
      have hy_eq : y_out pos = Fin.append (natToBitsLSB C.w_a pos.1) (natToBitsLSB C.w_v (prefSum54 (C.extBeta α) ⟨pos.1, h1⟩)) := by
        dsimp only [y_out, k_in]
        funext u; refine Fin.addCases (fun ia => ?_) (fun ic => ?_) u
        · simp only [Fin.append_left]; exact congrFun ha_eq ia
        · simp only [Fin.append_right]; exact congrFun hc_eq ic
      rw [show unrouteSort C.d (sortTrace bitsToNat C.d true k_in) ys2 pos = y_out pos from rfl, hy_eq]
      dsimp only [k_in, Function.comp_apply, w2fRecAt]; rw [dif_pos h1, hk_append]
    · simp only [dif_neg h1] at hp; rw [dif_neg h1]
      by_cases h2 : pos.1 < C.m + C.N
      · simp only [dif_pos h2] at hp; rw [dif_pos h2]
        have hf0 : keyF (recKey54 (C.packRec2 (natToBits C.w_a (modeOf54 (C.extBeta α) (pos.1 - C.m))) (fun _ => false)
            (natToBits C.w_v (pos.1 - C.m)) (natToBitsLSB C.w_a C.m) (fun _ => false))) = false := by
          change C.rec2F (C.packRec2 (natToBits C.w_a (modeOf54 (C.extBeta α) (pos.1 - C.m))) (fun _ => false)
            (natToBits C.w_v (pos.1 - C.m)) (natToBitsLSB C.w_a C.m) (fun _ => false)) 0 = false
          rw [C.rec2F_packRec2]
        rw [hf0] at hp; simp only [Bool.false_eq_true, ↓reduceIte] at hp
        have hy_eq : y_out pos = Fin.append (natToBitsLSB C.w_a C.m) (fun _ => false) := by
          dsimp only [y_out, k_in]
          funext u; refine Fin.addCases (fun ia => ?_) (fun ic => ?_) u
          · simp only [Fin.append_left]; exact congrFun hp.1 ia
          · simp only [Fin.append_right]; exact congrFun hp.2 ic
        rw [show unrouteSort C.d (sortTrace bitsToNat C.d true k_in) ys2 pos = y_out pos from rfl, hy_eq]
        dsimp only [k_in, Function.comp_apply, w2fRecAt]; rw [dif_neg h1, dif_pos h2, hk_append]
      · simp only [dif_neg h2] at hp; rw [dif_neg h2]
        have hf0 : keyF (recKey54 (C.packRec2 (natToBits C.w_a C.m) (fun _ => false) (fun _ => false)
            (natToBitsLSB C.w_a C.m) (fun _ => false))) = false := by
          change C.rec2F (C.packRec2 (natToBits C.w_a C.m) (fun _ => false) (fun _ => false)
            (natToBitsLSB C.w_a C.m) (fun _ => false)) 0 = false
          rw [C.rec2F_packRec2]
        rw [hf0] at hp; simp only [Bool.false_eq_true, ↓reduceIte] at hp
        have hy_eq : y_out pos = Fin.append (natToBitsLSB C.w_a C.m) (fun _ => false) := by
          dsimp only [y_out, k_in]
          funext u; refine Fin.addCases (fun ia => ?_) (fun ic => ?_) u
          · simp only [Fin.append_left]; exact congrFun hp.1 ia
          · simp only [Fin.append_right]; exact congrFun hp.2 ic
        rw [show unrouteSort C.d (sortTrace bitsToNat C.d true k_in) ys2 pos = y_out pos from rfl, hy_eq]
        dsimp only [k_in, Function.comp_apply, w2fRecAt]; rw [dif_neg h1, dif_neg h2, hk_append]
  · funext idx; rcases finProdFinEquiv.surjective idx with ⟨⟨pos, u⟩, rfl⟩
    simp only [Function.comp_apply, packStage_arr2AllEmb, flatReg_apply']
    exact congrArg (fun f => f u) (congrArg (fun k => Fin.append k (ys2 pos)) (congrFun hsort_k pos).symm)
  · funext i; dsimp only [Function.comp_apply]; rw [C.packStage_trEmb, htr_k]
  · funext u; simp

noncomputable def pass2PrefixC : LayeredCircuit C.total :=
  C.initArr2C.seq (C.sort2C.seq (C.fillPref2C.seq C.sort2C.adj))

lemma pass2PrefixC_size :
    (C.pass2PrefixC.size : ℝ) ≤
      C.M * (2 * C.w_a + C.w_v + C.s + 1) +
        (C.m + C.N) * (30 * C.w_pos + 2 * C.w_a + 5 * C.w_v) +
        2 * (C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k2 + C.w_p2 + 1 : ℝ)) := by
  dsimp only [pass2PrefixC]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have h1 : (C.initArr2C.size : ℝ) ≤ C.M * (2 * C.w_a + C.w_v + C.s + 1) := by exact_mod_cast C.initArr2C_size
  have h2 := C.sort2C_size
  have h3 : (C.fillPref2C.size : ℝ) ≤ (C.m + C.N) * (30 * C.w_pos + 2 * C.w_a + 5 * C.w_v) := by
    exact_mod_cast C.fillPref2C_size
  push_cast at *
  linarith

lemma act_pass2PrefixC (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (A : Fin C.n → Qubits C.w_v) (K : Qubits C.w_v) (P : Fin C.n → Qubits C.w_v) :
    let L_bits := fun r : Fin C.N => natToBits C.s (modeOf54 (C.extBeta α) r.1)
    act C.pass2PrefixC.unitary (ket (C.packState A K L_bits P (fun _ _ => false) (fun _ => false))) =
      ket (C.packState A K L_bits P (C.x2Unrouted (C.extBeta α)) (fun _ => false)) := by
  dsimp only [pass2PrefixC]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  rw [C.act_initArr2C α hα, C.act_sort2C α, C.act_fillPref2C α hα, C.act_sort2C_adj α hα]

/-! #### 2.6 Uncomputation of Input Register `A` (`uncomputeAC`) & Full `pass2C` -/

abbrev modePosM (i : Fin C.n) : Fin C.M :=
  ⟨i.1, lt_of_lt_of_le (by dsimp [m]; omega) C.m_add_N_le_M⟩

lemma hdisj_c2_aLow (pos : Fin C.M) (i : Fin C.n) : ∀ a b, C.c2EmbLSB pos a ≠ C.aLowEmbLSB i b :=
  C.emb_disj_of_bounds _ _ C.offArr C.offTr 0 C.offK
    (C.slotSlice_in_arr pos (C.w_k2 + C.w_a) C.w_v C.hoff_c2)
    (C.aLowEmbLSB_bounds i)
    (Or.inr (by dsimp [offArr, offP, offL]; omega))

lemma hdisj_c2_scr (pos : Fin C.M) (off len : ℕ) (h : off + len ≤ C.lenScr) :
    ∀ a b, C.c2EmbLSB pos a ≠ C.scrEmb off len h b :=
  C.slotSlice_scr_disj pos (C.w_k2 + C.w_a) C.w_v off len C.hoff_c2 h

noncomputable def uncomputeAStepC (i : Fin C.n) : LayeredCircuit C.total :=
  if _h0 : i.1 = 0 then
    C.subInPlaceC C.w_v (C.c2EmbLSB (C.modePosM i)) (C.aLowEmbLSB i) (C.scrEmb 0 1 C.offScr_one)
      (C.hdisj_c2_aLow _ i) (C.hdisj_c2_scr _ 0 1 C.offScr_one) (C.hdisj_aLow_scr i 0 1 C.offScr_one)
  else
    let prev : Fin C.n := ⟨i.1 - 1, by omega⟩
    (C.subInPlaceC C.w_v (C.c2EmbLSB (C.modePosM i)) (C.aLowEmbLSB i) (C.scrEmb 0 1 C.offScr_one)
      (C.hdisj_c2_aLow _ i) (C.hdisj_c2_scr _ 0 1 C.offScr_one) (C.hdisj_aLow_scr i 0 1 C.offScr_one)).seq
      (C.addInPlaceC C.w_v (C.c2EmbLSB (C.modePosM prev)) (C.aLowEmbLSB i) (C.scrEmb 0 1 C.offScr_one)
        (C.hdisj_c2_aLow _ i) (C.hdisj_c2_scr _ 0 1 C.offScr_one) (C.hdisj_aLow_scr i 0 1 C.offScr_one))

lemma uncomputeAStepC_size (i : Fin C.n) : (C.uncomputeAStepC i).size ≤ 28 * C.w_v := by
  dsimp only [uncomputeAStepC]; split_ifs
  · rw [C.subInPlaceC_size]; omega
  · rw [LayeredCircuit.seq_size, C.subInPlaceC_size, C.addInPlaceC_size]; omega

noncomputable def uncomputeAC : LayeredCircuit C.total :=
  LayeredCircuit.seqList (List.ofFn C.uncomputeAStepC)

lemma uncomputeAC_size : C.uncomputeAC.size ≤ C.n * (28 * C.w_v) :=
  seqList_ofFn_size_le C.uncomputeAStepC (28 * C.w_v) C.uncomputeAStepC_size

lemma act_uncomputeAC (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (K : Qubits C.w_v) (L : Fin C.N → Qubits C.s) (P : Fin C.n → Qubits C.w_v) :
    let A_bits := fun i : Fin C.n => natToBitsLSB C.w_v (α i)
    act C.uncomputeAC.unitary (ket (C.packState A_bits K L P (C.x2Unrouted (C.extBeta α)) (fun _ => false))) =
      ket (C.packState (fun _ _ => false) K L P (C.x2Unrouted (C.extBeta α)) (fun _ => false)) := by
  intro A_bits
  let zAt : (t : ℕ) → t ≤ C.n → Qubits C.total := fun t _ =>
    C.packState (fun j => if j.1 < t then fun _ => false else A_bits j) K L P (C.x2Unrouted (C.extBeta α)) (fun _ => false)
  have hc2_read : ∀ (i : Fin C.n) A_cur,
      ((C.packState A_cur K L P (C.x2Unrouted (C.extBeta α)) (fun _ => false)) ∘ C.c2EmbLSB (C.modePosM i)) =
        natToBitsLSB C.w_v (prefSum54 α i) := by
    intro i A_cur; funext u
    simp only [Function.comp_apply, packState, c2EmbLSB, C.packStage_eval_slotSliceEmb]
    dsimp only [x2Unrouted, modePosM]
    have hlt : i.1 < C.m := by dsimp only [m]; omega
    rw [dif_pos hlt, C.packRec2_eval_c2, C.prefSum_extBeta_lt α i.1 i.isLt]
  have hrun := act_seqList_fin_ket C.uncomputeAStepC zAt fun t ht => by
    let cur : Fin C.n := ⟨t, ht⟩
    have hcur_eq : (if cur.1 < t then fun _ => false else A_bits cur) = A_bits cur := if_neg (by dsimp [cur]; omega)
    have hα_lt : α cur < 2 ^ C.w_v := C.sum_sub_lt_two_pow_w_v hα cur
    have hp_lt : prefSum54 α cur < 2 ^ C.w_v := C.prefSum_alpha_lt_two_pow hα cur
    dsimp only [uncomputeAStepC]
    by_cases ht0 : t = 0
    · have h0' : cur.1 = 0 := ht0
      rw [dif_pos h0', C.act_subInPlaceC _ _ _ _ _ _ _ _ (fun _ => by simp [zAt, packState])]
      rw [hc2_read]
      have hA_read : bitsToNatLSB (zAt t (le_of_lt ht) ∘ C.aLowEmbLSB cur) = α cur := by
        have hcomp : zAt t (le_of_lt ht) ∘ C.aLowEmbLSB cur = A_bits cur := by
          funext u; simp only [Function.comp_apply, zAt, packState, packStage_aLowEmbLSB, hcur_eq]
        rw [hcomp]; exact bitsToNatLSB_natToBitsLSB hα_lt
      rw [hA_read, bitsToNatLSB_natToBitsLSB hp_lt]
      have hpref0 : prefSum54 α cur = α cur := by
        dsimp only [prefSum54]
        rw [Finset.sum_eq_single cur]
        · simp
        · intro j _ hj'
          rw [if_neg]; intro hle
          exact hj' (Fin.ext (by have := Fin.le_iff_val_le_val.mp hle; dsimp [cur] at *; omega))
        · intro h; exact absurd (Finset.mem_univ cur) h
      rw [hpref0, show 2 ^ C.w_v + α cur - α cur = 2 ^ C.w_v by omega,
        ← natToBitsLSB_mod_eq', Nat.mod_self, natToBitsLSB_zero']
      dsimp only [zAt, packState]
      rw [C.packStage_update_aLowEmbLSB]
      congr 2; funext j
      by_cases hj : j = cur
      · subst hj; rw [Function.update_self, if_pos (by dsimp [cur]; omega)]
      · rw [Function.update_of_ne hj]
        have hiff : j.1 < t ↔ j.1 < t + 1 := by
          have := Fin.val_ne_of_ne hj; dsimp [cur] at this; omega
        simp [hiff]
    · have h0' : cur.1 ≠ 0 := ht0
      let prev : Fin C.n := ⟨cur.1 - 1, by omega⟩
      have hp_prev_lt : prefSum54 α prev < 2 ^ C.w_v := C.prefSum_alpha_lt_two_pow hα prev
      have hsucc : prefSum54 α cur = prefSum54 α prev + α cur := by
        have h1 : cur = ⟨(t - 1) + 1, by omega⟩ := Fin.ext (by dsimp [cur]; omega)
        have h2 : prev = ⟨t - 1, by omega⟩ := rfl
        rw [h1, h2, C.prefSum_alpha_succ α (t - 1) (by omega)]
      rw [dif_neg h0', LayeredCircuit.seq_unitary, act_mul]
      rw [C.act_subInPlaceC _ _ _ _ _ _ _ _ (fun _ => by simp [zAt, packState]), hc2_read]
      have hA_read1 : bitsToNatLSB (zAt t (le_of_lt ht) ∘ C.aLowEmbLSB cur) = α cur := by
        have hcomp : zAt t (le_of_lt ht) ∘ C.aLowEmbLSB cur = A_bits cur := by
          funext u; simp only [Function.comp_apply, zAt, packState, packStage_aLowEmbLSB, hcur_eq]
        rw [hcomp]; exact bitsToNatLSB_natToBitsLSB hα_lt
      rw [hA_read1, bitsToNatLSB_natToBitsLSB hp_lt]
      dsimp only [zAt, packState]
      rw [C.packStage_update_aLowEmbLSB]
      rw [C.act_addInPlaceC _ _ _ _ _ _ _ _ (fun _ => by simp), hc2_read]
      have hA_read2 : bitsToNatLSB (C.packState
            (Function.update (fun j : Fin C.n => if j.1 < t then fun _ => false else A_bits j) cur
              (natToBitsLSB C.w_v (2 ^ C.w_v + α cur - prefSum54 α cur)))
            K L P (C.x2Unrouted (C.extBeta α)) (fun _ => false) ∘ C.aLowEmbLSB cur) =
          (2 ^ C.w_v + α cur - prefSum54 α cur) % 2 ^ C.w_v := by
        have hcomp : C.packState (Function.update (fun j : Fin C.n => if j.1 < t then fun _ => false else A_bits j) cur
              (natToBitsLSB C.w_v (2 ^ C.w_v + α cur - prefSum54 α cur)))
            K L P (C.x2Unrouted (C.extBeta α)) (fun _ => false) ∘ C.aLowEmbLSB cur =
            natToBitsLSB C.w_v (2 ^ C.w_v + α cur - prefSum54 α cur) := by
          funext u; simp only [Function.comp_apply, packState, packStage_aLowEmbLSB, Function.update_self]
        rw [hcomp, bitsToNatLSB_natToBitsLSB_mod']
      rw [hA_read2, bitsToNatLSB_natToBitsLSB hp_prev_lt]
      have hzero_val : natToBitsLSB C.w_v (prefSum54 α prev + (2 ^ C.w_v + α cur - prefSum54 α cur) % 2 ^ C.w_v) =
          fun _ => false := by
        rw [← natToBitsLSB_mod_eq', Nat.add_mod_mod,
          show prefSum54 α prev + (2 ^ C.w_v + α cur - prefSum54 α cur) = 2 ^ C.w_v by rw [hsucc]; omega,
          Nat.mod_self, natToBitsLSB_zero']
      rw [hzero_val]
      rw [C.packStage_update_aLowEmbLSB, Function.update_idem]
      congr 2; funext j
      by_cases hj : j = cur
      · subst hj; rw [Function.update_self, if_pos (by dsimp [cur]; omega)]
      · rw [Function.update_of_ne hj]
        have hiff : j.1 < t ↔ j.1 < t + 1 := by
          have := Fin.val_ne_of_ne hj; dsimp [cur] at this; omega
        simp [hiff]
  have hz0 : zAt 0 (Nat.zero_le C.n) = C.packState A_bits K L P (C.x2Unrouted (C.extBeta α)) (fun _ => false) := by
    dsimp only [zAt]; rfl
  have hzn : zAt C.n le_rfl = C.packState (fun _ _ => false) K L P (C.x2Unrouted (C.extBeta α)) (fun _ => false) := by
    dsimp only [zAt]; congr 1; funext j; rw [if_pos j.isLt]
  rw [hz0, hzn] at hrun
  exact hrun

noncomputable def pass2C : LayeredCircuit C.total :=
  C.pass2PrefixC.seq (C.uncomputeAC.seq C.pass2PrefixC.adj)

lemma pass2C_size :
    (C.pass2C.size : ℝ) ≤
      2 * (C.M * (2 * C.w_a + C.w_v + C.s + 1) +
        (C.m + C.N) * (30 * C.w_pos + 2 * C.w_a + 5 * C.w_v) +
        2 * (C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k2 + C.w_p2 + 1 : ℝ))) +
        C.n * (28 * C.w_v) := by
  dsimp only [pass2C]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have h1 := C.pass2PrefixC_size
  have h2 : (C.uncomputeAC.size : ℝ) ≤ C.n * (28 * C.w_v) := by exact_mod_cast C.uncomputeAC_size
  push_cast at *
  linarith

lemma act_pass2C (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N) :
    let A_bits := fun i : Fin C.n => natToBitsLSB C.w_v (α i)
    let K_bits := natToBitsLSB C.w_v (∑ i : Fin C.n, α i)
    let L_bits := fun r : Fin C.N => natToBits C.s (modeOf54 (C.extBeta α) r.1)
    act C.pass2C.unitary
        (ket (C.packState A_bits K_bits L_bits (fun _ _ => false) (fun _ _ => false) (fun _ => false))) =
      ket (C.packState (fun _ _ => false) K_bits L_bits (fun _ _ => false) (fun _ _ => false) (fun _ => false)) := by
  intro A_bits K_bits L_bits
  have hpref_bwd := act_adj_ket_of_act_ket _
    (C.act_pass2PrefixC α hα (fun _ _ => false) K_bits (fun _ _ => false))
  dsimp only [pass2C]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  rw [C.act_pass2PrefixC α hα A_bits K_bits (fun _ _ => false), C.act_uncomputeAC α hα, hpref_bwd]

end OccCtx

end QuantumLTF.Membership.Supplement.StageA


/-! ### Pass 3 (`encodeSymAllC`), `stageAC`, Gate-Count Bounds, & Root `solution` -/

namespace QuantumLTF.Membership.Supplement.StageA

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open Thm49Primitives Thm410Router Cslib.BitonicSort

namespace OccCtx

variable (C : OccCtx)

/-! #### 3.1 Pass-3 Particle-Symbol Encoding (`encodeSymAllC`) -/

abbrev symAncEmb : Fin (C.s - 1) ↪ Fin C.total := C.scrEmb 0 (C.s - 1) C.offScr_sym

lemma hLA_sym (r : Fin C.N) : ∀ i j, C.lSlotEmb r i ≠ C.symAncEmb j :=
  C.emb_disj_of_bounds _ _ C.offL C.offP C.offScr (C.offScr + (C.s - 1))
    (C.lSlotEmb_bounds r) (C.scrEmb_bounds 0 (C.s - 1) C.offScr_sym)
    (Or.inl (by dsimp [offScr, offTr, offArr, offP]; omega))

noncomputable def encodeSymAllC : LayeredCircuit C.total :=
  LayeredCircuit.seqList (List.ofFn fun r : Fin C.N => C.encodeSymC r C.symAncEmb (C.hLA_sym r))

lemma encodeSymAllC_size : C.encodeSymAllC.size ≤ C.N * (13 * C.s) :=
  seqList_ofFn_size_le _ (13 * C.s) fun r => C.encodeSymC_size r C.symAncEmb (C.hLA_sym r)

lemma act_encodeSymAllC (α : Fin C.n → ℕ) (hα : ∑ i : Fin C.n, α i ≤ C.N)
    (K : Qubits C.w_v) :
    let l : Fin C.N → Fin C.m := fun r =>
      ⟨modeOf54 (C.extBeta α) r.1, C.O.modeOf_lt (C.extBeta α) (C.extBeta_sum hα) r.isLt⟩
    let L_in : Fin C.N → Qubits C.s := fun r => natToBits C.s (l r).1
    let L_out : Fin C.N → Qubits C.s := fun r => particleSym54 C.n C.s (l r)
    act C.encodeSymAllC.unitary
        (ket (C.packState (fun _ _ => false) K L_in (fun _ _ => false) (fun _ _ => false) (fun _ => false))) =
      ket (C.packState (fun _ _ => false) K L_out (fun _ _ => false) (fun _ _ => false) (fun _ => false)) := by
  intro l L_in L_out
  let zAt : (t : ℕ) → t ≤ C.N → Qubits C.total := fun t _ =>
    C.packState (fun _ _ => false) K (fun r => if r.1 < t then L_out r else L_in r)
      (fun _ _ => false) (fun _ _ => false) (fun _ => false)
  have hrun := act_seqList_fin_ket (fun r : Fin C.N => C.encodeSymC r C.symAncEmb (C.hLA_sym r)) zAt fun t ht => by
    let r : Fin C.N := ⟨t, ht⟩
    have hr_not : ¬ r.1 < t := by dsimp [r]; omega
    rw [C.act_encodeSymC r C.symAncEmb (C.hLA_sym r) _ (l r)]
    · dsimp only [zAt, packState]
      rw [C.packStage_update_lSlotEmb]
      refine congrArg ket (congrArg (fun L' =>
        C.packStage (fun _ _ => false) K L' (fun _ _ => false) (fun _ _ => false) (fun _ => false) (fun _ => false))
        (funext fun j => ?_))
      by_cases hj : j = r
      · subst hj; rw [Function.update_self, if_pos (by dsimp [r]; omega)]
      · rw [Function.update_of_ne hj]
        have hiff : j.1 < t ↔ j.1 < t + 1 := by
          have := Fin.val_ne_of_ne hj; dsimp [r] at this; omega
        simp [hiff]
    · funext u; simp only [Function.comp_apply, zAt, packState, packStage_lSlotEmb, if_neg hr_not]; rfl
    · intro k; simp [zAt, packState, symAncEmb]
  have hz0 : zAt 0 (Nat.zero_le C.N) =
      C.packState (fun _ _ => false) K L_in (fun _ _ => false) (fun _ _ => false) (fun _ => false) := by
    dsimp only [zAt]; rfl
  have hzN : zAt C.N le_rfl =
      C.packState (fun _ _ => false) K L_out (fun _ _ => false) (fun _ _ => false) (fun _ => false) := by
    dsimp only [zAt]; congr 1; funext r; simp [r.isLt]
  rw [hz0, hzN] at hrun
  exact hrun

/-! #### 3.2 Full Stage A Circuit & Gate-Count Bound -/

noncomputable def stageAC : LayeredCircuit C.total :=
  C.pass1C.seq (C.pass2C.seq C.encodeSymAllC)

lemma s_pos' : 1 ≤ C.s := by dsimp only [s]; omega

lemma d_le_clog : C.d ≤ Nat.clog 2 ((C.K + 1) * (C.n + 1) + 2) + 1 := by
  dsimp only [d]
  have hle : C.m + C.N ≤ (C.K + 1) * (C.n + 1) + 2 := by
    have h1 : C.K ≤ C.K * C.n := Nat.le_mul_of_pos_right C.K C.hn
    have hmul : (C.K + 1) * (C.n + 1) = C.K * C.n + C.K + C.n + 1 := by ring
    dsimp only [m, N]
    omega
  exact le_trans (Nat.clog_mono_right 2 hle) (Nat.le_succ _)

lemma s_le_clog : C.s ≤ Nat.clog 2 ((C.K + 1) * (C.n + 1) + 2) + 1 := by
  dsimp only [s]
  have hle : C.n ≤ (C.K + 1) * (C.n + 1) + 2 := by
    have h1 : 1 * (C.n + 1) ≤ (C.K + 1) * (C.n + 1) := Nat.mul_le_mul_right _ (by have := C.hK; omega)
    omega
  exact Nat.add_le_add_right (Nat.clog_mono_right 2 hle) 1

lemma w_v_le_clog : C.w_v ≤ Nat.clog 2 ((C.K + 1) * (C.n + 1) + 2) + 1 := by
  dsimp only [w_v]
  have hle : 2 * C.K + 1 ≤ (C.K + 1) * (C.n + 1) + 2 := by
    have h1 : (C.K + 1) * 2 ≤ (C.K + 1) * (C.n + 1) := Nat.mul_le_mul_left _ (by have := C.hn; omega)
    omega
  exact le_trans (Nat.clog_mono_right 2 hle) (Nat.le_succ _)

lemma M_le_two_mul_m_add_N : C.M ≤ 2 * (C.m + C.N) := by
  rw [C.M_eq]; dsimp only [d]
  have hge4 : 4 ≤ C.m + C.N := by have := C.hn; have := C.hK; dsimp only [m, N]; omega
  have hd1 : 1 ≤ Nat.clog 2 (C.m + C.N) := by
    have := C.d_ge_two; dsimp only [d] at this; omega
  have hlt : 2 ^ (Nat.clog 2 (C.m + C.N) - 1) < C.m + C.N := by
    by_contra hnot
    have hle : C.m + C.N ≤ 2 ^ (Nat.clog 2 (C.m + C.N) - 1) := by omega
    have hclog := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr hle
    omega
  have hpow : 2 ^ Nat.clog 2 (C.m + C.N) = 2 * 2 ^ (Nat.clog 2 (C.m + C.N) - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hd1]
  omega

lemma m_add_N_le_two_mul : C.m + C.N ≤ 2 * (C.n + C.K * C.s) := by
  have hn := C.hn; have hs := C.s_pos'
  have hks : C.K ≤ C.K * C.s := Nat.le_mul_of_pos_right C.K hs
  dsimp only [m, N]
  omega

lemma M_le_four_mul : C.M ≤ 4 * (C.n + C.K * C.s) :=
  le_trans C.M_le_two_mul_m_add_N (by have := C.m_add_N_le_two_mul; omega)

lemma stageAC_size :
    ((C.stageAC.size : ℕ) : ℝ) ≤
      (704 * C.R.C_sort + 1000) * ((C.n + C.K * C.s : ℕ) : ℝ) *
        ((Nat.clog 2 ((C.K + 1) * (C.n + 1) + 2) + 1 : ℕ) : ℝ) ^ 3 := by
  set L : ℕ := Nat.clog 2 ((C.K + 1) * (C.n + 1) + 2) + 1
  have hL1 : 1 ≤ L := by dsimp [L]; omega
  have hsL : C.s ≤ L := C.s_le_clog
  have hwvL : C.w_v ≤ L := C.w_v_le_clog
  have hdL : C.d ≤ L := C.d_le_clog
  have hwaL : C.w_a ≤ 2 * L := by dsimp only [w_a]; omega
  have hwposL : C.w_pos ≤ 3 * L := by dsimp only [w_pos]; omega
  have hk1L : C.w_k1 + C.w_p1 + 1 ≤ 6 * L := by dsimp only [w_k1, w_p1, w_a]; omega
  have hk2L : C.w_k2 + C.w_p2 + 1 ≤ 8 * L := by dsimp only [w_k2, w_p2, w_a]; omega
  have hmN := C.m_add_N_le_two_mul
  have hM := C.M_le_four_mul
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by linarith only [hLr]
  have hL2 : (L : ℝ) ≤ (L : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hLr hL0; rwa [mul_one, ← sq] at this
  have hL3 : (L : ℝ) ≤ (L : ℝ) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hLr (sq_nonneg (L : ℝ))
    rw [mul_one] at hmul
    exact le_trans hL2 (by simpa [pow_succ] using hmul)
  have hR_nn : 0 ≤ ((C.n + C.K * C.s : ℕ) : ℝ) := Nat.cast_nonneg _
  have hCsort_pos : 0 < C.R.C_sort := C.R.hC_sort_pos
  have hnr : ((C.n : ℕ) : ℝ) ≤ ((C.n + C.K * C.s : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right C.n (C.K * C.s)
  have hNsr : ((C.N * C.s : ℕ) : ℝ) ≤ 2 * ((C.n + C.K * C.s : ℕ) : ℝ) := by
    have : C.N * C.s = 2 * (C.K * C.s) := by dsimp only [N]; ring
    rw [this]
    exact_mod_cast (by omega : 2 * (C.K * C.s) ≤ 2 * (C.n + C.K * C.s))
  have hmNr : ((C.m : ℝ) + C.N) ≤ 2 * ((C.n + C.K * C.s : ℕ) : ℝ) := by exact_mod_cast hmN
  have hMr : ((C.M : ℕ) : ℝ) ≤ 4 * ((C.n + C.K * C.s : ℕ) : ℝ) := by exact_mod_cast hM
  have h2dr : (2 ^ C.d : ℝ) ≤ 4 * ((C.n + C.K * C.s : ℕ) : ℝ) := by
    exact_mod_cast (by rw [← C.M_eq]; exact hM : 2 ^ C.d ≤ 4 * (C.n + C.K * C.s))
  have hd1r : ((C.d + 1 : ℝ) ^ 2) ≤ 4 * (L : ℝ) ^ 2 := by
    have h1 : (C.d + 1 : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast (by omega : C.d + 1 ≤ 2 * L)
    have h0 : 0 ≤ (C.d + 1 : ℝ) := by positivity
    calc (C.d + 1 : ℝ) ^ 2 = (C.d + 1 : ℝ) * (C.d + 1 : ℝ) := sq _
      _ ≤ (2 * (L : ℝ)) * (2 * (L : ℝ)) := mul_le_mul h1 h1 h0 (by linarith only [hL0])
      _ = 4 * (L : ℝ) ^ 2 := by ring
  have hwvr : (C.w_v : ℝ) ≤ (L : ℝ) := by exact_mod_cast hwvL
  have hsr : (C.s : ℝ) ≤ (L : ℝ) := by exact_mod_cast hsL
  have hwar : (C.w_a : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hwaL
  have hwposr : (C.w_pos : ℝ) ≤ 3 * (L : ℝ) := by exact_mod_cast hwposL
  have hk1r : (C.w_k1 + C.w_p1 + 1 : ℝ) ≤ 6 * (L : ℝ) := by exact_mod_cast hk1L
  have hk2r : (C.w_k2 + C.w_p2 + 1 : ℝ) ≤ 8 * (L : ℝ) := by exact_mod_cast hk2L
  have hnwv : ((C.n : ℕ) : ℝ) * (C.w_v : ℝ) ≤ ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 :=
    le_trans (mul_le_mul hnr hwvr (Nat.cast_nonneg _) hR_nn) (mul_le_mul_of_nonneg_left hL3 hR_nn)
  have hMav : (C.M : ℝ) * ((C.w_a : ℝ) + C.w_v) ≤ 12 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
    have h1 : (C.M : ℝ) * ((C.w_a : ℝ) + C.w_v) ≤ (4 * ((C.n + C.K * C.s : ℕ) : ℝ)) * (3 * (L : ℝ)) :=
      mul_le_mul hMr (by linarith only [hwar, hwvr]) (by positivity) (by linarith only [hR_nn])
    have hmul : 12 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ≤ 12 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hL3 (by linarith only [hR_nn])
    linarith only [h1, hmul, show (4 * ((C.n + C.K * C.s : ℕ) : ℝ)) * (3 * (L : ℝ)) =
      12 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) from by ring]
  have hmN_p1 : ((C.m : ℝ) + C.N) * (33 * C.w_a + 30 * C.w_pos + 2 * C.w_v + 24) ≤
      364 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
    have h1 : (33 * (C.w_a : ℝ) + 30 * C.w_pos + 2 * C.w_v + 24) ≤ 182 * (L : ℝ) := by
      linarith only [hwar, hwposr, hwvr, hLr]
    have h2 : ((C.m : ℝ) + C.N) * (33 * C.w_a + 30 * C.w_pos + 2 * C.w_v + 24) ≤
        (2 * ((C.n + C.K * C.s : ℕ) : ℝ)) * (182 * (L : ℝ)) :=
      mul_le_mul hmNr h1 (by positivity) (by linarith only [hR_nn])
    have hmul : 364 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ≤ 364 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hL3 (by linarith only [hR_nn])
    linarith only [h2, hmul, show (2 * ((C.n + C.K * C.s : ℕ) : ℝ)) * (182 * (L : ℝ)) =
      364 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) from by ring]
  have hsort1_r : C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k1 + C.w_p1 + 1 : ℝ) ≤
      96 * C.R.C_sort * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
    have h1 : (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) ≤ (4 * ((C.n + C.K * C.s : ℕ) : ℝ)) * (4 * (L : ℝ) ^ 2) :=
      mul_le_mul h2dr hd1r (by positivity) (by linarith only [hR_nn])
    have h2 : (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k1 + C.w_p1 + 1 : ℝ) ≤
        (4 * ((C.n + C.K * C.s : ℕ) : ℝ) * (4 * (L : ℝ) ^ 2)) * (6 * (L : ℝ)) :=
      mul_le_mul h1 hk1r (by positivity) (by positivity)
    have h3 : C.R.C_sort * ((2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k1 + C.w_p1 + 1 : ℝ)) ≤
        C.R.C_sort * ((4 * ((C.n + C.K * C.s : ℕ) : ℝ) * (4 * (L : ℝ) ^ 2)) * (6 * (L : ℝ))) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hCsort_pos)
    linarith only [h3, show C.R.C_sort * ((4 * ((C.n + C.K * C.s : ℕ) : ℝ) * (4 * (L : ℝ) ^ 2)) * (6 * (L : ℝ))) =
      96 * C.R.C_sort * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 from by ring,
      show C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k1 + C.w_p1 + 1 : ℝ) =
      C.R.C_sort * ((2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k1 + C.w_p1 + 1 : ℝ)) from by ring]
  have hM2av : (C.M : ℝ) * (2 * C.w_a + C.w_v + C.s + 1) ≤
      28 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
    have h1 : (2 * (C.w_a : ℝ) + C.w_v + C.s + 1) ≤ 7 * (L : ℝ) := by
      linarith only [hwar, hwvr, hsr, hLr]
    have h2 : (C.M : ℝ) * (2 * C.w_a + C.w_v + C.s + 1) ≤ (4 * ((C.n + C.K * C.s : ℕ) : ℝ)) * (7 * (L : ℝ)) :=
      mul_le_mul hMr h1 (by positivity) (by linarith only [hR_nn])
    have hmul : 28 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ≤ 28 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hL3 (by linarith only [hR_nn])
    linarith only [h2, hmul, show (4 * ((C.n + C.K * C.s : ℕ) : ℝ)) * (7 * (L : ℝ)) =
      28 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) from by ring]
  have hmN_p2 : ((C.m : ℝ) + C.N) * (30 * C.w_pos + 2 * C.w_a + 5 * C.w_v) ≤
      198 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
    have h1 : (30 * (C.w_pos : ℝ) + 2 * C.w_a + 5 * C.w_v) ≤ 99 * (L : ℝ) := by
      linarith only [hwposr, hwar, hwvr]
    have h2 : ((C.m : ℝ) + C.N) * (30 * C.w_pos + 2 * C.w_a + 5 * C.w_v) ≤
        (2 * ((C.n + C.K * C.s : ℕ) : ℝ)) * (99 * (L : ℝ)) :=
      mul_le_mul hmNr h1 (by positivity) (by linarith only [hR_nn])
    have hmul : 198 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ≤ 198 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hL3 (by linarith only [hR_nn])
    linarith only [h2, hmul, show (2 * ((C.n + C.K * C.s : ℕ) : ℝ)) * (99 * (L : ℝ)) =
      198 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) from by ring]
  have hsort2_r : C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k2 + C.w_p2 + 1 : ℝ) ≤
      128 * C.R.C_sort * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
    have h1 : (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) ≤ (4 * ((C.n + C.K * C.s : ℕ) : ℝ)) * (4 * (L : ℝ) ^ 2) :=
      mul_le_mul h2dr hd1r (by positivity) (by linarith only [hR_nn])
    have h2 : (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k2 + C.w_p2 + 1 : ℝ) ≤
        (4 * ((C.n + C.K * C.s : ℕ) : ℝ) * (4 * (L : ℝ) ^ 2)) * (8 * (L : ℝ)) :=
      mul_le_mul h1 hk2r (by positivity) (by positivity)
    have h3 : C.R.C_sort * ((2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k2 + C.w_p2 + 1 : ℝ)) ≤
        C.R.C_sort * ((4 * ((C.n + C.K * C.s : ℕ) : ℝ) * (4 * (L : ℝ) ^ 2)) * (8 * (L : ℝ))) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hCsort_pos)
    linarith only [h3, show C.R.C_sort * ((4 * ((C.n + C.K * C.s : ℕ) : ℝ) * (4 * (L : ℝ) ^ 2)) * (8 * (L : ℝ))) =
      128 * C.R.C_sort * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 from by ring,
      show C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k2 + C.w_p2 + 1 : ℝ) =
      C.R.C_sort * ((2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k2 + C.w_p2 + 1 : ℝ)) from by ring]
  have hwv_term : (C.w_v : ℝ) ≤ ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
    have hn1 : (1 : ℝ) ≤ ((C.n + C.K * C.s : ℕ) : ℝ) := by
      exact_mod_cast (by have := C.hn; omega : 1 ≤ C.n + C.K * C.s)
    calc (C.w_v : ℝ) ≤ (L : ℝ) := hwvr
      _ ≤ (L : ℝ) ^ 3 := hL3
      _ = 1 * (L : ℝ) ^ 3 := (one_mul _).symm
      _ ≤ ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hn1 (pow_nonneg hL0 3)
  have hNs_term : (C.N : ℝ) * (C.s : ℝ) ≤ 2 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
    have h1 : (C.N : ℝ) * (C.s : ℝ) = ((C.N * C.s : ℕ) : ℝ) := by push_cast; ring
    rw [h1]
    have hL1_3 : (1 : ℝ) ≤ (L : ℝ) ^ 3 := le_trans hLr hL3
    have h2 : ((C.N * C.s : ℕ) : ℝ) ≤ 2 * ((C.n + C.K * C.s : ℕ) : ℝ) := hNsr
    have h3 : 2 * ((C.n + C.K * C.s : ℕ) : ℝ) * 1 ≤ 2 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hL1_3 (by linarith only [hR_nn])
    linarith only [h2, h3]
  have hp1 := C.pass1C_size
  have hp2 := C.pass2C_size
  have hp3 : (C.encodeSymAllC.size : ℝ) ≤ (C.N : ℝ) * (13 * C.s) := by exact_mod_cast C.encodeSymAllC_size
  rw [show (2 : ℝ) * C.n * (15 * C.w_v) = 30 * ((C.n : ℝ) * C.w_v) by ring,
      show (2 : ℝ) * C.M * (C.w_a + C.w_v) = 2 * ((C.M : ℝ) * (C.w_a + C.w_v)) by ring,
      show (2 : ℝ) * C.N * C.s = 2 * ((C.N : ℝ) * C.s) by ring] at hp1
  rw [show (C.n : ℝ) * (28 * C.w_v) = 28 * ((C.n : ℝ) * C.w_v) by ring] at hp2
  rw [show (C.N : ℝ) * (13 * C.s) = 13 * ((C.N : ℝ) * C.s) by ring] at hp3
  have hp1' : (C.pass1C.size : ℝ) ≤
      (192 * C.R.C_sort + 423) * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
    calc (C.pass1C.size : ℝ)
        ≤ 30 * ((C.n : ℝ) * C.w_v) + 2 * ((C.M : ℝ) * (C.w_a + C.w_v)) + C.w_v + 2 * ((C.N : ℝ) * C.s) +
            ((C.m : ℝ) + C.N) * (33 * C.w_a + 30 * C.w_pos + 2 * C.w_v + 24) +
            2 * (C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k1 + C.w_p1 + 1 : ℝ)) := hp1
      _ ≤ 30 * (((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3) +
            2 * (12 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3) +
            (((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3) +
            2 * (2 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3) +
            364 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 +
            2 * (96 * C.R.C_sort * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3) := by
          refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left hnwv (by norm_num))
            (mul_le_mul_of_nonneg_left hMav (by norm_num)))
            hwv_term)
            (mul_le_mul_of_nonneg_left hNs_term (by norm_num)))
            hmN_p1)
            (mul_le_mul_of_nonneg_left hsort1_r (by norm_num))
      _ = (192 * C.R.C_sort + 423) * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by ring
  have hp2' : (C.pass2C.size : ℝ) ≤
      (512 * C.R.C_sort + 480) * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
    calc (C.pass2C.size : ℝ)
        ≤ 2 * ((C.M : ℝ) * (2 * C.w_a + C.w_v + C.s + 1) +
            ((C.m : ℝ) + C.N) * (30 * C.w_pos + 2 * C.w_a + 5 * C.w_v) +
            2 * (C.R.C_sort * (2 ^ C.d : ℝ) * ((C.d + 1 : ℝ) ^ 2) * (C.w_k2 + C.w_p2 + 1 : ℝ))) +
            28 * ((C.n : ℝ) * C.w_v) := hp2
      _ ≤ 2 * (28 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 +
            198 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 +
            2 * (128 * C.R.C_sort * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3)) +
            28 * (((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3) := by
          refine add_le_add (mul_le_mul_of_nonneg_left
            (add_le_add (add_le_add hM2av hmN_p2) (mul_le_mul_of_nonneg_left hsort2_r (by norm_num))) (by norm_num))
            (mul_le_mul_of_nonneg_left hnwv (by norm_num))
      _ = (512 * C.R.C_sort + 480) * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by ring
  have hp3' : (C.encodeSymAllC.size : ℝ) ≤
      26 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
    calc (C.encodeSymAllC.size : ℝ) ≤ 13 * ((C.N : ℝ) * C.s) := hp3
      _ ≤ 13 * (2 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hNs_term (by norm_num)
      _ = 26 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by ring
  have hRL_nn : 0 ≤ ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by positivity
  calc ((C.stageAC.size : ℕ) : ℝ)
      = (C.pass1C.size : ℝ) + ((C.pass2C.size : ℝ) + (C.encodeSymAllC.size : ℝ)) := by
          dsimp only [stageAC]; rw [LayeredCircuit.seq_size, LayeredCircuit.seq_size, Nat.cast_add, Nat.cast_add]
    _ ≤ (192 * C.R.C_sort + 423) * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 +
          ((512 * C.R.C_sort + 480) * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 +
            26 * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3) := add_le_add hp1' (add_le_add hp2' hp3')
    _ = (704 * C.R.C_sort + 929) * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by ring
    _ ≤ (704 * C.R.C_sort + 1000) * ((C.n + C.K * C.s : ℕ) : ℝ) * (L : ℝ) ^ 3 := by
          have hcoef : 704 * C.R.C_sort + 929 ≤ 704 * C.R.C_sort + 1000 := by norm_num
          simpa [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hRL_nn

end OccCtx

end QuantumLTF.Membership.Supplement.StageA

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.StageA Thm49Primitives

theorem solution :
    ∃ (C_occ : ℝ) (K_occ : ℕ), 0 < C_occ ∧
      ∀ (n K D q : ℕ), 1 ≤ n → 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
        let s := Nat.clog 2 n + 1
        ∃ (e_occ : ℕ) (partEmb_occ : Fin (2 * K * s) ↪ Fin (n * q + e_occ))
          (degState_occ : ℕ → Qubits (n * q + e_occ))
          (V_occ : Circuit gates12 (n * q + e_occ)),
          ((V_occ.size : ℕ) : ℝ) ≤
            C_occ * n * (q + Nat.clog 2 (n * D + 2) + 1) +
            C_occ * (n + K * s) * (Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1) ^ K_occ ∧
          ∀ (α : Fin n → ℕ), K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K →
            ∃ (l : Fin (2 * K) → Fin (n + 1)),
              Monotone l ∧
              (∀ i : Fin n, (Finset.univ.filter fun p => l p = ⟨i.1, by omega⟩).card = α i) ∧
              (Finset.univ.filter fun p => l p = ⟨n, Nat.lt_succ_self n⟩).card = 2 * K - ∑ i, α i ∧
              act V_occ.unitary (padKet e_occ (ket (flatReg n q fun i => natToBits q (α i)))) =
                embedPartAndDeg54 partEmb_occ
                  (ket (flatReg (2 * K) s fun p => particleSym54 n s (l p)))
                  (degState_occ (∑ i, α i)) := by
  obtain ⟨O⟩ := QuantumLTF.Membership.Supplement.occ_arith_54
  obtain ⟨R⟩ := QuantumLTF.Membership.Supplement.bitonic_routing_54
  refine ⟨704 * R.C_sort + 1000, 3, by have := R.hC_sort_pos; linarith, ?_⟩
  intro n K D q hn hK hD hq
  dsimp only
  let C : OccCtx := ⟨O, R, n, K, D, q, hn, hK, hD, hq⟩
  let degState_occ : ℕ → Qubits C.total := fun k =>
    C.packState (fun _ _ => false) (natToBitsLSB C.w_v k)
      (fun _ _ => false) (fun _ _ => false) (fun _ _ => false) (fun _ => false)
  let V_occ : Circuit gates12 C.total := C.stageAC.toCircuit
  refine ⟨C.e_occ, C.partEmb, degState_occ, V_occ, ?_, ?_⟩
  · have hsz : V_occ.size = C.stageAC.size := rfl
    rw [hsz]
    have h0 : 0 ≤ (704 * R.C_sort + 1000) * (n : ℝ) * ((q : ℝ) + Nat.clog 2 (n * D + 2) + 1) := by
      have := R.hC_sort_pos; positivity
    have hst := C.stageAC_size
    have hst' : (C.stageAC.size : ℝ) ≤
        (704 * R.C_sort + 1000) * ((n : ℝ) + (K : ℝ) * ((Nat.clog 2 n + 1 : ℕ) : ℝ)) *
          ((Nat.clog 2 ((K + 1) * (n + 1) + 2) : ℝ) + 1) ^ 3 := by
      refine le_trans hst (le_of_eq ?_)
      dsimp only [C, OccCtx.s]
      push_cast
      ring
    calc ((C.stageAC.size : ℕ) : ℝ)
        ≤ (704 * R.C_sort + 1000) * ((n : ℝ) + (K : ℝ) * ((Nat.clog 2 n + 1 : ℕ) : ℝ)) *
            ((Nat.clog 2 ((K + 1) * (n + 1) + 2) : ℝ) + 1) ^ 3 := hst'
      _ ≤ (704 * R.C_sort + 1000) * (n : ℝ) * ((q : ℝ) + Nat.clog 2 (n * D + 2) + 1) +
            (704 * R.C_sort + 1000) * ((n : ℝ) + (K : ℝ) * ((Nat.clog 2 n + 1 : ℕ) : ℝ)) *
              ((Nat.clog 2 ((K + 1) * (n + 1) + 2) : ℝ) + 1) ^ 3 := le_add_of_nonneg_left h0
      _ = _ := by push_cast; ring
  · intro α ⟨_, hα⟩
    let l : Fin (2 * K) → Fin (n + 1) := fun p =>
      ⟨modeOf54 (C.extBeta α) p.1, O.modeOf_lt (C.extBeta α) (C.extBeta_sum hα) p.isLt⟩
    refine ⟨l, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      exact Fin.le_iff_val_le_val.mpr (O.modeOf_mono (C.extBeta α) (Fin.le_iff_val_le_val.mp hab))
    · intro i
      have hcnt := O.modeOf_count (C.extBeta α) (C.extBeta_sum hα) ⟨i.1, by dsimp only [OccCtx.m, C]; omega⟩
      have hsub : (Finset.univ.filter fun p : Fin (2 * K) => l p = ⟨i.1, by omega⟩) =
          Finset.univ.filter fun p : Fin (2 * K) => modeOf54 (C.extBeta α) p.1 = i.1 := by
        ext p; simp [l, Fin.ext_iff]
      rw [hsub, hcnt]
      dsimp only [OccCtx.extBeta, C]
      rw [dif_pos i.isLt]
    · have hcnt := O.modeOf_count (C.extBeta α) (C.extBeta_sum hα) (Fin.last n)
      rw [Fin.val_last] at hcnt
      have hsub : (Finset.univ.filter fun p : Fin (2 * K) => l p = ⟨n, Nat.lt_succ_self n⟩) =
          Finset.univ.filter fun p : Fin (2 * K) => modeOf54 (C.extBeta α) p.1 = n := by
        ext p; simp [l, Fin.ext_iff]
      rw [hsub, hcnt]
      dsimp only [OccCtx.extBeta, C]
      rw [Fin.val_last, dif_neg (lt_irrefl n)]
    · rw [show V_occ.unitary = C.stageAC.unitary from rfl, padKet_ket_eq,
        C.padZero_flatReg_eq_packState α (C.sum_sub_lt_two_pow_w_v hα)]
      dsimp only [OccCtx.stageAC]
      simp only [LayeredCircuit.seq_unitary, act_mul]
      rw [C.act_pass1C α hα, C.act_pass2C α hα, C.act_encodeSymAllC α hα]
      exact (C.embedPartAndDeg54_eq_packState (∑ i, α i) (fun p => particleSym54 n C.s (l p))).symm

