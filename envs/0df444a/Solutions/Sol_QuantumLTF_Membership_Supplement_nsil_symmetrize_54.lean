-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.nsil_symmetrize_54
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T03:57:33.595194+00:00
-- url     : https://prove2.me/submissions/293a9e97-127d-499c-be65-138f8c4cac44

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
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Comb
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Circs
import Theorems.Thm_QuantumLTF_Membership_Supplement_bitonic_routing_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_lcg_sym_comb_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_lcg_sym_arith_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_alonso_schott_sil_54
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketHL54V2
import Theorems.Thm_QuantumLTF_Membership_Supplement_harm_bucket_hl_54_v2

set_option autoImplicit false

namespace Aux_nsil_sym_54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

/-! ### 1. Embedding, `liftState`, and Sub-Circuit Helpers -/

def sliceEmb {m : ℕ} (off len : ℕ) (h : off + len ≤ m) : Fin len ↪ Fin m where
  toFun i := ⟨off + i.1, by omega⟩
  inj' _ _ hij := Fin.ext (by have := congrArg Fin.val hij; dsimp at this; omega)

@[simp] lemma sliceEmb_apply {m : ℕ} (off len : ℕ) (h : off + len ≤ m) (i : Fin len) :
    sliceEmb off len h i = ⟨off + i.1, by omega⟩ := rfl

lemma sliceEmb_disjoint {m o1 l1 o2 l2 : ℕ} (h1 : o1 + l1 ≤ m) (h2 : o2 + l2 ≤ m)
    (h : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) :
    ∀ i j, sliceEmb o1 l1 h1 i ≠ sliceEmb o2 l2 h2 j := by
  intro i j hij
  have hv := congrArg Fin.val hij
  have hi := i.isLt
  have hj := j.isLt
  simp only [sliceEmb_apply] at hv
  omega

def regEmb {m : ℕ} (off N w : ℕ) (h : off + N * w ≤ m) : Fin (N * w) ↪ Fin m :=
  sliceEmb off (N * w) h

def slotInReg (N w : ℕ) (j : Fin N) : Fin w ↪ Fin (N * w) where
  toFun b := finProdFinEquiv (j, b)
  inj' _ _ h := (Prod.ext_iff.mp (finProdFinEquiv.injective h)).2

@[simp] lemma slotInReg_apply (N w : ℕ) (j : Fin N) (b : Fin w) :
    slotInReg N w j b = finProdFinEquiv (j, b) := rfl

def slotEmb {m : ℕ} (off N w : ℕ) (h : off + N * w ≤ m) (j : Fin N) : Fin w ↪ Fin m :=
  (slotInReg N w j).trans (regEmb off N w h)

lemma emb_disjoint_combineEmb {a b c m : ℕ} {ea : Fin a ↪ Fin m} {eb : Fin b ↪ Fin m}
    {ec : Fin c ↪ Fin m} (hab : ∀ i j, ea i ≠ eb j)
    (hac : ∀ i k, ea i ≠ ec k) (hbc : ∀ j k, eb j ≠ ec k) :
    ∀ u k, combineEmb ea eb hab u ≠ ec k := by
  intro u k
  induction u using Fin.addCases with
  | left i => simp only [combineEmb_castAdd]; exact hac i k
  | right j => simp only [combineEmb_natAdd]; exact hbc j k

lemma combineEmb_disjoint_emb {a b c m : ℕ} {ea : Fin a ↪ Fin m} {eb : Fin b ↪ Fin m}
    {ec : Fin c ↪ Fin m} (hab : ∀ i j, ea i ≠ eb j)
    (hac : ∀ i k, ea i ≠ ec k) (hbc : ∀ j k, eb j ≠ ec k) :
    ∀ k u, ec k ≠ combineEmb ea eb hab u :=
  fun k u h => emb_disjoint_combineEmb hab hac hbc u k h.symm

lemma emb_trans_disjoint_left {a b m : ℕ} {e1 : Fin a ↪ Fin b} {e2 : Fin b ↪ Fin m}
    {c : ℕ} {ec : Fin c ↪ Fin m} (h : ∀ j k, e2 j ≠ ec k) :
    ∀ i k, (e1.trans e2) i ≠ ec k :=
  fun i k => h (e1 i) k

lemma emb_trans_disjoint_right {a b m : ℕ} {e1 : Fin a ↪ Fin b} {e2 : Fin b ↪ Fin m}
    {c : ℕ} {ec : Fin c ↪ Fin m} (h : ∀ k j, ec k ≠ e2 j) :
    ∀ k i, ec k ≠ (e1.trans e2) i :=
  fun k i => h k (e1 i)

lemma slotEmb_disjoint_slot {m off N w : ℕ} (h : off + N * w ≤ m) {j1 j2 : Fin N} (hj : j1 ≠ j2) :
    ∀ b1 b2, slotEmb off N w h j1 b1 ≠ slotEmb off N w h j2 b2 := by
  intro b1 b2 hij
  have heq := (regEmb off N w h).injective hij
  exact hj (Prod.ext_iff.mp (finProdFinEquiv.injective heq)).1

lemma combineEmb_zero_right {a m : ℕ} (e : Fin a ↪ Fin m) (e0 : Fin 0 ↪ Fin m)
    (h : ∀ i j, e i ≠ e0 j) : combineEmb e e0 h = e := by
  ext i
  have hi : (i : Fin (a + 0)) = Fin.castAdd 0 i := Fin.ext rfl
  conv_lhs => rw [hi]
  rw [combineEmb_castAdd]

lemma updateOn_combineEmb_right {a b m : ℕ} (eA : Fin a ↪ Fin m) (eB : Fin b ↪ Fin m)
    (hAB : ∀ i j, eA i ≠ eB j) (z : Qubits m)
    (f : Qubits (a + b) → Qubits (a + b))
    (hleft : ∀ (x : Qubits (a + b)) (i : Fin a), f x (Fin.castAdd b i) = x (Fin.castAdd b i))
    (g : Qubits b)
    (hright : ∀ j : Fin b, f (z ∘ combineEmb eA eB hAB) (Fin.natAdd a j) = g j) :
    updateOn (combineEmb eA eB hAB) z (f (z ∘ combineEmb eA eB hAB)) = updateOn eB z g := by
  funext u
  by_cases hu : u ∈ Set.range (combineEmb eA eB hAB)
  · rcases hu with ⟨ij, rfl⟩
    induction ij using Fin.addCases with
    | left i =>
      rw [updateOn_apply_emb, combineEmb_castAdd]
      have hnot : eA i ∉ Set.range eB := by rintro ⟨j, hj⟩; exact hAB i j hj.symm
      rw [updateOn_apply_not_mem _ _ _ hnot, hleft, Function.comp_apply, combineEmb_castAdd]
    | right j =>
      rw [updateOn_apply_emb, combineEmb_natAdd, updateOn_apply_emb, hright j]
  · have hnotB : u ∉ Set.range eB := fun ⟨j, hj⟩ => hu ⟨Fin.natAdd a j, by simpa using hj⟩
    rw [updateOn_apply_not_mem _ _ _ hu, updateOn_apply_not_mem _ _ _ hnotB]

lemma act_mapWires_ket_singleton {m₀ m : ℕ} (lc : LayeredCircuit m₀) (emb : Fin m₀ ↪ Fin m)
    (z : Qubits m) (y₀ : Qubits m₀) (h : act lc.unitary (ket (z ∘ emb)) = ket y₀) :
    act (lc.mapWires emb).unitary (ket z) = ket (updateOn emb z y₀) := by
  have hsum := LcgSym54.act_mapWires_ket_sum lc emb z ({()} : Finset Unit) (fun _ => 1) (fun _ => y₀)
    (by simpa using h)
  simpa using hsum

lemma act_adj_ket {m : ℕ} (lc : LayeredCircuit m) {ψ φ : EuclideanSpace ℂ (Qubits m)}
    (h : act lc.unitary ψ = φ) :
    act lc.adj.unitary φ = ψ := by
  rw [← h, ← act_mul, LayeredCircuit.adj_unitary,
    Matrix.mem_unitaryGroup_iff'.mp lc.unitary_mem_unitaryGroup, act_one]

lemma act_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℂ)
    {A : Type*} (s : Finset A) (f : A → EuclideanSpace ℂ ι) :
    act V (∑ a ∈ s, f a) = ∑ a ∈ s, act V (f a) :=
  map_sum (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) V) f s

lemma act_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℂ)
    (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act V (c • ψ) = c • act V ψ :=
  map_smul (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) V) c ψ

lemma updateOn_updateOn_self {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (z : Qubits m) (x y : Qubits m₀) :
    updateOn emb (updateOn emb z x) y = updateOn emb z y := by
  funext u
  by_cases hu : u ∈ Set.range emb
  · rcases hu with ⟨i, rfl⟩
    rw [updateOn_apply_emb, updateOn_apply_emb]
  · rw [updateOn_apply_not_mem _ _ _ hu, updateOn_apply_not_mem _ _ _ hu, updateOn_apply_not_mem _ _ _ hu]

noncomputable def liftState {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (z₀ : Qubits m)
    (ψ : EuclideanSpace ℂ (Qubits m₀)) : EuclideanSpace ℂ (Qubits m) :=
  ∑ x : Qubits m₀, ψ x • ket (updateOn emb z₀ x)

lemma liftState_ket {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (z₀ : Qubits m) (x₀ : Qubits m₀) :
    liftState emb z₀ (ket x₀) = ket (updateOn emb z₀ x₀) := by
  unfold liftState
  rw [Finset.sum_eq_single x₀]
  · simp [ket]
  · intro x _ hx
    simp [ket, hx]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma liftState_smul {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (z₀ : Qubits m) (c : ℂ)
    (ψ : EuclideanSpace ℂ (Qubits m₀)) :
    liftState emb z₀ (c • ψ) = c • liftState emb z₀ ψ := by
  unfold liftState
  have hcoord : ∀ x : Qubits m₀, ((c • ψ) x) • ket (updateOn emb z₀ x) =
      c • (ψ x • ket (updateOn emb z₀ x)) := by
    intro x
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← smul_smul]
  simp_rw [hcoord, ← Finset.smul_sum]

lemma liftState_sum {m₀ m : ℕ} {A : Type*} (emb : Fin m₀ ↪ Fin m) (z₀ : Qubits m)
    (s : Finset A) (f : A → EuclideanSpace ℂ (Qubits m₀)) :
    liftState emb z₀ (∑ a ∈ s, f a) = ∑ a ∈ s, liftState emb z₀ (f a) := by
  unfold liftState
  have hcoord : ∀ x : Qubits m₀, (∑ a ∈ s, f a) x = ∑ a ∈ s, (f a) x := by
    intro x
    change (WithLp.ofLp (∑ a ∈ s, f a)) x = ∑ a ∈ s, (WithLp.ofLp (f a)) x
    rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [hcoord, Finset.sum_smul]
  rw [Finset.sum_comm]

lemma act_mapWires_liftState {m₀ m : ℕ} (lc : LayeredCircuit m₀) (emb : Fin m₀ ↪ Fin m)
    (z₀ : Qubits m) (ψ : EuclideanSpace ℂ (Qubits m₀)) :
    act (lc.mapWires emb).unitary (liftState emb z₀ ψ) = liftState emb z₀ (act lc.unitary ψ) := by
  unfold liftState
  rw [act_sum]
  simp_rw [act_smul, act_mapWires_ket_expand, updateOn_comp_self, updateOn_updateOn_self,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hcoord : (act lc.unitary ψ) y = ∑ x : Qubits m₀, ψ x * (act lc.unitary (ket x)) y := by
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    refine Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [hcoord, Finset.sum_smul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul]

lemma act_seqList_foldl {m : ℕ} {S : Type*} (enc : S → Qubits m)
    (circ : ℕ → LayeredCircuit m) (trans : S → ℕ → S)
    (xs : List ℕ) (s0 : S)
    (hstep : ∀ k ∈ xs, ∀ s : S, act (circ k).unitary (ket (enc s)) = ket (enc (trans s k))) :
    act (LayeredCircuit.seqList (xs.map circ)).unitary (ket (enc s0)) =
      ket (enc (xs.foldl trans s0)) := by
  induction xs generalizing s0 with
  | nil => simp [LayeredCircuit.seqList, act_one]
  | cons k ks ih =>
    simp only [List.map_cons, LayeredCircuit.seqList, LayeredCircuit.seq_unitary,
      act_mul, List.foldl_cons]
    rw [hstep k List.mem_cons_self s0]
    exact ih (trans s0 k) fun k' hk' => hstep k' (List.mem_cons_of_mem _ hk')

lemma LayeredCircuit_seqList_size_le {m : ℕ} (lcs : List (LayeredCircuit m)) (B : ℕ)
    (hB : ∀ lc ∈ lcs, lc.size ≤ B) :
    (LayeredCircuit.seqList lcs).size ≤ lcs.length * B := by
  rw [LayeredCircuit.seqList_size]
  induction lcs with
  | nil => simp
  | cons lc rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := hB lc List.mem_cons_self
    have h2 := ih fun lc' hlc' => hB lc' (List.mem_cons_of_mem _ hlc')
    omega

lemma act_setConstOn {w m : ℕ} (arith : LcgSym54ArithV2) (c : ℕ)
    (e : Fin w ↪ Fin m) (z : Qubits m) :
    act ((arith.setConstMSBCircuit w c).mapWires e).unitary (ket z) =
      ket (updateOn e z (fun i => xor (z (e i)) (natToBits w c i))) := by
  let embAnc : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have hdisj : ∀ i j, e i ≠ embAnc j := fun _ j => Fin.elim0 j
  have hsub := arith.act_subReg_perm (arith.setConstMSBCircuit w c) (setConstMSBFn w c)
    (arith.setConstMSBCircuit_implements w c) e embAnc hdisj z (fun j => Fin.elim0 j)
  rw [combineEmb_zero_right] at hsub
  exact hsub

lemma act_copyRegOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eSrc eDst : Fin w ↪ Fin m) (hSD : ∀ i j, eSrc i ≠ eDst j) (z : Qubits m) :
    act ((arith.copyRegCircuit w).mapWires (combineEmb eSrc eDst hSD)).unitary (ket z) =
      ket (updateOn eDst z (fun j => xor (z (eDst j)) (z (eSrc j)))) := by
  let embAnc : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have hdisj : ∀ i j, combineEmb eSrc eDst hSD i ≠ embAnc j := fun _ j => Fin.elim0 j
  have hsub := arith.act_subReg_perm (arith.copyRegCircuit w) (copyRegFn w)
    (arith.copyRegCircuit_implements w) (combineEmb eSrc eDst hSD) embAnc hdisj z (fun j => Fin.elim0 j)
  rw [combineEmb_zero_right] at hsub
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eSrc eDst hSD z (copyRegFn w) ?_ _ ?_
  · intro x i
    dsimp only [copyRegFn]
    have hlt : ¬ (w ≤ (Fin.castAdd w i : Fin (w + w)).1) := by dsimp [Fin.castAdd]; omega
    rw [dif_neg hlt]
  · intro j
    dsimp only [copyRegFn, Function.comp_apply]
    have hge : w ≤ (Fin.natAdd w j : Fin (w + w)).1 := by dsimp [Fin.natAdd]; omega
    rw [dif_pos hge, combineEmb_natAdd]
    have hidx : (⟨(Fin.natAdd w j : Fin (w + w)).1 - w, by dsimp [Fin.natAdd]; omega⟩ : Fin (w + w)) =
        Fin.castAdd w j := Fin.ext (by dsimp [Fin.natAdd, Fin.castAdd]; omega)
    rw [hidx, combineEmb_castAdd]

def packDTA54Emb {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j)
    (hAA : ∀ i k, eArr i ≠ eAnc k)
    (hTA : ∀ j k, eTr j ≠ eAnc k) :
    Fin ((N * w + T) + anc) ↪ Fin m :=
  combineEmb (combineEmb eArr eTr hAT) eAnc (emb_disjoint_combineEmb hAT hAA hTA)

@[simp] lemma packDTA54Emb_arr {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (i : Fin (N * w)) :
    packDTA54Emb eArr eTr eAnc hAT hAA hTA (Fin.castAdd anc (Fin.castAdd T i)) = eArr i := by
  simp [packDTA54Emb]

@[simp] lemma packDTA54Emb_tr {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (j : Fin T) :
    packDTA54Emb eArr eTr eAnc hAT hAA hTA (Fin.castAdd anc (Fin.natAdd (N * w) j)) = eTr j := by
  simp [packDTA54Emb]

@[simp] lemma packDTA54Emb_anc {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (k : Fin anc) :
    packDTA54Emb eArr eTr eAnc hAT hAA hTA (Fin.natAdd (N * w + T) k) = eAnc k := by
  simp [packDTA54Emb]

lemma comp_packDTA54Emb {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (z : Qubits m) (arr : Fin N → Qubits w) (tr : Qubits T)
    (hzA : z ∘ eArr = flatReg N w arr) (hzT : z ∘ eTr = tr) (hzAnc : z ∘ eAnc = fun _ => false) :
    z ∘ packDTA54Emb eArr eTr eAnc hAT hAA hTA = packDTA54 N w T anc arr tr := by
  funext u
  refine Fin.addCases (fun ij => ?_) (fun k => ?_) u
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) ij
    · simp only [Function.comp_apply, packDTA54Emb_arr, packDTA54, padZero_castAdd, Fin.append_left]
      exact congrFun hzA i
    · simp only [Function.comp_apply, packDTA54Emb_tr, packDTA54, padZero_castAdd, Fin.append_right]
      exact congrFun hzT j
  · simp only [Function.comp_apply, packDTA54Emb_anc, packDTA54, padZero_natAdd]
    exact congrFun hzAnc k

lemma padKet_ket_eq {N e : ℕ} (x : Qubits N) :
    padKet e (ket x) = ket (padZero N e x) := by
  ext z
  simp only [padKet, ket, PiLp.single_apply]
  by_cases hz : ∀ j : Fin e, z (Fin.natAdd N j) = false
  · rw [if_pos hz]
    by_cases hmatch : (fun i => z (Fin.castAdd e i)) = x
    · have hzp : z = padZero N e x := by
        funext u
        refine Fin.addCases (fun i => ?_) (fun j => ?_) u
        · simpa using congrFun hmatch i
        · simp [hz j]
      rw [if_pos hmatch, if_pos hzp]
    · have hzp : z ≠ padZero N e x := fun h => hmatch (funext fun i => by simpa using congrFun h (Fin.castAdd e i))
      rw [if_neg hmatch, if_neg hzp]
  · rw [if_neg hz]
    have hzp : z ≠ padZero N e x := fun h => hz fun j => by simpa using congrFun h (Fin.natAdd N j)
    rw [if_neg hzp]

/-! ### 2. Pure Sorting & Key-Composition Lemmas -/

def routePerm (br : BitonicRouting54) (d : ℕ) (flags : Fin (sortTraceSize d) → Bool) :
    Equiv.Perm (Fin (arity d)) where
  toFun := routeSort d flags id
  invFun := unrouteSort d flags id
  left_inv i := by
    have h := congrFun (br.routeSort_unrouteSort d flags id) i
    rwa [br.routeSort_apply d flags (unrouteSort d flags id) i] at h
  right_inv i := by
    have h := congrFun (br.unrouteSort_routeSort d flags id) i
    rwa [br.unrouteSort_apply d flags (routeSort d flags id) i] at h

lemma routeSort_eq_comp_routePerm (br : BitonicRouting54) {α : Type} (d : ℕ)
    (flags : Fin (sortTraceSize d) → Bool) (x : Fin (arity d) → α) :
    routeSort d flags x = x ∘ routePerm br d flags :=
  funext fun i => br.routeSort_apply d flags x i

lemma unrouteSort_eq_comp_inv_routePerm (br : BitonicRouting54) {α : Type} (d : ℕ)
    (flags : Fin (sortTraceSize d) → Bool) (x : Fin (arity d) → α) :
    unrouteSort d flags x = fun i => x ((routePerm br d flags)⁻¹ i) :=
  funext fun i => br.unrouteSort_apply d flags x i

lemma natToBits_one_one : natToBits 1 1 = fun _ => true := by
  have h0 : bitsToNat (natToBits 1 1) = 1 := by
    rw [← bitsEquivFin_apply]
    simp [natToBits]
  have h1 : bitsToNat (fun _ : Fin 1 => true) = 1 := by
    simp [bitsToNat]
  rw [← h1] at h0
  exact bitsToNat_inj_of_zero_lt (w := 1) h0
where
  bitsToNat_inj_of_zero_lt {w : ℕ} {a b : Qubits w} (h : bitsToNat a = bitsToNat b) : a = b := by
    have ha := bitsEquivFin_apply a
    have hb := bitsEquivFin_apply b
    have heq : bitsEquivFin w a = bitsEquivFin w b := Fin.ext (by omega)
    exact (bitsEquivFin w).injective heq

lemma list_ofFn_comp_perm {M : ℕ} {α : Type*} (f : Fin M → α) (π : Equiv.Perm (Fin M)) :
    (List.ofFn (f ∘ π)).Perm (List.ofFn f) := by
  classical
  have hcnt : ∀ (L : List α) (a : α),
      L.count a = ∑ i : Fin L.length, if L[i.1] = a then 1 else 0 := by
    intro L a
    induction L with
    | nil => simp
    | cons x xs ih =>
      simp only [List.count_cons, ih, List.length_cons, Fin.sum_univ_succ, Fin.val_zero,
        Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ, beq_iff_eq]
      rw [Nat.add_comm]
      rfl
  rw [List.perm_iff_count]
  intro a
  rw [hcnt, hcnt]
  have h1 : ∑ i : Fin (List.ofFn (f ∘ π)).length,
        (if (List.ofFn (f ∘ π))[i.1] = a then 1 else 0) =
      ∑ i : Fin M, if f (π i) = a then 1 else 0 := by
    refine Fintype.sum_equiv (finCongr List.length_ofFn) _ _ fun i => ?_
    simp only [List.getElem_ofFn, Function.comp_apply]
    rfl
  have h2 : ∑ i : Fin (List.ofFn f).length,
        (if (List.ofFn f)[i.1] = a then 1 else 0) =
      ∑ i : Fin M, if f i = a then 1 else 0 := by
    refine Fintype.sum_equiv (finCongr List.length_ofFn) _ _ fun i => ?_
    simp only [List.getElem_ofFn]
    rfl
  rw [h1, h2]
  exact Fintype.sum_equiv π _ _ fun _ => rfl

def padSym (n s K d : ℕ) (y : Fin (2 * K) → Fin (n + 1)) : Fin (arity d) → Qubits s :=
  fun p => if h : p.1 < 2 * K then particleSym54 n s (y ⟨p.1, h⟩) else fun _ => false

def key2Arr (n s K d : ℕ) (y : Fin (2 * K) → Fin (n + 1)) : Fin (arity d) → Qubits ((1 + s) + d) :=
  fun p =>
    if h : p.1 < 2 * K then
      Fin.append (Fin.append (fun _ : Fin 1 => false) (particleSym54 n s (y ⟨p.1, h⟩))) (fun _ : Fin d => false)
    else
      Fin.append (Fin.append (fun _ : Fin 1 => true) (fun _ : Fin s => false)) (natToBits d p.1)

lemma bitsToNat_key2Arr_lt (comb : LcgSym54Comb) (n K d : ℕ)
    (y : Fin (2 * K) → Fin (n + 1)) (p : Fin (arity d)) (hp : p.1 < 2 * K) :
    let s := Nat.clog 2 n + 1
    bitsToNat (key2Arr n s K d y p) = 2 ^ d * bitsToNat (particleSym54 n s (y ⟨p.1, hp⟩)) := by
  intro s
  simp only [key2Arr, dif_pos hp, comb.bitsToNat_append]
  have h1 : bitsToNat (fun _ : Fin 1 => false) = 0 := by simp [bitsToNat]
  have h2 : bitsToNat (fun _ : Fin d => false) = 0 := by simp [bitsToNat]
  rw [h1, h2]
  ring

lemma bitsToNat_key2Arr_ge (comb : LcgSym54Comb) (n K d : ℕ)
    (y : Fin (2 * K) → Fin (n + 1)) (p : Fin (arity d)) (hp : ¬ p.1 < 2 * K) :
    let s := Nat.clog 2 n + 1
    bitsToNat (key2Arr n s K d y p) = 2 ^ (s + d) + p.1 := by
  intro s
  simp only [key2Arr, dif_neg hp, comb.bitsToNat_append]
  have h1 : bitsToNat (fun _ : Fin 1 => true) = 1 := by simp [bitsToNat]
  have h2 : bitsToNat (fun _ : Fin s => false) = 0 := by simp [bitsToNat]
  have hp_lt : p.1 < 2 ^ d := by rw [← arity_eq_two_pow d]; exact p.isLt
  have h3 : bitsToNat (natToBits d p.1) = p.1 := comb.bitsToNat_natToBits hp_lt
  rw [h1, h2, h3, Nat.pow_add]
  ring

lemma key2Arr_permList (n K d : ℕ) (hNM : 2 * K ≤ arity d)
    (l : Fin (2 * K) → Fin (n + 1)) (σ : Equiv.Perm (Fin (2 * K))) :
    let s := Nat.clog 2 n + 1
    key2Arr n s K d (permList σ l) = key2Arr n s K d l ∘ padPerm54 (2 * K) (arity d) hNM σ := by
  intro s
  funext p
  by_cases hp : p.1 < 2 * K
  · have hp' : (padPerm54 (2 * K) (arity d) hNM σ p).1 < 2 * K := by
      rw [padPerm54_lt _ _ _ _ hp]
      exact (σ ⟨p.1, hp⟩).isLt
    simp only [Function.comp_apply, key2Arr, dif_pos hp, dif_pos hp']
    have hidx : (⟨(padPerm54 (2 * K) (arity d) hNM σ p).1, hp'⟩ : Fin (2 * K)) = σ ⟨p.1, hp⟩ := by
      ext; exact padPerm54_lt _ _ _ _ hp
    rw [hidx]
    rfl
  · have hge : 2 * K ≤ p.1 := Nat.le_of_not_lt hp
    simp only [Function.comp_apply, padPerm54_ge _ _ _ _ hge, key2Arr, dif_neg hp]

lemma sort_key2Arr_eq (br : BitonicRouting54) (comb : LcgSym54Comb) (n K d : ℕ)
    (hNM : 2 * K ≤ arity d) (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l)
    (σ : Equiv.Perm (Fin (2 * K))) :
    let s := Nat.clog 2 n + 1
    sort (fun r => bitsToNat (recKey54 (w_p := 0) r)) d true (key2Arr n s K d (permList σ l)) =
      key2Arr n s K d l := by
  intro s
  have hrec : (fun r : Qubits (((1 + s) + d) + 0) => bitsToNat (recKey54 (w_p := 0) r)) = bitsToNat :=
    funext fun r => congrArg bitsToNat (funext fun _ => rfl)
  change sort (fun r : Qubits (((1 + s) + d) + 0) => bitsToNat (recKey54 (w_p := 0) r)) d true
      (key2Arr n s K d (permList σ l)) = key2Arr n s K d l
  rw [hrec]
  let y := permList σ l
  have hmono_l : Monotone (bitsToNat ∘ key2Arr n s K d l) := by
    intro p₁ p₂ hp
    dsimp only [Function.comp_apply]
    by_cases h1 : p₁.1 < 2 * K <;> by_cases h2 : p₂.1 < 2 * K
    · rw [bitsToNat_key2Arr_lt comb n K d l p₁ h1, bitsToNat_key2Arr_lt comb n K d l p₂ h2]
      exact Nat.mul_le_mul_left _
        ((comb.bitsToNat_particleSym54_strictMono n).monotone (hl (by exact Fin.mk_le_mk.mpr hp)))
    · rw [bitsToNat_key2Arr_lt comb n K d l p₁ h1, bitsToNat_key2Arr_ge comb n K d l p₂ h2]
      have hlt : bitsToNat (particleSym54 n (Nat.clog 2 n + 1) (l ⟨p₁.1, h1⟩)) <
          2 ^ (Nat.clog 2 n + 1) := comb.bitsToNat_lt_two_pow _
      have hpow : 2 ^ d * bitsToNat (particleSym54 n (Nat.clog 2 n + 1) (l ⟨p₁.1, h1⟩)) <
          2 ^ d * 2 ^ (Nat.clog 2 n + 1) := Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos d)
      rw [Nat.pow_add, Nat.mul_comm (2 ^ (Nat.clog 2 n + 1)) (2 ^ d)]
      omega
    · exfalso; have : p₁.1 ≤ p₂.1 := hp; omega
    · rw [bitsToNat_key2Arr_ge comb n K d l p₁ h1, bitsToNat_key2Arr_ge comb n K d l p₂ h2]
      omega
  have hmono_sort : Monotone (bitsToNat ∘ sort bitsToNat d true (key2Arr n s K d y)) :=
    br.monotone_sort bitsToNat d (key2Arr n s K d y)
  have hperm1 : (List.ofFn (sort bitsToNat d true (key2Arr n s K d y))).Perm (List.ofFn (key2Arr n s K d y)) :=
    br.sort_perm bitsToNat d true (key2Arr n s K d y)
  have hperm2 : (List.ofFn (key2Arr n s K d y)).Perm (List.ofFn (key2Arr n s K d l)) := by
    rw [show y = permList σ l from rfl, key2Arr_permList n K d hNM l σ]
    exact list_ofFn_comp_perm _ _
  have hperm_nat : (List.ofFn (bitsToNat ∘ sort bitsToNat d true (key2Arr n s K d y))).Perm
      (List.ofFn (bitsToNat ∘ key2Arr n s K d l)) := by
    have h := (hperm1.trans hperm2).map bitsToNat
    simpa [List.map_ofFn, Function.comp_def] using h
  have hlist_eq : List.ofFn (bitsToNat ∘ sort bitsToNat d true (key2Arr n s K d y)) =
      List.ofFn (bitsToNat ∘ key2Arr n s K d l) :=
    comb.perm_eq_of_sorted_of_inj id _ _ hperm_nat
      (List.pairwise_ofFn.mpr fun _ _ hij => hmono_sort (le_of_lt hij))
      (List.pairwise_ofFn.mpr fun _ _ hij => hmono_l (le_of_lt hij))
      (fun _ _ _ _ h => h)
  funext i
  have hnat : bitsToNat (sort bitsToNat d true (key2Arr n s K d y) i) = bitsToNat (key2Arr n s K d l i) := by
    have hi : i.1 < 2 ^ d := by rw [← arity_eq_two_pow d]; exact i.isLt
    have := congrArg (fun L : List ℕ => L[i.1]?) hlist_eq
    simpa [hi] using this
  exact comb.bitsToNat_inj hnat

lemma sort_permRegBits_eq (br : BitonicRouting54) (comb : LcgSym54Comb) (K d : ℕ)
    (hNM : 2 * K ≤ arity d) (σ : Equiv.Perm (Fin (2 * K))) :
    sort (fun r => bitsToNat (recKey54 (w_p := 0) r)) d true (permRegBits (2 * K) d hNM σ) =
      fun i : Fin (arity d) => natToBits d i.1 := by
  have hrec : (fun r : Qubits (d + 0) => bitsToNat (recKey54 (w_p := 0) r)) = bitsToNat :=
    funext fun r => congrArg bitsToNat (funext fun _ => rfl)
  change sort (fun r : Qubits (d + 0) => bitsToNat (recKey54 (w_p := 0) r)) d true
      (permRegBits (2 * K) d hNM σ) = _
  rw [hrec]
  have hpermReg : permRegBits (2 * K) d hNM σ =
      (fun i : Fin (arity d) => natToBits d i.1) ∘ padPerm54 (2 * K) (arity d) hNM σ := rfl
  have hmono1 : Monotone (bitsToNat ∘ sort bitsToNat d true (permRegBits (2 * K) d hNM σ)) :=
    br.monotone_sort bitsToNat d (permRegBits (2 * K) d hNM σ)
  have hmono2 : Monotone (bitsToNat ∘ (fun i : Fin (arity d) => natToBits d i.1)) := by
    intro i j hij
    have hi : i.1 < 2 ^ d := by rw [← arity_eq_two_pow d]; exact i.isLt
    have hj : j.1 < 2 ^ d := by rw [← arity_eq_two_pow d]; exact j.isLt
    dsimp only [Function.comp_apply]
    rw [comb.bitsToNat_natToBits hi, comb.bitsToNat_natToBits hj]
    exact hij
  have hperm1 := br.sort_perm bitsToNat d true (permRegBits (2 * K) d hNM σ)
  have hperm2 : (List.ofFn (permRegBits (2 * K) d hNM σ)).Perm
      (List.ofFn (fun i : Fin (arity d) => natToBits d i.1)) := by
    rw [hpermReg]
    exact list_ofFn_comp_perm _ _
  have hperm_nat : (List.ofFn (bitsToNat ∘ sort bitsToNat d true (permRegBits (2 * K) d hNM σ))).Perm
      (List.ofFn (bitsToNat ∘ fun i : Fin (arity d) => natToBits d i.1)) := by
    have h := (hperm1.trans hperm2).map bitsToNat
    simpa [List.map_ofFn, Function.comp_def] using h
  have hlist_eq : List.ofFn (bitsToNat ∘ sort bitsToNat d true (permRegBits (2 * K) d hNM σ)) =
      List.ofFn (bitsToNat ∘ fun i : Fin (arity d) => natToBits d i.1) :=
    comb.perm_eq_of_sorted_of_inj id _ _ hperm_nat
      (List.pairwise_ofFn.mpr fun _ _ hij => hmono1 (le_of_lt hij))
      (List.pairwise_ofFn.mpr fun _ _ hij => hmono2 (le_of_lt hij))
      (fun _ _ _ _ h => h)
  funext i
  have hi : i.1 < 2 ^ d := by rw [← arity_eq_two_pow d]; exact i.isLt
  have hnat : bitsToNat (sort bitsToNat d true (permRegBits (2 * K) d hNM σ) i) =
      bitsToNat (natToBits d i.1) := by
    have := congrArg (fun L : List ℕ => L[i.1]?) hlist_eq
    simpa [hi] using this
  exact comb.bitsToNat_inj hnat

lemma unrouteSort_tr1_id (br : BitonicRouting54) (comb : LcgSym54Comb) (K d : ℕ)
    (hNM : 2 * K ≤ arity d) (σ : Equiv.Perm (Fin (2 * K))) :
    let tr1 := sortTrace (fun r => bitsToNat (recKey54 (w_p := 0) r)) d true (permRegBits (2 * K) d hNM σ)
    unrouteSort d tr1 id = padPerm54 (2 * K) (arity d) hNM σ := by
  intro tr1
  have hsort := sort_permRegBits_eq br comb K d hNM σ
  have hrec : (fun r : Qubits (d + 0) => bitsToNat (recKey54 (w_p := 0) r)) = bitsToNat := by
    funext r; congr 1
  have hroute_tr1 : routeSort d tr1 (permRegBits (2 * K) d hNM σ) = fun i : Fin (arity d) => natToBits d i.1 := by
    have h := br.routeSort_sortTrace (fun r => bitsToNat (recKey54 (w_p := 0) r)) d true (permRegBits (2 * K) d hNM σ)
    rw [h, hsort]
  funext i
  let π := routePerm br d tr1
  have hperm_j : ∀ j : Fin (arity d), padPerm54 (2 * K) (arity d) hNM σ (π j) = j := by
    intro j
    have hj := congrFun hroute_tr1 j
    rw [br.routeSort_apply] at hj
    change permRegBits (2 * K) d hNM σ (π j) = natToBits d j.1 at hj
    have hnat := congrArg bitsToNat hj
    have h1 : (padPerm54 (2 * K) (arity d) hNM σ (π j)).1 < 2 ^ d := by
      rw [← arity_eq_two_pow d]; exact (padPerm54 _ _ _ _ _).isLt
    have h2 : j.1 < 2 ^ d := by rw [← arity_eq_two_pow d]; exact j.isLt
    dsimp only [permRegBits] at hnat
    rw [comb.bitsToNat_natToBits h1, comb.bitsToNat_natToBits h2] at hnat
    exact Fin.ext hnat
  have hinj : padPerm54 (2 * K) (arity d) hNM σ (π (π⁻¹ i)) = π⁻¹ i := hperm_j (π⁻¹ i)
  have hinv_eq : π⁻¹ i = unrouteSort d tr1 id i := rfl
  rw [← hinv_eq]
  simpa using hinj.symm

def tr2Of (n K d : ℕ) (y : Fin (2 * K) → Fin (n + 1)) : Fin (sortTraceSize d) → Bool :=
  sortTrace (fun r => bitsToNat (recKey54 (w_p := 0) r)) d true (key2Arr n (Nat.clog 2 n + 1) K d y)

noncomputable def tauOf (br : BitonicRouting54) (comb : LcgSym54Comb) (n K d : ℕ)
    (hNM : 2 * K ≤ arity d) (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l)
    (y : Fin (2 * K) → Fin (n + 1)) : Equiv.Perm (Fin (2 * K)) := by
  classical
  exact if h : ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = y then
    let π := routePerm br d (tr2Of n K d y)
    let hfix : ∀ i : Fin (arity d), 2 * K ≤ i.1 → π i = i := by
      intro i hi
      rcases h with ⟨σ, rfl⟩
      have hsort := sort_key2Arr_eq br comb n K d hNM l hl σ
      have hroute : routeSort d (tr2Of n K d (permList σ l)) (key2Arr n (Nat.clog 2 n + 1) K d (permList σ l)) =
          key2Arr n (Nat.clog 2 n + 1) K d l := by
        have h1 := br.routeSort_sortTrace (fun r => bitsToNat (recKey54 (w_p := 0) r)) d true
          (key2Arr n (Nat.clog 2 n + 1) K d (permList σ l))
        exact h1.trans hsort
      have heq := congrArg bitsToNat (congrFun hroute i)
      rw [br.routeSort_apply] at heq
      have hi_not : ¬ i.1 < 2 * K := Nat.not_lt.mpr hi
      rw [bitsToNat_key2Arr_ge comb n K d l i hi_not] at heq
      change bitsToNat (key2Arr n (Nat.clog 2 n + 1) K d (permList σ l) (π i)) = _ at heq
      by_cases hpi : (π i).1 < 2 * K
      · rw [bitsToNat_key2Arr_lt comb n K d _ (π i) hpi] at heq
        have hlt : bitsToNat (particleSym54 n (Nat.clog 2 n + 1) (permList σ l ⟨(π i).1, hpi⟩)) <
            2 ^ (Nat.clog 2 n + 1) := comb.bitsToNat_lt_two_pow _
        have hpow : 2 ^ d * bitsToNat (particleSym54 n (Nat.clog 2 n + 1) (permList σ l ⟨(π i).1, hpi⟩)) <
            2 ^ d * 2 ^ (Nat.clog 2 n + 1) := Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos d)
        rw [Nat.pow_add, Nat.mul_comm (2 ^ (Nat.clog 2 n + 1)) (2 ^ d)] at heq
        omega
      · rw [bitsToNat_key2Arr_ge comb n K d _ (π i) hpi] at heq
        exact Fin.ext (by omega)
    let hlt : ∀ i : Fin (2 * K), (π ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1 < 2 * K := by
      intro i
      by_contra hge
      have hge' : 2 * K ≤ (π ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1 := Nat.le_of_not_lt hge
      have hsame := hfix (π ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩) hge'
      have hinj := π.injective hsame
      have hval := congrArg Fin.val hinj
      dsimp at hval
      have := i.isLt
      omega
    let hinv_lt : ∀ i : Fin (2 * K), (π⁻¹ ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1 < 2 * K := by
      intro i
      by_contra hge
      have hge' : 2 * K ≤ (π⁻¹ ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1 := Nat.le_of_not_lt hge
      have hsame := hfix (π⁻¹ ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩) hge'
      change π (π.symm ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩) = _ at hsame
      rw [π.apply_symm_apply] at hsame
      have hval : i.1 = (π⁻¹ ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1 := congrArg Fin.val hsame
      have := i.isLt
      omega
    ({ toFun := fun i => ⟨(π ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1, hlt i⟩
       invFun := fun i => ⟨(π⁻¹ ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1, hinv_lt i⟩
       left_inv := fun i => Fin.ext (by
         dsimp
         rw [π.symm_apply_apply])
       right_inv := fun i => Fin.ext (by
         dsimp
         rw [π.apply_symm_apply]) } : Equiv.Perm (Fin (2 * K)))⁻¹
  else 1

lemma tauOf_spec (br : BitonicRouting54) (comb : LcgSym54Comb) (n K d : ℕ)
    (hNM : 2 * K ≤ arity d) (l : Fin (2 * K) → Fin (n + 1)) (hl : Monotone l)
    (y : Fin (2 * K) → Fin (n + 1)) (hy : ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = y) :
    permList (tauOf br comb n K d hNM l hl y)⁻¹ y = l ∧
      routeSort d (tr2Of n K d y) id = padPerm54 (2 * K) (arity d) hNM (tauOf br comb n K d hNM l hl y)⁻¹ := by
  classical
  have htau_inv : ∀ i : Fin (2 * K),
      ((tauOf br comb n K d hNM l hl y)⁻¹ i).1 =
        (routePerm br d (tr2Of n K d y) ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1 := by
    intro i
    simp [tauOf, dif_pos hy]
  have hfix : ∀ i : Fin (arity d), 2 * K ≤ i.1 → routePerm br d (tr2Of n K d y) i = i := by
    intro i hi
    rcases hy with ⟨σ, rfl⟩
    have hsort := sort_key2Arr_eq br comb n K d hNM l hl σ
    have hroute : routeSort d (tr2Of n K d (permList σ l)) (key2Arr n (Nat.clog 2 n + 1) K d (permList σ l)) =
        key2Arr n (Nat.clog 2 n + 1) K d l := by
      have h1 := br.routeSort_sortTrace (fun r => bitsToNat (recKey54 (w_p := 0) r)) d true
        (key2Arr n (Nat.clog 2 n + 1) K d (permList σ l))
      exact h1.trans hsort
    have heq := congrArg bitsToNat (congrFun hroute i)
    rw [br.routeSort_apply] at heq
    have hi_not : ¬ i.1 < 2 * K := Nat.not_lt.mpr hi
    rw [bitsToNat_key2Arr_ge comb n K d l i hi_not] at heq
    change bitsToNat (key2Arr n (Nat.clog 2 n + 1) K d (permList σ l)
      (routePerm br d (tr2Of n K d (permList σ l)) i)) = _ at heq
    by_cases hpi : (routePerm br d (tr2Of n K d (permList σ l)) i).1 < 2 * K
    · rw [bitsToNat_key2Arr_lt comb n K d _ _ hpi] at heq
      have hlt : bitsToNat (particleSym54 n (Nat.clog 2 n + 1) (permList σ l ⟨_, hpi⟩)) <
          2 ^ (Nat.clog 2 n + 1) := comb.bitsToNat_lt_two_pow _
      have hpow : 2 ^ d * bitsToNat (particleSym54 n (Nat.clog 2 n + 1) (permList σ l ⟨_, hpi⟩)) <
          2 ^ d * 2 ^ (Nat.clog 2 n + 1) := Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos d)
      rw [Nat.pow_add, Nat.mul_comm (2 ^ (Nat.clog 2 n + 1)) (2 ^ d)] at heq
      omega
    · rw [bitsToNat_key2Arr_ge comb n K d _ _ hpi] at heq
      exact Fin.ext (by omega)
  have hperm_eq : routeSort d (tr2Of n K d y) id =
      padPerm54 (2 * K) (arity d) hNM (tauOf br comb n K d hNM l hl y)⁻¹ := by
    funext i
    change (routePerm br d (tr2Of n K d y) i) = _
    by_cases hi : i.1 < 2 * K
    · apply Fin.ext
      rw [padPerm54_lt _ _ _ _ hi, htau_inv ⟨i.1, hi⟩]
    · have hge : 2 * K ≤ i.1 := Nat.le_of_not_lt hi
      rw [padPerm54_ge _ _ _ _ hge, hfix i hge]
  refine ⟨?_, hperm_eq⟩
  funext i
  rcases hy with ⟨σ, rfl⟩
  have hsort := sort_key2Arr_eq br comb n K d hNM l hl σ
  have hroute : routeSort d (tr2Of n K d (permList σ l)) (key2Arr n (Nat.clog 2 n + 1) K d (permList σ l)) =
      key2Arr n (Nat.clog 2 n + 1) K d l := by
    have h1 := br.routeSort_sortTrace (fun r => bitsToNat (recKey54 (w_p := 0) r)) d true
      (key2Arr n (Nat.clog 2 n + 1) K d (permList σ l))
    exact h1.trans hsort
  have heq := congrFun hroute ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩
  rw [br.routeSort_apply] at heq
  have hpi : (routePerm br d (tr2Of n K d (permList σ l)) ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1 < 2 * K := by
    have hv := htau_inv i
    rw [← hv]
    exact ((tauOf br comb n K d hNM l hl (permList σ l))⁻¹ i).isLt
  have hrec_sym : ∀ j : Fin (Nat.clog 2 n + 1),
      key2Arr n (Nat.clog 2 n + 1) K d (permList σ l)
        (routePerm br d (tr2Of n K d (permList σ l)) ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩)
        (Fin.castAdd d (Fin.natAdd 1 j)) =
      key2Arr n (Nat.clog 2 n + 1) K d l ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩
        (Fin.castAdd d (Fin.natAdd 1 j)) := fun j => congrFun heq _
  have hsym_eq : particleSym54 n (Nat.clog 2 n + 1)
      (permList σ l ((tauOf br comb n K d hNM l hl (permList σ l))⁻¹ i)) =
      particleSym54 n (Nat.clog 2 n + 1) (l i) := by
    funext j
    have h := hrec_sym j
    change (key2Arr n (Nat.clog 2 n + 1) K d (permList σ l)
      (routePerm br d (tr2Of n K d (permList σ l)) ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩))
        (Fin.castAdd d (Fin.natAdd 1 j)) =
      (key2Arr n (Nat.clog 2 n + 1) K d l ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩)
        (Fin.castAdd d (Fin.natAdd 1 j)) at h
    simp only [key2Arr, dif_pos hpi, dif_pos i.isLt, Fin.append_left, Fin.append_right] at h
    have hidx : (⟨(routePerm br d (tr2Of n K d (permList σ l)) ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1, hpi⟩ :
        Fin (2 * K)) = (tauOf br comb n K d hNM l hl (permList σ l))⁻¹ i := by
      ext; exact (htau_inv i).symm
    rw [hidx] at h
    exact h
  exact particleSym54_inj n hsym_eq

/-! ### 3. Additional `updateOn` / `flatReg` / `padKet` Combinators -/

@[simp] lemma flatReg_zero {N w : ℕ} :
    flatReg N w (fun _ _ => false) = fun _ => false := rfl

lemma flatReg_splitReg {N w : ℕ} (y : Qubits (N * w)) :
    flatReg N w (splitReg N w y) = y := by
  funext k
  dsimp [flatReg, splitReg]
  rw [Equiv.apply_symm_apply]

lemma splitReg_flatReg {N w : ℕ} (x : Fin N → Qubits w) :
    splitReg N w (flatReg N w x) = x := by
  funext i j
  dsimp [splitReg, flatReg]
  rw [Equiv.symm_apply_apply]

lemma updateOn_comp_disjoint {k1 k2 m : ℕ} (e1 : Fin k1 ↪ Fin m) (e2 : Fin k2 ↪ Fin m)
    (hdisj : ∀ i j, e1 i ≠ e2 j) (z : Qubits m) (val : Qubits k1) :
    updateOn e1 z val ∘ e2 = z ∘ e2 := by
  funext j
  apply updateOn_apply_not_mem
  rintro ⟨i, hi⟩
  exact hdisj i j hi

lemma updateOn_comm {k1 k2 m : ℕ} (e1 : Fin k1 ↪ Fin m) (e2 : Fin k2 ↪ Fin m)
    (hdisj : ∀ i j, e1 i ≠ e2 j) (z : Qubits m) (v1 : Qubits k1) (v2 : Qubits k2) :
    updateOn e1 (updateOn e2 z v2) v1 = updateOn e2 (updateOn e1 z v1) v2 := by
  funext u
  by_cases h1 : u ∈ Set.range e1
  · rcases h1 with ⟨i, rfl⟩
    have hnot2 : e1 i ∉ Set.range e2 := fun ⟨j, hj⟩ => hdisj i j hj.symm
    rw [updateOn_apply_emb, updateOn_apply_not_mem _ _ _ hnot2, updateOn_apply_emb]
  · rw [updateOn_apply_not_mem _ _ _ h1]
    by_cases h2 : u ∈ Set.range e2
    · rcases h2 with ⟨j, rfl⟩
      rw [updateOn_apply_emb, updateOn_apply_emb]
    · rw [updateOn_apply_not_mem _ _ _ h2, updateOn_apply_not_mem _ _ _ h2,
        updateOn_apply_not_mem _ _ _ h1]

lemma updateOn_eq_self_of_eq {k m : ℕ} (e : Fin k ↪ Fin m) (z : Qubits m) (v : Qubits k)
    (h : v = z ∘ e) : updateOn e z v = z := by
  funext u
  by_cases hu : u ∈ Set.range e
  · rcases hu with ⟨i, rfl⟩
    rw [updateOn_apply_emb, h, Function.comp_apply]
  · exact updateOn_apply_not_mem _ _ _ hu

lemma updateOn_combineEmb_padZero {a b m : ℕ} (eA : Fin a ↪ Fin m) (eB : Fin b ↪ Fin m)
    (hAB : ∀ i j, eA i ≠ eB j) (z : Qubits m) (hzB : z ∘ eB = fun _ => false) (x : Qubits a) :
    updateOn (combineEmb eA eB hAB) z (padZero a b x) = updateOn eA z x := by
  funext u
  by_cases hu : u ∈ Set.range (combineEmb eA eB hAB)
  · rcases hu with ⟨ij, rfl⟩
    induction ij using Fin.addCases with
    | left i =>
      rw [updateOn_apply_emb, combineEmb_castAdd, updateOn_apply_emb, padZero_castAdd]
    | right j =>
      have hnotA : eB j ∉ Set.range eA := fun ⟨i, hi⟩ => hAB i j hi
      rw [updateOn_apply_emb, combineEmb_natAdd, updateOn_apply_not_mem _ _ _ hnotA, padZero_natAdd]
      exact (congrFun hzB j).symm
  · have hnotA : u ∉ Set.range eA := fun ⟨i, hi⟩ => hu ⟨Fin.castAdd b i, by simpa using hi⟩
    rw [updateOn_apply_not_mem _ _ _ hu, updateOn_apply_not_mem _ _ _ hnotA]

lemma updateOn_packDTA54Emb {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) (arr : Fin N → Qubits w) (tr : Qubits T) :
    updateOn (packDTA54Emb eArr eTr eAnc hAT hAA hTA) z (packDTA54 N w T anc arr tr) =
      updateOn eTr (updateOn eArr z (flatReg N w arr)) tr := by
  funext u
  by_cases hu : u ∈ Set.range (packDTA54Emb eArr eTr eAnc hAT hAA hTA)
  · rcases hu with ⟨ijk, rfl⟩
    refine Fin.addCases (fun ij => ?_) (fun k => ?_) ijk
    · refine Fin.addCases (fun i => ?_) (fun j => ?_) ij
      · have hnotT : eArr i ∉ Set.range eTr := fun ⟨j, hj⟩ => hAT i j hj.symm
        rw [updateOn_apply_emb, packDTA54Emb_arr, updateOn_apply_not_mem _ _ _ hnotT,
          updateOn_apply_emb, packDTA54, padZero_castAdd, Fin.append_left]
      · rw [updateOn_apply_emb, packDTA54Emb_tr, updateOn_apply_emb, packDTA54,
          padZero_castAdd, Fin.append_right]
    · have hnotT : eAnc k ∉ Set.range eTr := fun ⟨j, hj⟩ => hTA j k hj
      have hnotA : eAnc k ∉ Set.range eArr := fun ⟨i, hi⟩ => hAA i k hi
      rw [updateOn_apply_emb, packDTA54Emb_anc, updateOn_apply_not_mem _ _ _ hnotT,
        updateOn_apply_not_mem _ _ _ hnotA, packDTA54, padZero_natAdd]
      exact (congrFun hzAnc k).symm
  · have hnotT : u ∉ Set.range eTr := fun ⟨j, hj⟩ =>
      hu ⟨Fin.castAdd anc (Fin.natAdd (N * w) j), by simpa using hj⟩
    have hnotA : u ∉ Set.range eArr := fun ⟨i, hi⟩ =>
      hu ⟨Fin.castAdd anc (Fin.castAdd T i), by simpa using hi⟩
    rw [updateOn_apply_not_mem _ _ _ hu, updateOn_apply_not_mem _ _ _ hnotT,
      updateOn_apply_not_mem _ _ _ hnotA]

@[simp] lemma flatReg_comp_slotInReg {N w : ℕ} (arr : Fin N → Qubits w) (j : Fin N) :
    flatReg N w arr ∘ slotInReg N w j = arr j := by
  funext b
  rw [Function.comp_apply, flatReg, slotInReg_apply, Equiv.symm_apply_apply]

lemma updateOn_slotEmb_comp_regEmb {m off N w : ℕ} (h : off + N * w ≤ m)
    (z : Qubits m) (arr : Fin N → Qubits w) (hz : z ∘ regEmb off N w h = flatReg N w arr)
    (j : Fin N) (val : Qubits w) :
    updateOn (slotEmb off N w h j) z val ∘ regEmb off N w h =
      flatReg N w (Function.update arr j val) := by
  funext idx
  rcases finProdFinEquiv.surjective idx with ⟨⟨q, b⟩, rfl⟩
  simp only [Function.comp_apply, flatReg, Equiv.symm_apply_apply]
  by_cases hq : q = j
  · subst hq
    change updateOn (slotEmb off N w h q) z val (slotEmb off N w h q b) =
      Function.update arr q val q b
    rw [updateOn_apply_emb, Function.update_self]
  · rw [Function.update_of_ne hq]
    have hnot : regEmb off N w h (finProdFinEquiv (q, b)) ∉ Set.range (slotEmb off N w h j) := by
      rintro ⟨b', hb'⟩
      have heq := (regEmb off N w h).injective hb'
      exact hq (Prod.ext_iff.mp (finProdFinEquiv.injective heq)).1.symm
    rw [updateOn_apply_not_mem _ _ _ hnot]
    have := congrFun hz (finProdFinEquiv (q, b))
    simpa [flatReg] using this

lemma act_seqList_finRange_step {m N : ℕ} (enc : ℕ → Qubits m) (circ : Fin N → LayeredCircuit m)
    (hstep : ∀ p : Fin N, act (circ p).unitary (ket (enc p.1)) = ket (enc (p.1 + 1))) :
    act (LayeredCircuit.seqList ((List.finRange N).map circ)).unitary (ket (enc 0)) = ket (enc N) := by
  suffices hdrop : ∀ d k, k ≤ N → d = N - k →
      act (LayeredCircuit.seqList (((List.finRange N).drop k).map circ)).unitary (ket (enc k)) =
        ket (enc N) by
    simpa using hdrop N 0 (Nat.zero_le N) (Nat.sub_zero N).symm
  intro d
  induction d with
  | zero =>
    intro k hk hd
    have hkN : k = N := by omega
    rw [hkN]
    have hlen : (List.finRange N).length ≤ N := by simp
    rw [List.drop_of_length_le hlen]
    simp [LayeredCircuit.seqList, act_one]
  | succ d' ih =>
    intro k hk hd
    have hklt : k < N := by omega
    have hdrop_eq : (List.finRange N).drop k =
        (List.finRange N)[k]'(by simp [hklt]) :: (List.finRange N).drop (k + 1) :=
      List.drop_eq_getElem_cons (by simp [hklt])
    have hget : (List.finRange N)[k]'(by simp [hklt]) = ⟨k, hklt⟩ := by simp
    rw [hdrop_eq, hget, List.map_cons, LayeredCircuit.seqList, LayeredCircuit.seq_unitary,
      act_mul, hstep ⟨k, hklt⟩]
    exact ih (k + 1) hklt (by omega)

lemma padKet_smul {N e : ℕ} (c : ℂ) (ψ : EuclideanSpace ℂ (Qubits N)) :
    padKet e (c • ψ) = c • padKet e ψ := by
  ext z
  dsimp [padKet]
  split_ifs with h
  · simp
  · simp

lemma padKet_sum {ι : Type*} {N e : ℕ} (s : Finset ι) (f : ι → EuclideanSpace ℂ (Qubits N)) :
    padKet e (∑ i ∈ s, f i) = ∑ i ∈ s, padKet e (f i) := by
  ext z
  have h1 : (WithLp.ofLp (∑ i ∈ s, f i)) (fun k => z (Fin.castAdd e k)) =
      ∑ i ∈ s, (WithLp.ofLp (f i)) (fun k => z (Fin.castAdd e k)) := by
    rw [WithLp.ofLp_sum, Finset.sum_apply]
  have h2 : (WithLp.ofLp (∑ i ∈ s, padKet e (f i))) z =
      ∑ i ∈ s, (WithLp.ofLp (padKet e (f i))) z := by
    rw [WithLp.ofLp_sum, Finset.sum_apply]
  change (WithLp.ofLp (padKet e (∑ i ∈ s, f i))) z = (WithLp.ofLp (∑ i ∈ s, padKet e (f i))) z
  rw [h2]
  dsimp [padKet]
  split_ifs with hz
  · exact h1
  · simp

lemma padSym_comp_padPerm54 (n s K d : ℕ) (hNM : 2 * K ≤ arity d)
    (l : Fin (2 * K) → Fin (n + 1)) (σ : Equiv.Perm (Fin (2 * K))) :
    padSym n s K d l ∘ padPerm54 (2 * K) (arity d) hNM σ =
      padSym n s K d (permList σ l) := by
  funext p
  by_cases hp : p.1 < 2 * K
  · have hp' : (padPerm54 (2 * K) (arity d) hNM σ p).1 < 2 * K := by
      rw [padPerm54_lt _ _ _ _ hp]
      exact (σ ⟨p.1, hp⟩).isLt
    simp only [Function.comp_apply, padSym, dif_pos hp', dif_pos hp]
    have hidx : (⟨(padPerm54 (2 * K) (arity d) hNM σ p).1, hp'⟩ : Fin (2 * K)) = σ ⟨p.1, hp⟩ := by
      ext; exact padPerm54_lt _ _ _ _ hp
    rw [hidx]
    rfl
  · have hge : 2 * K ≤ p.1 := Nat.le_of_not_lt hp
    simp only [Function.comp_apply, padPerm54_ge _ _ _ _ hge, padSym, dif_neg hp]

/-! ### 4. Circuit Construction & Stage-by-Stage Verification -/

lemma d_pos (K : ℕ) (hK : 1 ≤ K) : 1 ≤ Nat.clog 2 (2 * K) :=
  Nat.clog_pos (by norm_num) (by omega)

lemma two_mul_K_le_arity (K : ℕ) : 2 * K ≤ arity (Nat.clog 2 (2 * K)) := by
  rw [arity_eq_two_pow]
  exact Nat.le_pow_clog (by norm_num) (2 * K)

lemma arity_lt_four_mul_K (K : ℕ) (hK : 1 ≤ K) : arity (Nat.clog 2 (2 * K)) < 4 * K := by
  have hd : 1 ≤ Nat.clog 2 (2 * K) := d_pos K hK
  have hprev : 2 ^ (Nat.clog 2 (2 * K) - 1) < 2 * K := by
    by_contra hle
    have hge : 2 * K ≤ 2 ^ (Nat.clog 2 (2 * K) - 1) := Nat.le_of_not_lt hle
    have hclog : Nat.clog 2 (2 * K) ≤ Nat.clog 2 (2 * K) - 1 :=
      (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr hge
    omega
  rw [arity_eq_two_pow]
  have hpow : 2 ^ Nat.clog 2 (2 * K) = 2 * 2 ^ (Nat.clog 2 (2 * K) - 1) := by
    conv_lhs => rw [show Nat.clog 2 (2 * K) = (Nat.clog 2 (2 * K) - 1) + 1 by omega]
    rw [pow_succ']
  omega

section CircuitStages

variable (br : BitonicRouting54) (comb : LcgSym54Comb) (arith : LcgSym54ArithV2)
  (as : AlonsoSchottSil54) (hl : HarmBucketHL54V2)
  (n K : ℕ)

abbrev lay_s : ℕ := Nat.clog 2 n + 1
abbrev lay_d : ℕ := Nat.clog 2 (2 * K)
abbrev lay_M : ℕ := arity (lay_d K)
abbrev lay_w₂ : ℕ := (1 + lay_s n) + lay_d K
abbrev lay_tr : ℕ := sortTraceSize (lay_d K)

def lay_e : ℕ :=
  (lay_M K - 2 * K) * lay_s n +
    (lay_M K * lay_d K + lay_tr K + lay_d K + as.unifPermAnc (2 * K) (lay_d K) +
      lay_M K * lay_w₂ n K + lay_tr K + lay_w₂ n K + hl.harmBucketAnc n K (lay_d K))

abbrev lay_m : ℕ := 2 * K * lay_s n + lay_e as hl n K

def offReg1 : ℕ := 0
def offReg3 : ℕ := lay_M K * lay_s n
def offTr1 : ℕ := offReg3 n K + lay_M K * lay_d K
def offBk1 : ℕ := offTr1 n K + lay_tr K
def offUnif : ℕ := offBk1 n K + lay_d K
def offKey2 : ℕ := offUnif n K + as.unifPermAnc (2 * K) (lay_d K)
def offTr2 : ℕ := offKey2 as n K + lay_M K * lay_w₂ n K
def offBk2 : ℕ := offTr2 as n K + lay_tr K
def offHL : ℕ := offBk2 as n K + lay_w₂ n K

lemma lay_reg1_eq : lay_M K * lay_s n = 2 * K * lay_s n + (lay_M K - 2 * K) * lay_s n := by
  have hNM := two_mul_K_le_arity K
  rw [← Nat.add_mul, Nat.add_sub_of_le hNM]

lemma h_offHL_end :
    offHL as n K + hl.harmBucketAnc n K (lay_d K) = lay_m as hl n K := by
  dsimp only [offHL, offBk2, offTr2, offKey2, offUnif, offBk1, offTr1, offReg3, lay_m, lay_e]
  have := lay_reg1_eq n K
  omega

lemma h_reg1_le : offReg1 + lay_M K * lay_s n ≤ lay_m as hl n K := by
  have := h_offHL_end as hl n K
  dsimp only [offReg1, offHL, offBk2, offTr2, offKey2, offUnif, offBk1, offTr1, offReg3] at *
  omega

lemma h_reg3_le : offReg3 n K + lay_M K * lay_d K ≤ lay_m as hl n K := by
  have := h_offHL_end as hl n K
  dsimp only [offHL, offBk2, offTr2, offKey2, offUnif, offBk1, offTr1] at *
  omega

lemma h_tr1_le : offTr1 n K + lay_tr K ≤ lay_m as hl n K := by
  have := h_offHL_end as hl n K
  dsimp only [offHL, offBk2, offTr2, offKey2, offUnif, offBk1] at *
  omega

lemma h_bk1_le : offBk1 n K + lay_d K ≤ lay_m as hl n K := by
  have := h_offHL_end as hl n K
  dsimp only [offHL, offBk2, offTr2, offKey2, offUnif] at *
  omega

lemma h_unif_le : offUnif n K + as.unifPermAnc (2 * K) (lay_d K) ≤ lay_m as hl n K := by
  have := h_offHL_end as hl n K
  dsimp only [offHL, offBk2, offTr2, offKey2] at *
  omega

lemma h_key2_le : offKey2 as n K + lay_M K * lay_w₂ n K ≤ lay_m as hl n K := by
  have := h_offHL_end as hl n K
  dsimp only [offHL, offBk2, offTr2] at *
  omega

lemma h_tr2_le : offTr2 as n K + lay_tr K ≤ lay_m as hl n K := by
  have := h_offHL_end as hl n K
  dsimp only [offHL, offBk2] at *
  omega

lemma h_bk2_le : offBk2 as n K + lay_w₂ n K ≤ lay_m as hl n K := by
  have := h_offHL_end as hl n K
  dsimp only [offHL] at *
  omega

lemma h_hl_le : offHL as n K + hl.harmBucketAnc n K (lay_d K) ≤ lay_m as hl n K := by
  rw [h_offHL_end]

def embReg1 : Fin (lay_M K * lay_s n) ↪ Fin (lay_m as hl n K) :=
  sliceEmb offReg1 (lay_M K * lay_s n) (h_reg1_le as hl n K)

def embReg3 : Fin (lay_M K * lay_d K) ↪ Fin (lay_m as hl n K) :=
  sliceEmb (offReg3 n K) (lay_M K * lay_d K) (h_reg3_le as hl n K)

def embTr1 : Fin (lay_tr K) ↪ Fin (lay_m as hl n K) :=
  sliceEmb (offTr1 n K) (lay_tr K) (h_tr1_le as hl n K)

def embBk1 : Fin (lay_d K) ↪ Fin (lay_m as hl n K) :=
  sliceEmb (offBk1 n K) (lay_d K) (h_bk1_le as hl n K)

def embUnifAnc : Fin (as.unifPermAnc (2 * K) (lay_d K)) ↪ Fin (lay_m as hl n K) :=
  sliceEmb (offUnif n K) (as.unifPermAnc (2 * K) (lay_d K)) (h_unif_le as hl n K)

def embKey2 : Fin (lay_M K * lay_w₂ n K) ↪ Fin (lay_m as hl n K) :=
  sliceEmb (offKey2 as n K) (lay_M K * lay_w₂ n K) (h_key2_le as hl n K)

def embTr2 : Fin (lay_tr K) ↪ Fin (lay_m as hl n K) :=
  sliceEmb (offTr2 as n K) (lay_tr K) (h_tr2_le as hl n K)

def embBk2 : Fin (lay_w₂ n K) ↪ Fin (lay_m as hl n K) :=
  sliceEmb (offBk2 as n K) (lay_w₂ n K) (h_bk2_le as hl n K)

def embHLAnc : Fin (hl.harmBucketAnc n K (lay_d K)) ↪ Fin (lay_m as hl n K) :=
  sliceEmb (offHL as n K) (hl.harmBucketAnc n K (lay_d K)) (h_hl_le as hl n K)

lemma slice_disj_auto {o1 l1 o2 l2 : ℕ} (h1 : o1 + l1 ≤ lay_m as hl n K)
    (h2 : o2 + l2 ≤ lay_m as hl n K) (h : o1 + l1 ≤ o2) :
    ∀ i j, sliceEmb o1 l1 h1 i ≠ sliceEmb o2 l2 h2 j :=
  sliceEmb_disjoint h1 h2 (Or.inl h)

lemma slice_disj_auto_sym {o1 l1 o2 l2 : ℕ} (h1 : o1 + l1 ≤ lay_m as hl n K)
    (h2 : o2 + l2 ≤ lay_m as hl n K) (h : o2 + l2 ≤ o1) :
    ∀ i j, sliceEmb o1 l1 h1 i ≠ sliceEmb o2 l2 h2 j :=
  sliceEmb_disjoint h1 h2 (Or.inr h)

/-! Sub-embeddings into `reg1` and `key2` slots -/

def reg1Slot (p : Fin (lay_M K)) : Fin (lay_s n) ↪ Fin (lay_m as hl n K) :=
  slotEmb offReg1 (lay_M K) (lay_s n) (h_reg1_le as hl n K) p

def w2PadIn : Fin 1 ↪ Fin (lay_w₂ n K) where
  toFun b := Fin.castAdd (lay_d K) (Fin.castAdd (lay_s n) b)
  inj' a b h := by
    have hv := congrArg Fin.val h
    exact Fin.ext (by dsimp at hv; exact hv)

def w2SymIn : Fin (lay_s n) ↪ Fin (lay_w₂ n K) where
  toFun b := Fin.castAdd (lay_d K) (Fin.natAdd 1 b)
  inj' a b h := by
    have hv := congrArg Fin.val h
    exact Fin.ext (by simp at hv; exact hv)

def w2IdxIn : Fin (lay_d K) ↪ Fin (lay_w₂ n K) where
  toFun b := Fin.natAdd (1 + lay_s n) b
  inj' a b h := by
    have hv := congrArg Fin.val h
    exact Fin.ext (by simp at hv; exact hv)

def key2Slot (p : Fin (lay_M K)) : Fin (lay_w₂ n K) ↪ Fin (lay_m as hl n K) :=
  slotEmb (offKey2 as n K) (lay_M K) (lay_w₂ n K) (h_key2_le as hl n K) p

def key2PadBit (p : Fin (lay_M K)) : Fin 1 ↪ Fin (lay_m as hl n K) :=
  (w2PadIn n K).trans (key2Slot as hl n K p)

def key2SymSlot (p : Fin (lay_M K)) : Fin (lay_s n) ↪ Fin (lay_m as hl n K) :=
  (w2SymIn n K).trans (key2Slot as hl n K p)

def key2IdxSlot (p : Fin (lay_M K)) : Fin (lay_d K) ↪ Fin (lay_m as hl n K) :=
  (w2IdxIn n K).trans (key2Slot as hl n K p)

def key2LiveInKey2 : Fin (2 * K * lay_s n) ↪ Fin (lay_M K * lay_w₂ n K) where
  toFun u :=
    let pb := finProdFinEquiv.symm u
    slotInReg (lay_M K) (lay_w₂ n K) ⟨pb.1.1, lt_of_lt_of_le pb.1.isLt (two_mul_K_le_arity K)⟩
      (w2SymIn n K pb.2)
  inj' u₁ u₂ h := by
    have h1 := Prod.ext_iff.mp (finProdFinEquiv.injective h)
    have hp : (finProdFinEquiv.symm u₁).1 = (finProdFinEquiv.symm u₂).1 :=
      Fin.ext (by simpa using congrArg Fin.val h1.1)
    have hb : (finProdFinEquiv.symm u₁).2 = (finProdFinEquiv.symm u₂).2 :=
      (w2SymIn n K).injective h1.2
    exact finProdFinEquiv.symm.injective (Prod.ext hp hb)

def embKey2Live : Fin (2 * K * lay_s n) ↪ Fin (lay_m as hl n K) :=
  (key2LiveInKey2 n K).trans (embKey2 as hl n K)

lemma reg1Slot_disjoint_key2SymSlot (p q : Fin (lay_M K)) :
    ∀ i j, reg1Slot as hl n K p i ≠ key2SymSlot as hl n K q j := by
  intro i j
  exact slice_disj_auto as hl n K (h_reg1_le as hl n K) (h_key2_le as hl n K)
    (by dsimp only [offReg1, offKey2, offUnif, offBk1, offTr1, offReg3]; omega) _ _

/-! Helper lemmas for `mkState54` -/

noncomputable def mkState54
    (r1 : Fin (lay_M K) → Qubits (lay_s n))
    (r3 : Fin (lay_M K) → Qubits (lay_d K))
    (t1 : Qubits (lay_tr K))
    (k2 : Fin (lay_M K) → Qubits (lay_w₂ n K))
    (t2 : Qubits (lay_tr K)) : Qubits (lay_m as hl n K) :=
  updateOn (embTr2 as hl n K)
    (updateOn (embKey2 as hl n K)
      (updateOn (embTr1 as hl n K)
        (updateOn (embReg3 as hl n K)
          (updateOn (embReg1 as hl n K) (fun _ => false) (flatReg (lay_M K) (lay_s n) r1))
          (flatReg (lay_M K) (lay_d K) r3))
        t1)
      (flatReg (lay_M K) (lay_w₂ n K) k2))
    t2

/-! Disjointness macro lemmas for `mkState54` -/

lemma embReg1_disj_embReg3 : ∀ i j, embReg1 as hl n K i ≠ embReg3 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offReg1, offReg3]; omega)
lemma embReg1_disj_embTr1 : ∀ i j, embReg1 as hl n K i ≠ embTr1 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offReg1, offTr1, offReg3]; omega)
lemma embReg1_disj_embKey2 : ∀ i j, embReg1 as hl n K i ≠ embKey2 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offReg1, offKey2, offUnif, offBk1, offTr1, offReg3]; omega)
lemma embReg1_disj_embTr2 : ∀ i j, embReg1 as hl n K i ≠ embTr2 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offReg1, offTr2, offKey2, offUnif, offBk1, offTr1, offReg3]; omega)

lemma embReg3_disj_embTr1 : ∀ i j, embReg3 as hl n K i ≠ embTr1 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offTr1]; omega)
lemma embReg3_disj_embBk1 : ∀ i j, embReg3 as hl n K i ≠ embBk1 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offBk1, offTr1]; omega)
lemma embReg3_disj_embUnifAnc : ∀ i j, embReg3 as hl n K i ≠ embUnifAnc as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offUnif, offBk1, offTr1]; omega)
lemma embReg3_disj_embKey2 : ∀ i j, embReg3 as hl n K i ≠ embKey2 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offKey2, offUnif, offBk1, offTr1]; omega)
lemma embReg3_disj_embTr2 : ∀ i j, embReg3 as hl n K i ≠ embTr2 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offTr2, offKey2, offUnif, offBk1, offTr1]; omega)
lemma embReg3_disj_embHLAnc : ∀ i j, embReg3 as hl n K i ≠ embHLAnc as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offHL, offBk2, offTr2, offKey2, offUnif, offBk1, offTr1]; omega)

lemma embTr1_disj_embBk1 : ∀ i j, embTr1 as hl n K i ≠ embBk1 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offBk1]; omega)
lemma embTr1_disj_embKey2 : ∀ i j, embTr1 as hl n K i ≠ embKey2 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offKey2, offUnif, offBk1]; omega)
lemma embTr1_disj_embTr2 : ∀ i j, embTr1 as hl n K i ≠ embTr2 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offTr2, offKey2, offUnif, offBk1]; omega)

lemma embKey2_disj_embTr2 : ∀ i j, embKey2 as hl n K i ≠ embTr2 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offTr2]; omega)
lemma embKey2_disj_embBk2 : ∀ i j, embKey2 as hl n K i ≠ embBk2 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offBk2, offTr2]; omega)
lemma embKey2_disj_embHLAnc : ∀ i j, embKey2 as hl n K i ≠ embHLAnc as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offHL, offBk2, offTr2]; omega)

lemma embTr2_disj_embBk2 : ∀ i j, embTr2 as hl n K i ≠ embBk2 as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offBk2]; omega)
lemma embTr2_disj_embHLAnc : ∀ i j, embTr2 as hl n K i ≠ embHLAnc as hl n K j :=
  slice_disj_auto as hl n K _ _ (by dsimp only [offHL, offBk2]; omega)

lemma mkState54_comp_reg1 (r1 r3 t1 k2 t2) :
    mkState54 as hl n K r1 r3 t1 k2 t2 ∘ embReg1 as hl n K = flatReg (lay_M K) (lay_s n) r1 := by
  unfold mkState54
  rw [updateOn_comp_disjoint _ _ (fun i j => (embReg1_disj_embTr2 as hl n K j i).symm)]
  rw [updateOn_comp_disjoint _ _ (fun i j => (embReg1_disj_embKey2 as hl n K j i).symm)]
  rw [updateOn_comp_disjoint _ _ (fun i j => (embReg1_disj_embTr1 as hl n K j i).symm)]
  rw [updateOn_comp_disjoint _ _ (fun i j => (embReg1_disj_embReg3 as hl n K j i).symm)]
  exact updateOn_comp_self _ _ _

lemma mkState54_comp_reg3 (r1 r3 t1 k2 t2) :
    mkState54 as hl n K r1 r3 t1 k2 t2 ∘ embReg3 as hl n K = flatReg (lay_M K) (lay_d K) r3 := by
  unfold mkState54
  rw [updateOn_comp_disjoint _ _ (fun i j => (embReg3_disj_embTr2 as hl n K j i).symm)]
  rw [updateOn_comp_disjoint _ _ (fun i j => (embReg3_disj_embKey2 as hl n K j i).symm)]
  rw [updateOn_comp_disjoint _ _ (fun i j => (embReg3_disj_embTr1 as hl n K j i).symm)]
  exact updateOn_comp_self _ _ _

lemma mkState54_comp_tr1 (r1 r3 t1 k2 t2) :
    mkState54 as hl n K r1 r3 t1 k2 t2 ∘ embTr1 as hl n K = t1 := by
  unfold mkState54
  rw [updateOn_comp_disjoint _ _ (fun i j => (embTr1_disj_embTr2 as hl n K j i).symm)]
  rw [updateOn_comp_disjoint _ _ (fun i j => (embTr1_disj_embKey2 as hl n K j i).symm)]
  exact updateOn_comp_self _ _ _

lemma mkState54_comp_key2 (r1 r3 t1 k2 t2) :
    mkState54 as hl n K r1 r3 t1 k2 t2 ∘ embKey2 as hl n K = flatReg (lay_M K) (lay_w₂ n K) k2 := by
  unfold mkState54
  rw [updateOn_comp_disjoint _ _ (fun i j => (embKey2_disj_embTr2 as hl n K j i).symm)]
  exact updateOn_comp_self _ _ _

lemma mkState54_comp_tr2 (r1 r3 t1 k2 t2) :
    mkState54 as hl n K r1 r3 t1 k2 t2 ∘ embTr2 as hl n K = t2 :=
  updateOn_comp_self _ _ _

lemma mkState54_comp_other {len : ℕ} (e : Fin len ↪ Fin (lay_m as hl n K))
    (h1 : ∀ i j, embReg1 as hl n K i ≠ e j)
    (h3 : ∀ i j, embReg3 as hl n K i ≠ e j)
    (ht1 : ∀ i j, embTr1 as hl n K i ≠ e j)
    (hk2 : ∀ i j, embKey2 as hl n K i ≠ e j)
    (ht2 : ∀ i j, embTr2 as hl n K i ≠ e j)
    (r1 r3 t1 k2 t2) :
    mkState54 as hl n K r1 r3 t1 k2 t2 ∘ e = fun _ => false := by
  unfold mkState54
  rw [updateOn_comp_disjoint _ _ ht2, updateOn_comp_disjoint _ _ hk2,
    updateOn_comp_disjoint _ _ ht1, updateOn_comp_disjoint _ _ h3,
    updateOn_comp_disjoint _ _ h1]
  rfl

lemma mkState54_comp_bk1 (r1 r3 t1 k2 t2) :
    mkState54 as hl n K r1 r3 t1 k2 t2 ∘ embBk1 as hl n K = fun _ => false :=
  mkState54_comp_other as hl n K (embBk1 as hl n K)
    (slice_disj_auto as hl n K _ _ (by dsimp only [offReg1, offBk1, offTr1, offReg3]; omega))
    (embReg3_disj_embBk1 as hl n K)
    (embTr1_disj_embBk1 as hl n K)
    (slice_disj_auto_sym as hl n K _ _ (by dsimp only [offKey2, offUnif, offBk1]; omega))
    (slice_disj_auto_sym as hl n K _ _ (by dsimp only [offTr2, offKey2, offUnif, offBk1]; omega))
    r1 r3 t1 k2 t2

lemma mkState54_comp_unifAnc (r1 r3 t1 k2 t2) :
    mkState54 as hl n K r1 r3 t1 k2 t2 ∘ embUnifAnc as hl n K = fun _ => false :=
  mkState54_comp_other as hl n K (embUnifAnc as hl n K)
    (slice_disj_auto as hl n K _ _ (by dsimp only [offReg1, offUnif, offBk1, offTr1, offReg3]; omega))
    (embReg3_disj_embUnifAnc as hl n K)
    (slice_disj_auto as hl n K _ _ (by dsimp only [offTr1, offUnif, offBk1]; omega))
    (slice_disj_auto_sym as hl n K _ _ (by dsimp only [offKey2, offUnif]; omega))
    (slice_disj_auto_sym as hl n K _ _ (by dsimp only [offTr2, offKey2, offUnif]; omega))
    r1 r3 t1 k2 t2

lemma mkState54_comp_bk2 (r1 r3 t1 k2 t2) :
    mkState54 as hl n K r1 r3 t1 k2 t2 ∘ embBk2 as hl n K = fun _ => false :=
  mkState54_comp_other as hl n K (embBk2 as hl n K)
    (slice_disj_auto as hl n K _ _ (by dsimp only [offReg1, offBk2, offTr2, offKey2, offUnif, offBk1, offTr1, offReg3]; omega))
    (slice_disj_auto as hl n K _ _ (by dsimp only [offBk2, offTr2, offKey2, offUnif, offBk1, offTr1]; omega))
    (slice_disj_auto as hl n K _ _ (by dsimp only [offBk2, offTr2, offKey2, offUnif, offBk1]; omega))
    (embKey2_disj_embBk2 as hl n K)
    (embTr2_disj_embBk2 as hl n K)
    r1 r3 t1 k2 t2

lemma mkState54_comp_hlAnc (r1 r3 t1 k2 t2) :
    mkState54 as hl n K r1 r3 t1 k2 t2 ∘ embHLAnc as hl n K = fun _ => false :=
  mkState54_comp_other as hl n K (embHLAnc as hl n K)
    (slice_disj_auto as hl n K _ _ (by dsimp only [offReg1, offHL, offBk2, offTr2, offKey2, offUnif, offBk1, offTr1, offReg3]; omega))
    (embReg3_disj_embHLAnc as hl n K)
    (slice_disj_auto as hl n K _ _ (by dsimp only [offHL, offBk2, offTr2, offKey2, offUnif, offBk1]; omega))
    (embKey2_disj_embHLAnc as hl n K)
    (embTr2_disj_embHLAnc as hl n K)
    r1 r3 t1 k2 t2

lemma updateOn_tr2_mkState54 (r1 r3 t1 k2 t2 t2') :
    updateOn (embTr2 as hl n K) (mkState54 as hl n K r1 r3 t1 k2 t2) t2' =
      mkState54 as hl n K r1 r3 t1 k2 t2' :=
  updateOn_updateOn_self _ _ _ _

lemma updateOn_key2_mkState54 (r1 r3 t1 k2 t2 k2') :
    updateOn (embKey2 as hl n K) (mkState54 as hl n K r1 r3 t1 k2 t2) (flatReg (lay_M K) (lay_w₂ n K) k2') =
      mkState54 as hl n K r1 r3 t1 k2' t2 := by
  unfold mkState54
  rw [updateOn_comm _ _ (fun i j => (embKey2_disj_embTr2 as hl n K i j)), updateOn_updateOn_self]

lemma updateOn_tr1_mkState54 (r1 r3 t1 k2 t2 t1') :
    updateOn (embTr1 as hl n K) (mkState54 as hl n K r1 r3 t1 k2 t2) t1' =
      mkState54 as hl n K r1 r3 t1' k2 t2 := by
  unfold mkState54
  rw [updateOn_comm _ _ (embTr1_disj_embTr2 as hl n K)]
  rw [updateOn_comm _ _ (embTr1_disj_embKey2 as hl n K)]
  rw [updateOn_updateOn_self]

lemma updateOn_reg3_mkState54 (r1 r3 t1 k2 t2 r3') :
    updateOn (embReg3 as hl n K) (mkState54 as hl n K r1 r3 t1 k2 t2) (flatReg (lay_M K) (lay_d K) r3') =
      mkState54 as hl n K r1 r3' t1 k2 t2 := by
  unfold mkState54
  rw [updateOn_comm _ _ (embReg3_disj_embTr2 as hl n K)]
  rw [updateOn_comm _ _ (embReg3_disj_embKey2 as hl n K)]
  rw [updateOn_comm _ _ (embReg3_disj_embTr1 as hl n K)]
  rw [updateOn_updateOn_self]

lemma updateOn_reg1_mkState54 (r1 r3 t1 k2 t2 r1') :
    updateOn (embReg1 as hl n K) (mkState54 as hl n K r1 r3 t1 k2 t2) (flatReg (lay_M K) (lay_s n) r1') =
      mkState54 as hl n K r1' r3 t1 k2 t2 := by
  unfold mkState54
  rw [updateOn_comm _ _ (embReg1_disj_embTr2 as hl n K)]
  rw [updateOn_comm _ _ (embReg1_disj_embKey2 as hl n K)]
  rw [updateOn_comm _ _ (embReg1_disj_embTr1 as hl n K)]
  rw [updateOn_comm _ _ (embReg1_disj_embReg3 as hl n K)]
  rw [updateOn_updateOn_self]

lemma mkState54_eq_padZero (y : Fin (2 * K) → Fin (n + 1)) :
    mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) (fun _ _ => false) (fun _ => false)
      (fun _ _ => false) (fun _ => false) =
      padZero (2 * K * lay_s n) (lay_e as hl n K)
        (flatReg (2 * K) (lay_s n) fun p => particleSym54 n (lay_s n) (y p)) := by
  have hzero : mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) (fun _ _ => false)
      (fun _ => false) (fun _ _ => false) (fun _ => false) =
      updateOn (embReg1 as hl n K) (fun _ => false)
        (flatReg (lay_M K) (lay_s n) (padSym n (lay_s n) K (lay_d K) y)) := by
    unfold mkState54
    have hz1 : updateOn (embReg3 as hl n K)
        (updateOn (embReg1 as hl n K) (fun _ => false) (flatReg (lay_M K) (lay_s n) (padSym n (lay_s n) K (lay_d K) y)))
        (fun _ => false) =
        updateOn (embReg1 as hl n K) (fun _ => false) (flatReg (lay_M K) (lay_s n) (padSym n (lay_s n) K (lay_d K) y)) := by
      refine updateOn_eq_self_of_eq _ _ _ ?_
      rw [updateOn_comp_disjoint _ _ (embReg1_disj_embReg3 as hl n K)]
      rfl
    have hz2 : updateOn (embTr1 as hl n K)
        (updateOn (embReg1 as hl n K) (fun _ => false) (flatReg (lay_M K) (lay_s n) (padSym n (lay_s n) K (lay_d K) y)))
        (fun _ => false) =
        updateOn (embReg1 as hl n K) (fun _ => false) (flatReg (lay_M K) (lay_s n) (padSym n (lay_s n) K (lay_d K) y)) := by
      refine updateOn_eq_self_of_eq _ _ _ ?_
      rw [updateOn_comp_disjoint _ _ (embReg1_disj_embTr1 as hl n K)]
      rfl
    have hz3 : updateOn (embKey2 as hl n K)
        (updateOn (embReg1 as hl n K) (fun _ => false) (flatReg (lay_M K) (lay_s n) (padSym n (lay_s n) K (lay_d K) y)))
        (fun _ => false) =
        updateOn (embReg1 as hl n K) (fun _ => false) (flatReg (lay_M K) (lay_s n) (padSym n (lay_s n) K (lay_d K) y)) := by
      refine updateOn_eq_self_of_eq _ _ _ ?_
      rw [updateOn_comp_disjoint _ _ (embReg1_disj_embKey2 as hl n K)]
      rfl
    have hz4 : updateOn (embTr2 as hl n K)
        (updateOn (embReg1 as hl n K) (fun _ => false) (flatReg (lay_M K) (lay_s n) (padSym n (lay_s n) K (lay_d K) y)))
        (fun _ => false) =
        updateOn (embReg1 as hl n K) (fun _ => false) (flatReg (lay_M K) (lay_s n) (padSym n (lay_s n) K (lay_d K) y)) := by
      refine updateOn_eq_self_of_eq _ _ _ ?_
      rw [updateOn_comp_disjoint _ _ (embReg1_disj_embTr2 as hl n K)]
      rfl
    simp only [flatReg_zero]
    rw [hz1, hz2, hz3, hz4]
  rw [hzero]
  funext u
  by_cases hu : u.1 < 2 * K * lay_s n
  · have huM : u.1 < lay_M K * lay_s n := by
      have := two_mul_K_le_arity K
      nlinarith
    have hu_emb : u = embReg1 as hl n K ⟨u.1, huM⟩ := Fin.ext (by simp [embReg1, offReg1])
    conv_lhs => rw [hu_emb, updateOn_apply_emb]
    rw [padZero_val_lt _ u hu]
    let pb := finProdFinEquiv.symm (⟨u.1, hu⟩ : Fin (2 * K * lay_s n))
    have hpb_eq : finProdFinEquiv pb = (⟨u.1, hu⟩ : Fin (2 * K * lay_s n)) :=
      finProdFinEquiv.apply_symm_apply _
    have hval_mul : pb.2.1 + lay_s n * pb.1.1 = u.1 := by
      have hv := congrArg Fin.val hpb_eq
      simpa [finProdFinEquiv] using hv
    have hpM : pb.1.1 < lay_M K := lt_of_lt_of_le pb.1.isLt (two_mul_K_le_arity K)
    have hfinM : (⟨u.1, huM⟩ : Fin (lay_M K * lay_s n)) = finProdFinEquiv (⟨pb.1.1, hpM⟩, pb.2) := by
      ext; simp [finProdFinEquiv]; omega
    rw [hfinM]
    simp only [flatReg, Equiv.symm_apply_apply, padSym, dif_pos pb.1.isLt]
    rw [show (⟨u.1, hu⟩ : Fin (2 * K * lay_s n)) = finProdFinEquiv pb from hpb_eq.symm]
    simp only [Equiv.symm_apply_apply]
  · rw [padZero_val_ge _ u (Nat.le_of_not_lt hu)]
    by_cases huM : u.1 < lay_M K * lay_s n
    · have hu_emb : u = embReg1 as hl n K ⟨u.1, huM⟩ := Fin.ext (by simp [embReg1, offReg1])
      conv_lhs => rw [hu_emb, updateOn_apply_emb]
      let pbM := finProdFinEquiv.symm (⟨u.1, huM⟩ : Fin (lay_M K * lay_s n))
      have hpbM_eq : finProdFinEquiv pbM = (⟨u.1, huM⟩ : Fin (lay_M K * lay_s n)) :=
        finProdFinEquiv.apply_symm_apply _
      have hval_mul : pbM.2.1 + lay_s n * pbM.1.1 = u.1 := by
        have hv := congrArg Fin.val hpbM_eq
        simpa [finProdFinEquiv] using hv
      have hge_p : ¬ (finProdFinEquiv.symm (⟨u.1, huM⟩ : Fin (lay_M K * lay_s n))).1.1 < 2 * K := by
        intro hlt
        have hlt' : pbM.1.1 < 2 * K := hlt
        have hb := pbM.2.isLt
        have hlt2 : pbM.2.1 + lay_s n * pbM.1.1 < 2 * K * lay_s n := by
          have : lay_s n * (pbM.1.1 + 1) ≤ lay_s n * (2 * K) := Nat.mul_le_mul_left _ hlt'
          linarith [Nat.mul_succ (lay_s n) pbM.1.1, Nat.mul_comm (2 * K) (lay_s n)]
        omega
      simp only [flatReg, padSym, dif_neg hge_p]
    · have hnot : u ∉ Set.range (embReg1 as hl n K) := by
        rintro ⟨j, rfl⟩
        have := j.isLt
        simp only [embReg1, sliceEmb_apply, offReg1, zero_add] at huM
        exact huM this
      rw [updateOn_apply_not_mem _ _ _ hnot]

/-! ### Stage Definitions (`circ0`, `circ1`, `circ2a`..`circ2f`, `fullCirc`) -/

def emb0 : Fin (lay_M K * lay_d K + as.unifPermAnc (2 * K) (lay_d K)) ↪ Fin (lay_m as hl n K) :=
  combineEmb (embReg3 as hl n K) (embUnifAnc as hl n K) (embReg3_disj_embUnifAnc as hl n K)

def circ0 (hK : 1 ≤ K) : LayeredCircuit (lay_m as hl n K) :=
  (as.unifPermCircuit (2 * K) (lay_d K) (by omega) (d_pos K hK) (two_mul_K_le_arity K)).mapWires
    (emb0 as hl n K)

def emb1a : Fin ((lay_M K * lay_d K + lay_tr K) + lay_d K) ↪ Fin (lay_m as hl n K) :=
  packDTA54Emb (embReg3 as hl n K) (embTr1 as hl n K) (embBk1 as hl n K)
    (embReg3_disj_embTr1 as hl n K) (embReg3_disj_embBk1 as hl n K) (embTr1_disj_embBk1 as hl n K)

def circ1a : LayeredCircuit (lay_m as hl n K) :=
  (br.bitonicSortKeyCircuit (lay_d K) (lay_d K) 0 true).mapWires (emb1a as hl n K)

def emb1b : Fin (lay_M K * lay_s n + lay_tr K) ↪ Fin (lay_m as hl n K) :=
  combineEmb (embReg1 as hl n K) (embTr1 as hl n K) (embReg1_disj_embTr1 as hl n K)

def circ1b : LayeredCircuit (lay_m as hl n K) :=
  (br.unrouteSortCircuit (lay_d K) (lay_s n)).mapWires (emb1b as hl n K)

def circ1 : LayeredCircuit (lay_m as hl n K) :=
  ((circ1a br as hl n K).seq (circ1b br as hl n K)).seq (circ1a br as hl n K).adj

def circ2aSlot (p : Fin (lay_M K)) : LayeredCircuit (lay_m as hl n K) :=
  if _ : p.1 < 2 * K then
    (arith.copyRegCircuit (lay_s n)).mapWires
      (combineEmb (reg1Slot as hl n K p) (key2SymSlot as hl n K p)
        (reg1Slot_disjoint_key2SymSlot as hl n K p p))
  else
    ((arith.setConstMSBCircuit 1 1).mapWires (key2PadBit as hl n K p)).seq
      ((arith.setConstMSBCircuit (lay_d K) p.1).mapWires (key2IdxSlot as hl n K p))

def circ2a : LayeredCircuit (lay_m as hl n K) :=
  LayeredCircuit.seqList ((List.finRange (lay_M K)).map (circ2aSlot arith as hl n K))

def emb2b : Fin ((lay_M K * lay_w₂ n K + lay_tr K) + lay_w₂ n K) ↪ Fin (lay_m as hl n K) :=
  packDTA54Emb (embKey2 as hl n K) (embTr2 as hl n K) (embBk2 as hl n K)
    (embKey2_disj_embTr2 as hl n K) (embKey2_disj_embBk2 as hl n K) (embTr2_disj_embBk2 as hl n K)

def circ2b : LayeredCircuit (lay_m as hl n K) :=
  (br.bitonicSortKeyCircuit (lay_d K) (lay_w₂ n K) 0 true).mapWires (emb2b as hl n K)

def emb2c : Fin (lay_M K * lay_d K + lay_tr K) ↪ Fin (lay_m as hl n K) :=
  combineEmb (embReg3 as hl n K) (embTr2 as hl n K) (embReg3_disj_embTr2 as hl n K)

def circ2c : LayeredCircuit (lay_m as hl n K) :=
  (br.routeSortCircuit (lay_d K) (lay_d K)).mapWires (emb2c as hl n K)

lemma embKey2Live_disj_embReg3 : ∀ i j, embKey2Live as hl n K i ≠ embReg3 as hl n K j :=
  fun i j h => (embReg3_disj_embKey2 as hl n K j (key2LiveInKey2 n K i)) h.symm

lemma embKey2Live_disj_embHLAnc : ∀ i j, embKey2Live as hl n K i ≠ embHLAnc as hl n K j :=
  fun i j => embKey2_disj_embHLAnc as hl n K (key2LiveInKey2 n K i) j

def emb2d : Fin ((2 * K * lay_s n + lay_M K * lay_d K) + hl.harmBucketAnc n K (lay_d K)) ↪
    Fin (lay_m as hl n K) :=
  combineEmb
    (combineEmb (embKey2Live as hl n K) (embReg3 as hl n K) (embKey2Live_disj_embReg3 as hl n K))
    (embHLAnc as hl n K)
    (emb_disjoint_combineEmb (embKey2Live_disj_embReg3 as hl n K)
      (embKey2Live_disj_embHLAnc as hl n K) (embReg3_disj_embHLAnc as hl n K))

def circ2d (hn : 1 ≤ n) (hK : 1 ≤ K) : LayeredCircuit (lay_m as hl n K) :=
  ((hl.harmBucketH_lCircuit n K (lay_d K) hn hK (d_pos K hK) (two_mul_K_le_arity K)).mapWires
    (emb2d as hl n K)).adj

def fullCirc (hn : 1 ≤ n) (hK : 1 ≤ K) : LayeredCircuit (lay_m as hl n K) :=
  LayeredCircuit.seqList
    [ circ0 as hl n K hK
    , circ1 br as hl n K
    , circ2a arith as hl n K
    , circ2b br as hl n K
    , circ2c br as hl n K
    , circ2d as hl n K hn hK
    , (circ2b br as hl n K).adj
    , (circ2a arith as hl n K).adj
    ]

/-! ### Stage-by-Stage Correctness Proofs -/

lemma act_circ0 (hK : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1)) :
    act (circ0 as hl n K hK).unitary
        (ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) l) (fun _ _ => false)
          (fun _ => false) (fun _ _ => false) (fun _ => false))) =
      ((1 / Real.sqrt (Nat.factorial (2 * K) : ℝ) : ℝ) : ℂ) •
        ∑ σ : Equiv.Perm (Fin (2 * K)),
          ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) l)
            (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
            (fun _ => false) (fun _ _ => false) (fun _ => false)) := by
  let z0 := mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) l) (fun _ _ => false)
    (fun _ => false) (fun _ _ => false) (fun _ => false)
  have hz0 : z0 ∘ emb0 as hl n K = fun _ => false := by
    funext u
    refine Fin.addCases (fun i => ?_) (fun j => ?_) u
    · simp only [Function.comp_apply, emb0, combineEmb_castAdd]
      exact congrFun (mkState54_comp_reg3 as hl n K _ _ _ _ _) i
    · simp only [Function.comp_apply, emb0, combineEmb_natAdd]
      exact congrFun (mkState54_comp_unifAnc as hl n K _ _ _ _ _) j
  have hact := as.act_unifPermCircuit (2 * K) (lay_d K) (by omega) (d_pos K hK) (two_mul_K_le_arity K)
  rw [← hz0] at hact
  have hsum_eq :
      ((1 / Real.sqrt (Nat.factorial (2 * K) : ℝ) : ℝ) : ℂ) •
        ∑ σ : Equiv.Perm (Fin (2 * K)),
          ket (padZero (lay_M K * lay_d K) (as.unifPermAnc (2 * K) (lay_d K))
            (flatReg (lay_M K) (lay_d K) (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ))) =
        ∑ σ : Equiv.Perm (Fin (2 * K)),
          (((1 / Real.sqrt (Nat.factorial (2 * K) : ℝ) : ℝ) : ℂ)) •
            ket (padZero (lay_M K * lay_d K) (as.unifPermAnc (2 * K) (lay_d K))
              (flatReg (lay_M K) (lay_d K) (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ))) :=
    Finset.smul_sum
  rw [hsum_eq] at hact
  have hlifted := LcgSym54.act_mapWires_ket_sum
    (as.unifPermCircuit (2 * K) (lay_d K) (by omega) (d_pos K hK) (two_mul_K_le_arity K))
    (emb0 as hl n K) z0 Finset.univ
    (fun _ => ((1 / Real.sqrt (Nat.factorial (2 * K) : ℝ) : ℝ) : ℂ)) _ hact
  rw [← Finset.smul_sum] at hlifted
  change act (circ0 as hl n K hK).unitary (ket z0) = _ at hlifted
  rw [hlifted]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [emb0, updateOn_combineEmb_padZero _ _ _ z0 (mkState54_comp_unifAnc as hl n K _ _ _ _ _) _,
    updateOn_reg3_mkState54]

lemma act_circ1a (comb : LcgSym54Comb) (r1 : Fin (lay_M K) → Qubits (lay_s n))
    (σ : Equiv.Perm (Fin (2 * K))) :
    let tr1_σ := sortTrace (fun r => bitsToNat (recKey54 (w_p := 0) r)) (lay_d K) true
      (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
    act (circ1a br as hl n K).unitary
        (ket (mkState54 as hl n K r1 (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
          (fun _ => false) (fun _ _ => false) (fun _ => false))) =
      ket (mkState54 as hl n K r1 (fun i => natToBits (lay_d K) i.1) tr1_σ
        (fun _ _ => false) (fun _ => false)) := by
  intro tr1_σ
  let z := mkState54 as hl n K r1 (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
    (fun _ => false) (fun _ _ => false) (fun _ => false)
  have hsingle := act_mapWires_ket_singleton
    (br.bitonicSortKeyCircuit (lay_d K) (lay_d K) 0 true) (emb1a as hl n K) z
    (packDTA54 (lay_M K) (lay_d K) (lay_tr K) (lay_d K) (fun i => natToBits (lay_d K) i.1) tr1_σ)
    (by
      rw [emb1a, comp_packDTA54Emb _ _ _ _ _ _ z _ (fun _ => false)
        (mkState54_comp_reg3 as hl n K _ _ _ _ _)
        (mkState54_comp_tr1 as hl n K _ _ _ _ _)
        (mkState54_comp_bk1 as hl n K _ _ _ _ _)]
      have hsort := br.act_bitonicSortKeyCircuit_ket (lay_d K) (lay_d K) 0 true
        (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
      dsimp only [Nat.add_zero] at hsort
      rw [hsort]
      exact congrArg (fun arr => ket (packDTA54 (lay_M K) (lay_d K) (lay_tr K) (lay_d K) arr tr1_σ))
        (sort_permRegBits_eq br comb K (lay_d K) (two_mul_K_le_arity K) σ))
  change act (circ1a br as hl n K).unitary (ket z) = _ at hsingle
  rw [hsingle]
  congr 1
  rw [emb1a, updateOn_packDTA54Emb _ _ _ _ _ _ z (mkState54_comp_bk1 as hl n K _ _ _ _ _),
    updateOn_reg3_mkState54, updateOn_tr1_mkState54]

lemma updateOn_combineEmb {a b m : ℕ} (eA : Fin a ↪ Fin m) (eB : Fin b ↪ Fin m)
    (hAB : ∀ i j, eA i ≠ eB j) (z : Qubits m) (xA : Qubits a) (xB : Qubits b) :
    updateOn (combineEmb eA eB hAB) z (Fin.append xA xB) = updateOn eB (updateOn eA z xA) xB := by
  funext u
  by_cases hu : u ∈ Set.range (combineEmb eA eB hAB)
  · rcases hu with ⟨ij, rfl⟩
    induction ij using Fin.addCases with
    | left i =>
      have hnotB : eA i ∉ Set.range eB := fun ⟨j, hj⟩ => hAB i j hj.symm
      rw [updateOn_apply_emb, combineEmb_castAdd, updateOn_apply_not_mem _ _ _ hnotB,
        updateOn_apply_emb, Fin.append_left]
    | right j =>
      rw [updateOn_apply_emb, combineEmb_natAdd, updateOn_apply_emb, Fin.append_right]
  · have hnotA : u ∉ Set.range eA := fun ⟨i, hi⟩ => hu ⟨Fin.castAdd b i, by simpa using hi⟩
    have hnotB : u ∉ Set.range eB := fun ⟨j, hj⟩ => hu ⟨Fin.natAdd a j, by simpa using hj⟩
    rw [updateOn_apply_not_mem _ _ _ hu, updateOn_apply_not_mem _ _ _ hnotB,
      updateOn_apply_not_mem _ _ _ hnotA]

lemma comp_combineEmb {a b m : ℕ} (eA : Fin a ↪ Fin m) (eB : Fin b ↪ Fin m)
    (hAB : ∀ i j, eA i ≠ eB j) (z : Qubits m) :
    z ∘ combineEmb eA eB hAB = Fin.append (z ∘ eA) (z ∘ eB) := by
  funext u
  induction u using Fin.addCases with
  | left i => simp
  | right j => simp

lemma act_circ1b (comb : LcgSym54Comb) (l : Fin (2 * K) → Fin (n + 1)) (σ : Equiv.Perm (Fin (2 * K))) :
    let tr1_σ := sortTrace (fun r => bitsToNat (recKey54 (w_p := 0) r)) (lay_d K) true
      (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
    act (circ1b br as hl n K).unitary
        (ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) l)
          (fun i => natToBits (lay_d K) i.1) tr1_σ (fun _ _ => false) (fun _ => false))) =
      ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) (permList σ l))
        (fun i => natToBits (lay_d K) i.1) tr1_σ (fun _ _ => false) (fun _ => false)) := by
  intro tr1_σ
  let z := mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) l)
    (fun i => natToBits (lay_d K) i.1) tr1_σ (fun _ _ => false) (fun _ => false)
  have hsingle := act_mapWires_ket_singleton
    (br.unrouteSortCircuit (lay_d K) (lay_s n)) (emb1b as hl n K) z
    (Fin.append (flatReg (lay_M K) (lay_s n) (padSym n (lay_s n) K (lay_d K) (permList σ l))) tr1_σ)
    (by
      rw [emb1b, comp_combineEmb, mkState54_comp_reg1, mkState54_comp_tr1]
      rw [br.act_unrouteSortCircuit_ket (lay_d K) (lay_s n) (padSym n (lay_s n) K (lay_d K) l) tr1_σ]
      have hunroute : unrouteSort (lay_d K) tr1_σ (padSym n (lay_s n) K (lay_d K) l) =
          padSym n (lay_s n) K (lay_d K) (permList σ l) := by
        rw [unrouteSort_eq_comp_inv_routePerm br]
        have hcomp : (fun i => padSym n (lay_s n) K (lay_d K) l ((routePerm br (lay_d K) tr1_σ)⁻¹ i)) =
            padSym n (lay_s n) K (lay_d K) l ∘ unrouteSort (lay_d K) tr1_σ id := rfl
        rw [hcomp, show unrouteSort (lay_d K) tr1_σ id =
            padPerm54 (2 * K) (arity (lay_d K)) (two_mul_K_le_arity K) σ from
          unrouteSort_tr1_id br comb K (lay_d K) (two_mul_K_le_arity K) σ]
        exact padSym_comp_padPerm54 n (lay_s n) K (lay_d K) (two_mul_K_le_arity K) l σ
      rw [hunroute])
  change act (circ1b br as hl n K).unitary (ket z) = _ at hsingle
  rw [hsingle]
  congr 1
  rw [emb1b, updateOn_combineEmb, updateOn_reg1_mkState54, updateOn_tr1_mkState54]

lemma act_circ1 (comb : LcgSym54Comb) (l : Fin (2 * K) → Fin (n + 1)) (σ : Equiv.Perm (Fin (2 * K))) :
    act (circ1 br as hl n K).unitary
        (ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) l)
          (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
          (fun _ => false) (fun _ _ => false) (fun _ => false))) =
      ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) (permList σ l))
        (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
        (fun _ => false) (fun _ _ => false) (fun _ => false)) := by
  unfold circ1
  simp only [LayeredCircuit.seq_unitary, act_mul]
  rw [act_circ1a br as hl n K comb (padSym n (lay_s n) K (lay_d K) l) σ]
  rw [act_circ1b br as hl n K comb l σ]
  exact act_adj_ket (circ1a br as hl n K)
    (act_circ1a br as hl n K comb (padSym n (lay_s n) K (lay_d K) (permList σ l)) σ)

/-! Stage 2a helpers and `act_circ2a` -/

def prefixKey2 (y : Fin (2 * K) → Fin (n + 1)) (k : ℕ) : Fin (lay_M K) → Qubits (lay_w₂ n K) :=
  fun q => if q.1 < k then key2Arr n (lay_s n) K (lay_d K) y q else fun _ => false

lemma w2_in_disj_pad_sym : ∀ (i : Fin 1) (j : Fin (lay_s n)), w2PadIn n K i ≠ w2SymIn n K j := by
  intro i j h
  have hv := congrArg Fin.val h
  change (Fin.castAdd (lay_d K) (Fin.castAdd (lay_s n) i)).1 =
      (Fin.castAdd (lay_d K) (Fin.natAdd 1 j)).1 at hv
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma w2_in_disj_pad_idx : ∀ (i : Fin 1) (j : Fin (lay_d K)), w2PadIn n K i ≠ w2IdxIn n K j := by
  intro i j h
  have hv := congrArg Fin.val h
  change (Fin.castAdd (lay_d K) (Fin.castAdd (lay_s n) i)).1 = (Fin.natAdd (1 + lay_s n) j).1 at hv
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma w2_in_disj_sym_idx : ∀ (i : Fin (lay_s n)) (j : Fin (lay_d K)), w2SymIn n K i ≠ w2IdxIn n K j := by
  intro i j h
  have hv := congrArg Fin.val h
  change (Fin.castAdd (lay_d K) (Fin.natAdd 1 i)).1 = (Fin.natAdd (1 + lay_s n) j).1 at hv
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma updateOn_slotEmb_eq {m off N w : ℕ} (h : off + N * w ≤ m)
    (z : Qubits m) (arr : Fin N → Qubits w) (hz : z ∘ regEmb off N w h = flatReg N w arr)
    (j : Fin N) (val : Qubits w) :
    updateOn (slotEmb off N w h j) z val =
      updateOn (regEmb off N w h) z (flatReg N w (Function.update arr j val)) := by
  funext u
  by_cases hu : u ∈ Set.range (regEmb off N w h)
  · rcases hu with ⟨idx, rfl⟩
    have hcomp := updateOn_slotEmb_comp_regEmb h z arr hz j val
    have h1 := congrFun hcomp idx
    rw [Function.comp_apply] at h1
    rw [h1, updateOn_apply_emb]
  · have hnotSlot : u ∉ Set.range (slotEmb off N w h j) := fun ⟨b, hb⟩ =>
      hu ⟨slotInReg N w j b, hb⟩
    rw [updateOn_apply_not_mem _ _ _ hnotSlot, updateOn_apply_not_mem _ _ _ hu]

lemma updateOn_key2Slot_lt (z : Qubits (lay_m as hl n K)) (p : Fin (lay_M K))
    (hz : z ∘ key2Slot as hl n K p = fun _ => false) (val : Qubits (lay_s n)) :
    updateOn (key2SymSlot as hl n K p) z val =
      updateOn (key2Slot as hl n K p) z
        (Fin.append (Fin.append (fun _ : Fin 1 => false) val) (fun _ : Fin (lay_d K) => false)) := by
  funext u
  by_cases hu : u ∈ Set.range (key2Slot as hl n K p)
  · rcases hu with ⟨b, rfl⟩
    rw [updateOn_apply_emb]
    refine Fin.addCases (fun b1 => ?_) (fun b2 => ?_) b
    · refine Fin.addCases (fun i => ?_) (fun j => ?_) b1
      · have hnot : key2Slot as hl n K p (Fin.castAdd (lay_d K) (Fin.castAdd (lay_s n) i)) ∉
            Set.range (key2SymSlot as hl n K p) := by
          rintro ⟨j, hj⟩
          have heq := (key2Slot as hl n K p).injective hj
          exact (w2_in_disj_pad_sym n K i j) heq.symm
        rw [updateOn_apply_not_mem _ _ _ hnot, Fin.append_left, Fin.append_left]
        exact congrFun hz _
      · change updateOn (key2SymSlot as hl n K p) z val (key2SymSlot as hl n K p j) = _
        rw [updateOn_apply_emb, Fin.append_left, Fin.append_right]
    · have hnot : key2Slot as hl n K p (Fin.natAdd (1 + lay_s n) b2) ∉
          Set.range (key2SymSlot as hl n K p) := by
        rintro ⟨j, hj⟩
        have heq := (key2Slot as hl n K p).injective hj
        exact (w2_in_disj_sym_idx n K j b2) heq
      rw [updateOn_apply_not_mem _ _ _ hnot, Fin.append_right]
      exact congrFun hz _
  · have hnotSym : u ∉ Set.range (key2SymSlot as hl n K p) := fun ⟨j, hj⟩ =>
      hu ⟨w2SymIn n K j, hj⟩
    rw [updateOn_apply_not_mem _ _ _ hnotSym, updateOn_apply_not_mem _ _ _ hu]

lemma updateOn_key2Slot_ge (z : Qubits (lay_m as hl n K)) (p : Fin (lay_M K))
    (hz : z ∘ key2Slot as hl n K p = fun _ => false) (idxVal : Qubits (lay_d K)) :
    updateOn (key2IdxSlot as hl n K p) (updateOn (key2PadBit as hl n K p) z (fun _ => true)) idxVal =
      updateOn (key2Slot as hl n K p) z
        (Fin.append (Fin.append (fun _ : Fin 1 => true) (fun _ : Fin (lay_s n) => false)) idxVal) := by
  funext u
  by_cases hu : u ∈ Set.range (key2Slot as hl n K p)
  · rcases hu with ⟨b, rfl⟩
    rw [updateOn_apply_emb]
    refine Fin.addCases (fun b1 => ?_) (fun b2 => ?_) b
    · refine Fin.addCases (fun i => ?_) (fun j => ?_) b1
      · have hnotIdx : key2PadBit as hl n K p i ∉
            Set.range (key2IdxSlot as hl n K p) := by
          rintro ⟨k, hk⟩
          exact (w2_in_disj_pad_idx n K i k) ((key2Slot as hl n K p).injective hk).symm
        change updateOn (key2IdxSlot as hl n K p)
          (updateOn (key2PadBit as hl n K p) z (fun _ => true)) idxVal (key2PadBit as hl n K p i) = _
        rw [updateOn_apply_not_mem _ _ _ hnotIdx, updateOn_apply_emb, Fin.append_left, Fin.append_left]
      · have hnotIdx : key2SymSlot as hl n K p j ∉
            Set.range (key2IdxSlot as hl n K p) := by
          rintro ⟨k, hk⟩
          exact (w2_in_disj_sym_idx n K j k) ((key2Slot as hl n K p).injective hk).symm
        have hnotPad : key2SymSlot as hl n K p j ∉
            Set.range (key2PadBit as hl n K p) := by
          rintro ⟨i, hi⟩
          exact (w2_in_disj_pad_sym n K i j) ((key2Slot as hl n K p).injective hi)
        change updateOn (key2IdxSlot as hl n K p)
          (updateOn (key2PadBit as hl n K p) z (fun _ => true)) idxVal (key2SymSlot as hl n K p j) = _
        rw [updateOn_apply_not_mem _ _ _ hnotIdx, updateOn_apply_not_mem _ _ _ hnotPad,
          Fin.append_left, Fin.append_right]
        exact congrFun hz _
    · change updateOn (key2IdxSlot as hl n K p)
        (updateOn (key2PadBit as hl n K p) z (fun _ => true)) idxVal (key2IdxSlot as hl n K p b2) = _
      rw [updateOn_apply_emb, Fin.append_right]
  · have hnotIdx : u ∉ Set.range (key2IdxSlot as hl n K p) := fun ⟨k, hk⟩ => hu ⟨w2IdxIn n K k, hk⟩
    have hnotPad : u ∉ Set.range (key2PadBit as hl n K p) := fun ⟨i, hi⟩ => hu ⟨w2PadIn n K i, hi⟩
    rw [updateOn_apply_not_mem _ _ _ hnotIdx, updateOn_apply_not_mem _ _ _ hnotPad,
      updateOn_apply_not_mem _ _ _ hu]

lemma act_circ2a (y : Fin (2 * K) → Fin (n + 1)) (r3Val : Fin (lay_M K) → Qubits (lay_d K)) :
    act (circ2a arith as hl n K).unitary
        (ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) r3Val
          (fun _ => false) (fun _ _ => false) (fun _ => false))) =
      ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) r3Val
        (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) y) (fun _ => false)) := by
  let enc : ℕ → Qubits (lay_m as hl n K) := fun k =>
    mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) r3Val
      (fun _ => false) (prefixKey2 n K y k) (fun _ => false)
  have hp0 : prefixKey2 n K y 0 = fun _ _ => false := by
    funext q _
    simp [prefixKey2]
  have hpM : prefixKey2 n K y (lay_M K) = key2Arr n (lay_s n) K (lay_d K) y := by
    funext q
    have hq : q.1 < lay_M K := q.isLt
    dsimp only [prefixKey2]
    rw [if_pos hq]
  have h0 : enc 0 = mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) r3Val
      (fun _ => false) (fun _ _ => false) (fun _ => false) := by
    dsimp only [enc]
    rw [hp0]
  have hM : enc (lay_M K) = mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) r3Val
      (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) y) (fun _ => false) := by
    dsimp only [enc]
    rw [hpM]
  rw [← h0, ← hM]
  refine act_seqList_finRange_step enc (circ2aSlot arith as hl n K) fun p => ?_
  dsimp only [circ2aSlot]
  let z := enc p.1
  have hz_reg1 : z ∘ reg1Slot as hl n K p = padSym n (lay_s n) K (lay_d K) y p := by
    change (z ∘ embReg1 as hl n K) ∘ slotInReg (lay_M K) (lay_s n) p = _
    rw [mkState54_comp_reg1, flatReg_comp_slotInReg]
  have hz_key2Slot : z ∘ key2Slot as hl n K p = fun _ => false := by
    change (z ∘ embKey2 as hl n K) ∘ slotInReg (lay_M K) (lay_w₂ n K) p = _
    rw [mkState54_comp_key2, flatReg_comp_slotInReg]
    simp [prefixKey2]
  have hupd_prefix : Function.update (prefixKey2 n K y p.1) p (key2Arr n (lay_s n) K (lay_d K) y p) =
      prefixKey2 n K y (p.1 + 1) := by
    funext q
    by_cases hq : q = p
    · subst hq; simp [prefixKey2]
    · have hne : q.1 ≠ p.1 := fun h => hq (Fin.ext h)
      rw [Function.update_of_ne hq]
      dsimp only [prefixKey2]
      by_cases hlt : q.1 < p.1
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]
  have hupd_mk : updateOn (key2Slot as hl n K p) z (key2Arr n (lay_s n) K (lay_d K) y p) = enc (p.1 + 1) := by
    rw [key2Slot, updateOn_slotEmb_eq _ z (prefixKey2 n K y p.1) (mkState54_comp_key2 as hl n K _ _ _ _ _) p,
      hupd_prefix]
    exact updateOn_key2_mkState54 as hl n K _ _ _ _ _ _
  split_ifs with hp
  · rw [act_copyRegOn arith]
    have hxor : (fun j : Fin (lay_s n) => xor (z (key2SymSlot as hl n K p j)) (z (reg1Slot as hl n K p j))) =
        particleSym54 n (lay_s n) (y ⟨p.1, hp⟩) := by
      funext j
      have h1 : z (key2SymSlot as hl n K p j) = false := congrFun hz_key2Slot (w2SymIn n K j)
      have h2 : z (reg1Slot as hl n K p j) = padSym n (lay_s n) K (lay_d K) y p j := congrFun hz_reg1 j
      rw [h1, h2, Bool.false_xor]
      simp [padSym, dif_pos hp]
    rw [hxor, updateOn_key2Slot_lt as hl n K z p hz_key2Slot]
    have hk2p : key2Arr n (lay_s n) K (lay_d K) y p =
        Fin.append (Fin.append (fun _ : Fin 1 => false) (particleSym54 n (lay_s n) (y ⟨p.1, hp⟩)))
          (fun _ : Fin (lay_d K) => false) := by
      simp [key2Arr, dif_pos hp]
    rw [← hk2p, hupd_mk]
  · simp only [LayeredCircuit.seq_unitary, act_mul]
    rw [act_setConstOn arith 1 (key2PadBit as hl n K p) z]
    have hpad_val : (fun i : Fin 1 => xor (z (key2PadBit as hl n K p i)) (natToBits 1 1 i)) =
        fun _ => true := by
      funext i
      have h1 : z (key2PadBit as hl n K p i) = false := congrFun hz_key2Slot (w2PadIn n K i)
      rw [h1, Bool.false_xor, natToBits_one_one]
    rw [hpad_val, act_setConstOn arith p.1 (key2IdxSlot as hl n K p)]
    let z' := updateOn (key2PadBit as hl n K p) z (fun _ => true)
    have hidx_zero : z' ∘ key2IdxSlot as hl n K p = fun _ => false := by
      funext k
      have hnot : key2IdxSlot as hl n K p k ∉ Set.range (key2PadBit as hl n K p) := by
        rintro ⟨i, hi⟩
        exact (w2_in_disj_pad_idx n K i k) ((key2Slot as hl n K p).injective hi)
      change z' (key2IdxSlot as hl n K p k) = false
      dsimp only [z']
      rw [updateOn_apply_not_mem _ _ _ hnot]
      exact congrFun hz_key2Slot (w2IdxIn n K k)
    have hidx_val : (fun k : Fin (lay_d K) => xor (z' (key2IdxSlot as hl n K p k)) (natToBits (lay_d K) p.1 k)) =
        natToBits (lay_d K) p.1 := by
      funext k
      have hk0 : z' (key2IdxSlot as hl n K p k) = false := congrFun hidx_zero k
      rw [hk0, Bool.false_xor]
    rw [hidx_val, updateOn_key2Slot_ge as hl n K z p hz_key2Slot]
    have hk2p : key2Arr n (lay_s n) K (lay_d K) y p =
        Fin.append (Fin.append (fun _ : Fin 1 => true) (fun _ : Fin (lay_s n) => false))
          (natToBits (lay_d K) p.1) := by
      simp [key2Arr, dif_neg hp]
    rw [← hk2p, hupd_mk]

lemma act_circ2b (comb : LcgSym54Comb) (l y : Fin (2 * K) → Fin (n + 1)) (hlm : Monotone l)
    (hy : ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = y)
    (r3Val : Fin (lay_M K) → Qubits (lay_d K)) :
    act (circ2b br as hl n K).unitary
        (ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) r3Val
          (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) y) (fun _ => false))) =
      ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) r3Val
        (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y)) := by
  rcases hy with ⟨σ, rfl⟩
  let z := mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) (permList σ l)) r3Val
    (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) (permList σ l)) (fun _ => false)
  have hsingle := act_mapWires_ket_singleton
    (br.bitonicSortKeyCircuit (lay_d K) (lay_w₂ n K) 0 true) (emb2b as hl n K) z
    (packDTA54 (lay_M K) (lay_w₂ n K) (lay_tr K) (lay_w₂ n K)
      (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) (permList σ l)))
    (by
      rw [emb2b, comp_packDTA54Emb _ _ _ _ _ _ z _ (fun _ => false)
        (mkState54_comp_key2 as hl n K _ _ _ _ _)
        (mkState54_comp_tr2 as hl n K _ _ _ _ _)
        (mkState54_comp_bk2 as hl n K _ _ _ _ _)]
      have hsort := br.act_bitonicSortKeyCircuit_ket (lay_d K) (lay_w₂ n K) 0 true
        (key2Arr n (lay_s n) K (lay_d K) (permList σ l))
      dsimp only [Nat.add_zero] at hsort
      rw [hsort]
      exact congrArg (fun arr => ket (packDTA54 (lay_M K) (lay_w₂ n K) (lay_tr K) (lay_w₂ n K) arr
          (tr2Of n K (lay_d K) (permList σ l))))
        (sort_key2Arr_eq br comb n K (lay_d K) (two_mul_K_le_arity K) l hlm σ))
  change act (circ2b br as hl n K).unitary (ket z) = _ at hsingle
  rw [hsingle]
  congr 1
  rw [emb2b, updateOn_packDTA54Emb _ _ _ _ _ _ z (mkState54_comp_bk2 as hl n K _ _ _ _ _),
    updateOn_key2_mkState54, updateOn_tr2_mkState54]

lemma act_circ2c (comb : LcgSym54Comb) (l : Fin (2 * K) → Fin (n + 1)) (hlm : Monotone l)
    (σ : Equiv.Perm (Fin (2 * K))) :
    let y := permList σ l
    let τ := tauOf br comb n K (lay_d K) (two_mul_K_le_arity K) l hlm y
    act (circ2c br as hl n K).unitary
        (ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y)
          (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
          (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y))) =
      ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y)
        (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) (σ * τ⁻¹))
        (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y)) := by
  intro y τ
  let z := mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y)
    (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
    (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y)
  have hspec := (tauOf_spec br comb n K (lay_d K) (two_mul_K_le_arity K) l hlm y ⟨σ, rfl⟩).2
  have hroute_perm : routeSort (lay_d K) (tr2Of n K (lay_d K) y)
      (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ) =
      permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) (σ * τ⁻¹) := by
    funext i
    rw [br.routeSort_apply]
    have hid := congrFun hspec i
    have hid' : routeSort (lay_d K) (tr2Of n K (lay_d K) y) id i =
        padPerm54 (2 * K) (lay_M K) (two_mul_K_le_arity K) τ⁻¹ i := hid
    change permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ
      (routeSort (lay_d K) (tr2Of n K (lay_d K) y) id i) = _
    rw [hid']
    simp only [permRegBits, padPerm54_mul, Equiv.Perm.mul_apply]
  have hsingle := act_mapWires_ket_singleton
    (br.routeSortCircuit (lay_d K) (lay_d K)) (emb2c as hl n K) z
    (Fin.append (flatReg (lay_M K) (lay_d K) (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) (σ * τ⁻¹)))
      (tr2Of n K (lay_d K) y))
    (by
      rw [emb2c, comp_combineEmb, mkState54_comp_reg3, mkState54_comp_tr2]
      rw [br.act_routeSortCircuit_ket (lay_d K) (lay_d K) _ (tr2Of n K (lay_d K) y), hroute_perm])
  change act (circ2c br as hl n K).unitary (ket z) = _ at hsingle
  rw [hsingle]
  congr 1
  rw [emb2c, updateOn_combineEmb, updateOn_reg3_mkState54, updateOn_tr2_mkState54]

lemma finProdFinEquiv_symm_key2LiveInKey2 (u : Fin (2 * K * lay_s n)) :
    finProdFinEquiv.symm (key2LiveInKey2 n K u) =
      (⟨(finProdFinEquiv.symm u).1.1, lt_of_lt_of_le (finProdFinEquiv.symm u).1.isLt (two_mul_K_le_arity K)⟩,
       w2SymIn n K (finProdFinEquiv.symm u).2) := by
  dsimp only [key2LiveInKey2, slotInReg]
  exact finProdFinEquiv.symm_apply_apply _

lemma mkState54_comp_embKey2Live (r1 r3 t1 t2) (l : Fin (2 * K) → Fin (n + 1)) :
    mkState54 as hl n K r1 r3 t1 (key2Arr n (lay_s n) K (lay_d K) l) t2 ∘ embKey2Live as hl n K =
      flatReg (2 * K) (lay_s n) fun p => particleSym54 n (lay_s n) (l p) := by
  funext u
  change ((mkState54 as hl n K r1 r3 t1 (key2Arr n (lay_s n) K (lay_d K) l) t2 ∘ embKey2 as hl n K)
    (key2LiveInKey2 n K u)) = _
  rw [mkState54_comp_key2]
  dsimp only [flatReg]
  rw [finProdFinEquiv_symm_key2LiveInKey2]
  have hw2 : w2SymIn n K (finProdFinEquiv.symm u).2 =
      Fin.castAdd (lay_d K) (Fin.natAdd 1 (finProdFinEquiv.symm u).2) := rfl
  rw [hw2]
  simp only [key2Arr, dif_pos (finProdFinEquiv.symm u).1.isLt]
  rw [Fin.append_left, Fin.append_right]

lemma updateOn_emb2d_mkState54 (l y : Fin (2 * K) → Fin (n + 1))
    (r3Val : Fin (lay_M K) → Qubits (lay_d K)) :
    let z0 := mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) (fun _ _ => false)
      (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y)
    updateOn (emb2d as hl n K) z0
      (padZero (2 * K * lay_s n + lay_M K * lay_d K) (hl.harmBucketAnc n K (lay_d K))
        (Fin.append (flatReg (2 * K) (lay_s n) fun p => particleSym54 n (lay_s n) (l p))
          (flatReg (lay_M K) (lay_d K) r3Val))) =
      mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) r3Val
        (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y) := by
  intro z0
  have hpad : updateOn (emb2d as hl n K) z0
      (padZero (2 * K * lay_s n + lay_M K * lay_d K) (hl.harmBucketAnc n K (lay_d K))
        (Fin.append (flatReg (2 * K) (lay_s n) fun p => particleSym54 n (lay_s n) (l p))
          (flatReg (lay_M K) (lay_d K) r3Val))) =
      updateOn (combineEmb (embKey2Live as hl n K) (embReg3 as hl n K) (embKey2Live_disj_embReg3 as hl n K)) z0
        (Fin.append (flatReg (2 * K) (lay_s n) fun p => particleSym54 n (lay_s n) (l p))
          (flatReg (lay_M K) (lay_d K) r3Val)) := by
    rw [emb2d, updateOn_combineEmb_padZero _ _ _ z0 (mkState54_comp_hlAnc as hl n K _ _ _ _ _)]
  rw [hpad, updateOn_combineEmb]
  have hsame : updateOn (embKey2Live as hl n K) z0
      (flatReg (2 * K) (lay_s n) fun p => particleSym54 n (lay_s n) (l p)) = z0 :=
    updateOn_eq_self_of_eq _ z0 _ (mkState54_comp_embKey2Live as hl n K _ _ _ _ l).symm
  rw [hsame]
  exact updateOn_reg3_mkState54 as hl n K _ _ _ _ _ r3Val

lemma act_circ2d_stabSum (hn : 1 ≤ n) (hK : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1)) (hlm : Monotone l)
    (y : Fin (2 * K) → Fin (n + 1)) :
    act (circ2d as hl n K hn hK).unitary
        (∑ h : stabGroup (2 * K) l,
          ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y)
            (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) h.1)
            (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y))) =
      (Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℂ) •
        ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) (fun _ _ => false)
          (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y)) := by
  let z0 := mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y) (fun _ _ => false)
    (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y)
  let ψ0_hl : Qubits ((2 * K * lay_s n + lay_M K * lay_d K) + hl.harmBucketAnc n K (lay_d K)) :=
    padZero (2 * K * lay_s n + lay_M K * lay_d K) (hl.harmBucketAnc n K (lay_d K))
      (Fin.append (flatReg (2 * K) (lay_s n) fun p => particleSym54 n (lay_s n) (l p)) (fun _ => false))
  let lc_hl := hl.harmBucketH_lCircuit n K (lay_d K) hn hK (d_pos K hK) (two_mul_K_le_arity K)
  have hact_hl := hl.act_harmBucketH_lCircuit n K (lay_d K) hn hK (d_pos K hK) (two_mul_K_le_arity K) l hlm
  have hcard_pos_nat : 0 < Fintype.card (stabGroup (2 * K) l) :=
    Fintype.card_pos_iff.mpr ⟨(1 : stabGroup (2 * K) l)⟩
  have hcard_pos : (0 : ℝ) < (Fintype.card (stabGroup (2 * K) l) : ℝ) := by
    exact_mod_cast hcard_pos_nat
  have hsqrt_ne : (Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hcard_pos).ne'
  have hsum_hl :
      ∑ h : stabGroup (2 * K) l,
        ket (padZero (2 * K * lay_s n + lay_M K * lay_d K) (hl.harmBucketAnc n K (lay_d K))
          (Fin.append (flatReg (2 * K) (lay_s n) fun p => particleSym54 n (lay_s n) (l p))
            (flatReg (lay_M K) (lay_d K) (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) h.1)))) =
      (Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℂ) •
        act lc_hl.unitary (ket ψ0_hl) := by
    change _ = (Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℂ) • act _ (ket _)
    rw [hact_hl, smul_smul]
    have hmul : (Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℂ) *
        ((1 / Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_one_div_cancel hsqrt_ne, Complex.ofReal_one]
    rw [hmul, one_smul]
  have hLHS :
      ∑ h : stabGroup (2 * K) l,
        ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y)
          (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) h.1)
          (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y)) =
      liftState (emb2d as hl n K) z0
        ((Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℂ) • act lc_hl.unitary (ket ψ0_hl)) := by
    rw [← hsum_hl, liftState_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [liftState_ket]
    congr 1
    exact (updateOn_emb2d_mkState54 as hl n K l y (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) h.1)).symm
  rw [hLHS, liftState_smul, act_smul]
  congr 1
  have hadj := act_adj_ket (lc_hl.mapWires (emb2d as hl n K))
    (act_mapWires_liftState lc_hl (emb2d as hl n K) z0 (ket ψ0_hl))
  change act (circ2d as hl n K hn hK).unitary
      (liftState (emb2d as hl n K) z0 (act lc_hl.unitary (ket ψ0_hl))) =
    liftState (emb2d as hl n K) z0 (ket ψ0_hl) at hadj
  rw [hadj, liftState_ket]
  congr 1
  have hzero_upd := updateOn_emb2d_mkState54 as hl n K l y (fun _ _ => false)
  simpa only [flatReg_zero] using hzero_upd

lemma act_fullCirc (comb : LcgSym54Comb) (hn : 1 ≤ n) (hK : 1 ≤ K)
    (l : Fin (2 * K) → Fin (n + 1)) (hlm : Monotone l) :
    act (fullCirc br arith as hl n K hn hK).unitary
        (padKet (lay_e as hl n K)
          (ket (flatReg (2 * K) (lay_s n) fun p => particleSym54 n (lay_s n) (l p)))) =
      padKet (lay_e as hl n K)
        (((Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) /
            Real.sqrt (Nat.factorial (2 * K) : ℝ) : ℝ) : ℂ) •
          ∑ y : { z : Fin (2 * K) → Fin (n + 1) // ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = z },
            ket (flatReg (2 * K) (lay_s n) fun p => particleSym54 n (lay_s n) (y.1 p))) := by
  rw [padKet_ket_eq, ← mkState54_eq_padZero as hl n K l]
  change act (fullCirc br arith as hl n K hn hK).unitary
      (ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) l) (fun _ _ => false)
        (fun _ => false) (fun _ _ => false) (fun _ => false))) = _
  unfold fullCirc
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, LayeredCircuit.id_unitary,
    one_mul, act_mul]
  rw [act_circ0 as hl n K hK l]
  have hstep123 : ∀ σ : Equiv.Perm (Fin (2 * K)),
      act (circ2c br as hl n K).unitary
        (act (circ2b br as hl n K).unitary
          (act (circ2a arith as hl n K).unitary
            (act (circ1 br as hl n K).unitary
              (ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) l)
                (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
                (fun _ => false) (fun _ _ => false) (fun _ => false)))))) =
      ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) (permList σ l))
        (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K)
          (σ * (tauOf br comb n K (lay_d K) (two_mul_K_le_arity K) l hlm (permList σ l))⁻¹))
        (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l)
        (tr2Of n K (lay_d K) (permList σ l))) := by
    intro σ
    rw [act_circ1 br as hl n K comb l σ,
      act_circ2a arith as hl n K (permList σ l) _,
      act_circ2b br as hl n K comb l (permList σ l) hlm ⟨σ, rfl⟩ _,
      act_circ2c br as hl n K comb l hlm σ]
  have h123 :
      act (circ2c br as hl n K).unitary
        (act (circ2b br as hl n K).unitary
          (act (circ2a arith as hl n K).unitary
            (act (circ1 br as hl n K).unitary
              (((1 / Real.sqrt (Nat.factorial (2 * K) : ℝ) : ℝ) : ℂ) •
                ∑ σ : Equiv.Perm (Fin (2 * K)),
                  ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) l)
                    (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) σ)
                    (fun _ => false) (fun _ _ => false) (fun _ => false)))))) =
      ((1 / Real.sqrt (Nat.factorial (2 * K) : ℝ) : ℝ) : ℂ) •
        ∑ σ : Equiv.Perm (Fin (2 * K)),
          ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) (permList σ l))
            (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K)
              (σ * (tauOf br comb n K (lay_d K) (two_mul_K_le_arity K) l hlm (permList σ l))⁻¹))
            (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l)
            (tr2Of n K (lay_d K) (permList σ l))) := by
    simp_rw [act_smul, act_sum]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => hstep123 σ
  rw [h123]
  have htau : ∀ y : { z : Fin (2 * K) → Fin (n + 1) // ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = z },
      permList (tauOf br comb n K (lay_d K) (two_mul_K_le_arity K) l hlm y.1)⁻¹ y.1 = l :=
    fun y => (tauOf_spec br comb n K (lay_d K) (two_mul_K_le_arity K) l hlm y.1 y.2).1
  let f : (Fin (2 * K) → Fin (n + 1)) → Equiv.Perm (Fin (2 * K)) → EuclideanSpace ℂ (Qubits (lay_m as hl n K)) :=
    fun y π => ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y)
      (permRegBits (2 * K) (lay_d K) (two_mul_K_le_arity K) π)
      (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y))
  change act (circ2a arith as hl n K).adj.unitary
      (act (circ2b br as hl n K).adj.unitary
        (act (circ2d as hl n K hn hK).unitary
          (((1 / Real.sqrt (Nat.factorial (2 * K) : ℝ) : ℝ) : ℂ) •
            ∑ σ : Equiv.Perm (Fin (2 * K)),
              f (permList σ l) (σ * (tauOf br comb n K (lay_d K) (two_mul_K_le_arity K) l hlm (permList σ l))⁻¹)))) = _
  rw [comb.eq_655_701_sum_factorization (2 * K) l
    (tauOf br comb n K (lay_d K) (two_mul_K_le_arity K) l hlm) htau f]
  rw [act_smul, act_sum]
  have h2d_term : ∀ y : { z : Fin (2 * K) → Fin (n + 1) // ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = z },
      act (circ2d as hl n K hn hK).unitary (∑ h : stabGroup (2 * K) l, f y.1 h.1) =
        (Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) : ℂ) •
          ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y.1) (fun _ _ => false)
            (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y.1)) :=
    fun y => act_circ2d_stabSum as hl n K hn hK l hlm y.1
  simp_rw [h2d_term, ← Finset.smul_sum, act_smul, act_sum]
  have h2e_term : ∀ y : { z : Fin (2 * K) → Fin (n + 1) // ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = z },
      act (circ2b br as hl n K).adj.unitary
        (ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y.1) (fun _ _ => false)
          (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) l) (tr2Of n K (lay_d K) y.1))) =
        ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y.1) (fun _ _ => false)
          (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) y.1) (fun _ => false)) :=
    fun y => act_adj_ket (circ2b br as hl n K) (act_circ2b br as hl n K comb l y.1 hlm y.2 _)
  simp_rw [h2e_term]
  have h2f_term : ∀ y : { z : Fin (2 * K) → Fin (n + 1) // ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = z },
      act (circ2a arith as hl n K).adj.unitary
        (ket (mkState54 as hl n K (padSym n (lay_s n) K (lay_d K) y.1) (fun _ _ => false)
          (fun _ => false) (key2Arr n (lay_s n) K (lay_d K) y.1) (fun _ => false))) =
        padKet (lay_e as hl n K)
          (ket (flatReg (2 * K) (lay_s n) fun p => particleSym54 n (lay_s n) (y.1 p))) := by
    intro y
    rw [act_adj_ket (circ2a arith as hl n K) (act_circ2a arith as hl n K y.1 _),
      mkState54_eq_padZero, padKet_ket_eq]
  simp_rw [h2f_term, ← padKet_sum, ← padKet_smul, smul_smul]
  congr 2
  rw [← Complex.ofReal_mul]
  congr 1
  ring

end CircuitStages

/-! ### 5. Final Coordinate Identity & Size Bound -/

lemma orbit_sum_eq_multinomKet54 (comb : LcgSym54Comb) (n K : ℕ)
    (α : Fin n → ℕ) (hk : K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K)
    (l : Fin (2 * K) → Fin (n + 1))
    (hα : ∀ i : Fin n, (Finset.univ.filter fun p => l p = ⟨i.1, by omega⟩).card = α i)
    (hblank : (Finset.univ.filter fun p => l p = ⟨n, Nat.lt_succ_self n⟩).card = 2 * K - ∑ i, α i) :
    let s := Nat.clog 2 n + 1
    ((Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) /
        Real.sqrt (Nat.factorial (2 * K) : ℝ) : ℝ) : ℂ) •
      ∑ y : { z : Fin (2 * K) → Fin (n + 1) // ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = z },
        ket (flatReg (2 * K) s fun p => particleSym54 n s (y.1 p)) =
      multinomKet54 n s K α hk := by
  intro s
  let fEnc : (Fin (2 * K) → Fin (n + 1)) → Qubits (2 * K * s) :=
    fun y => flatReg (2 * K) s fun p => particleSym54 n s (y p)
  have hfEnc_inj : Function.Injective fEnc := by
    intro y₁ y₂ heq
    have hsplit := congrArg (splitReg (2 * K) s) heq
    simp only [fEnc, splitReg_flatReg] at hsplit
    funext p
    exact particleSym54_inj n (congrFun hsplit p)
  have hcard :
      ((Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) /
          Real.sqrt (Nat.factorial (2 * K) : ℝ) : ℝ) : ℂ) =
        ((Real.sqrt
          ((∏ i : Fin n, ((α i).factorial : ℝ)) *
            ((2 * K - ∑ i : Fin n, α i).factorial : ℝ) / ((2 * K).factorial : ℝ)) : ℝ) : ℂ) := by
    congr 1
    rw [comb.card_stabGroup_fin_succ n K α l hα hblank]
    push_cast
    rw [← Real.sqrt_div (by positivity)]
  ext z
  change (WithLp.ofLp
      (((Real.sqrt (Fintype.card (stabGroup (2 * K) l) : ℝ) /
          Real.sqrt (Nat.factorial (2 * K) : ℝ) : ℝ) : ℂ) •
        ∑ y : { z : Fin (2 * K) → Fin (n + 1) // ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = z },
          ket (fEnc y.1))) z = (WithLp.ofLp (multinomKet54 n s K α hk)) z
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply]
  dsimp only [multinomKet54, WithLp.ofLp_toLp]
  have hcond_iff :
      (∃ y : { w : Fin (2 * K) → Fin (n + 1) // ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = w },
        fEnc y.1 = z) ↔
      ((∀ i : Fin n,
          (Finset.univ.filter fun r : Fin (2 * K) =>
            splitReg (2 * K) s z r = natToBits s i.val).card = α i) ∧
        (Finset.univ.filter fun r : Fin (2 * K) =>
          splitReg (2 * K) s z r = blankSym54 s).card = 2 * K - ∑ i : Fin n, α i) := by
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact (comb.orbit_particleSym54_iff_multinom n K α l hα hblank y).mp hy
    · rintro ⟨hzα, hzblank⟩
      let S_all : Fin (n + 1) → Finset (Fin (2 * K)) :=
        fun j => Finset.univ.filter fun r : Fin (2 * K) =>
          splitReg (2 * K) s z r = particleSym54 n s j
      have hdisj : (↑(Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))).PairwiseDisjoint S_all := by
        intro j₁ _ j₂ _ hj
        rw [Function.onFun]
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        simp only [S_all, Finset.mem_filter, Finset.mem_univ, true_and] at hr1 hr2
        exact hj (particleSym54_inj n (hr1.symm.trans hr2))
      have hcard_sum : ∑ j : Fin (n + 1), (S_all j).card = 2 * K := by
        rw [Fin.sum_univ_castSucc]
        have hcast : ∑ i : Fin n, (S_all i.castSucc).card = ∑ i : Fin n, α i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hps : particleSym54 n s i.castSucc = natToBits s i.val :=
            particleSym54_lt i.isLt
          simpa only [S_all, hps] using hzα i
        have hlast : (S_all (Fin.last n)).card = 2 * K - ∑ i : Fin n, α i := by
          simpa only [S_all, particleSym54_last] using hzblank
        rw [hcast, hlast]
        omega
      have hunion : Finset.univ.biUnion S_all = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [Finset.card_biUnion (fun j₁ _ j₂ _ hj => hdisj (Finset.mem_univ j₁) (Finset.mem_univ j₂) hj),
          hcard_sum, Fintype.card_fin]
      have hexists : ∀ r : Fin (2 * K), ∃ j : Fin (n + 1), splitReg (2 * K) s z r = particleSym54 n s j := by
        intro r
        have hr : r ∈ Finset.univ.biUnion S_all := hunion ▸ Finset.mem_univ r
        rcases Finset.mem_biUnion.mp hr with ⟨j, _, hjr⟩
        exact ⟨j, (Finset.mem_filter.mp hjr).2⟩
      let y : Fin (2 * K) → Fin (n + 1) := fun r => Classical.choose (hexists r)
      have hy_eq : fEnc y = z := by
        have hy_split : (fun r => particleSym54 n s (y r)) = splitReg (2 * K) s z :=
          funext fun r => (Classical.choose_spec (hexists r)).symm
        change flatReg (2 * K) s (fun r => particleSym54 n s (y r)) = z
        rw [hy_split, flatReg_splitReg z]
      have hzα' : ∀ i : Fin n,
          (Finset.univ.filter fun r : Fin (2 * K) =>
            splitReg (2 * K) (Nat.clog 2 n + 1) (fEnc y) r = natToBits (Nat.clog 2 n + 1) i.val).card = α i := by
        simpa only [hy_eq] using hzα
      have hzblank' :
          (Finset.univ.filter fun r : Fin (2 * K) =>
            splitReg (2 * K) (Nat.clog 2 n + 1) (fEnc y) r = blankSym54 (Nat.clog 2 n + 1)).card =
            2 * K - ∑ i : Fin n, α i := by
        simpa only [hy_eq] using hzblank
      have hy_orb : ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = y :=
        (comb.orbit_particleSym54_iff_multinom n K α l hα hblank y).mpr ⟨hzα', hzblank'⟩
      exact ⟨⟨y, hy_orb⟩, hy_eq⟩
  by_cases hex : ∃ y : { w : Fin (2 * K) → Fin (n + 1) // ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = w },
      fEnc y.1 = z
  · rcases hex with ⟨y₀, hy₀⟩
    have hcond : (∀ i : Fin n, (Finset.univ.filter fun r : Fin (2 * K) => splitReg (2 * K) s z r = natToBits s i.val).card = α i) ∧
        (Finset.univ.filter fun r : Fin (2 * K) => splitReg (2 * K) s z r = blankSym54 s).card = 2 * K - ∑ i : Fin n, α i :=
      hcond_iff.mp ⟨y₀, hy₀⟩
    rw [if_pos hcond]
    have hsum1 : ∑ y : { w : Fin (2 * K) → Fin (n + 1) // ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = w },
        (ket (fEnc y.1)) z = 1 := by
      rw [Finset.sum_eq_single y₀]
      · simp [ket, hy₀]
      · intro y _ hy
        have hne : z ≠ fEnc y.1 := fun h => hy (Subtype.ext (hfEnc_inj (h.symm.trans hy₀.symm)))
        simp [ket, hne]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [hsum1, mul_one, hcard]
  · have hcond : ¬ ((∀ i : Fin n, (Finset.univ.filter fun r : Fin (2 * K) => splitReg (2 * K) s z r = natToBits s i.val).card = α i) ∧
        (Finset.univ.filter fun r : Fin (2 * K) => splitReg (2 * K) s z r = blankSym54 s).card = 2 * K - ∑ i : Fin n, α i) :=
      fun h => hex (hcond_iff.mpr h)
    rw [if_neg hcond]
    have hsum0 : ∑ y : { w : Fin (2 * K) → Fin (n + 1) // ∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = w },
        (ket (fEnc y.1)) z = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      have hne : z ≠ fEnc y.1 := fun h => hex ⟨y, h.symm⟩
      simp [ket, hne]
    rw [hsum0, mul_zero]

lemma fullCirc_size_bound (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (as : AlonsoSchottSil54) (hl : HarmBucketHL54V2)
    (n K : ℕ) (hn : 1 ≤ n) (hK : 1 ≤ K) :
    let L := Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1
    let C_sym := 4 * as.C_as + 44 * br.C_sort + 16 + 5 * hl.C_hl * (2 : ℝ) ^ hl.K_hl
    let K_sym := max 4 hl.K_hl
    ((fullCirc br arith as hl n K hn hK).size : ℝ) ≤
      C_sym * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
  intro L C_sym K_sym
  have hd_pos : 1 ≤ lay_d K := d_pos K hK
  have hs_pos : 1 ≤ lay_s n := Nat.succ_pos _
  have hL_pos : (1 : ℝ) ≤ L := by exact_mod_cast (Nat.succ_pos _ : 1 ≤ L)
  have hs_le_L : lay_s n ≤ L := by
    dsimp only [lay_s, L]
    have hmono : Nat.clog 2 n ≤ Nat.clog 2 ((K + 1) * (n + 1) + 2) :=
      Nat.clog_mono_right 2 (by nlinarith)
    omega
  have hd1_le_L : lay_d K + 1 ≤ L := by
    dsimp only [lay_d, L]
    have hmono : Nat.clog 2 (2 * K) ≤ Nat.clog 2 ((K + 1) * (n + 1) + 2) :=
      Nat.clog_mono_right 2 (by nlinarith)
    omega
  have hM_lt : lay_M K < 4 * K := arity_lt_four_mul_K K hK
  have hM_le_Ks_nat : lay_M K ≤ 4 * (K * lay_s n) := by nlinarith
  have hM_le_Ks : ((lay_M K : ℕ) : ℝ) ≤ 4 * ((K * lay_s n : ℕ) : ℝ) := by
    exact_mod_cast hM_le_Ks_nat
  have hKs_nonneg : (0 : ℝ) ≤ ((K * lay_s n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL4_le : (L : ℝ) ^ 4 ≤ (L : ℝ) ^ K_sym :=
    pow_le_pow_right₀ hL_pos (le_max_left 4 hl.K_hl)
  have hLhl_le : (L : ℝ) ^ hl.K_hl ≤ (L : ℝ) ^ K_sym :=
    pow_le_pow_right₀ hL_pos (le_max_right 4 hl.K_hl)
  have hd1_R : ((lay_d K + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hd1_le_L
  have hw2_R : ((lay_w₂ n K + 1 : ℕ) : ℝ) ≤ 3 * (L : ℝ) := by
    have : lay_w₂ n K + 1 ≤ 3 * L := by dsimp only [lay_w₂]; omega
    exact_mod_cast this
  have hcirc0_size : ((circ0 as hl n K hK).size : ℝ) ≤ 4 * as.C_as * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
    calc ((circ0 as hl n K hK).size : ℝ)
        = ((as.unifPermCircuit (2 * K) (lay_d K) (by omega) hd_pos (two_mul_K_le_arity K)).size : ℝ) := by
            simp [circ0, LayeredCircuit.mapWires_size]
      _ ≤ as.C_as * (lay_M K : ℝ) * ((lay_d K + 1 : ℕ) : ℝ) ^ 4 :=
            as.unifPermCircuit_size (2 * K) (lay_d K) (by omega) hd_pos (two_mul_K_le_arity K)
      _ ≤ as.C_as * (4 * ((K * lay_s n : ℕ) : ℝ)) * (L : ℝ) ^ K_sym := by
            have hC := as.C_as_pos.le
            have hpow4 : ((lay_d K + 1 : ℕ) : ℝ) ^ 4 ≤ (L : ℝ) ^ 4 :=
              pow_le_pow_left₀ (by positivity) hd1_R 4
            calc as.C_as * (lay_M K : ℝ) * ((lay_d K + 1 : ℕ) : ℝ) ^ 4
                ≤ as.C_as * (4 * ((K * lay_s n : ℕ) : ℝ)) * (L : ℝ) ^ 4 := by gcongr
              _ ≤ as.C_as * (4 * ((K * lay_s n : ℕ) : ℝ)) * (L : ℝ) ^ K_sym := by gcongr
      _ = 4 * as.C_as * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by ring
  have h2M_eq : (2 ^ (lay_d K) : ℝ) = (lay_M K : ℝ) := by exact_mod_cast (arity_eq_two_pow (lay_d K)).symm
  have hcirc1a_size : ((circ1a br as hl n K).size : ℝ) ≤ 4 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
    have hb := br.bitonicSortKeyCircuit_size (lay_d K) (lay_d K) 0 true
    rw [h2M_eq] at hb
    simp only [Nat.cast_zero, add_zero] at hb
    calc ((circ1a br as hl n K).size : ℝ)
        = ((br.bitonicSortKeyCircuit (lay_d K) (lay_d K) 0 true).size : ℝ) := by
            simp [circ1a, LayeredCircuit.mapWires_size]
      _ ≤ br.C_sort * (lay_M K : ℝ) * ((lay_d K + 1 : ℝ) ^ 2) * (lay_d K + 1 : ℝ) := hb
      _ ≤ br.C_sort * (4 * ((K * lay_s n : ℕ) : ℝ)) * (L : ℝ) ^ 2 * (L : ℝ) := by
            have hC := br.hC_sort_pos.le
            have hd1' : (lay_d K + 1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hd1_le_L
            gcongr
      _ = 4 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ 3 := by ring
      _ ≤ 4 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
            have hC := br.hC_sort_pos.le
            have h3 : (L : ℝ) ^ 3 ≤ (L : ℝ) ^ K_sym :=
              pow_le_pow_right₀ hL_pos (le_trans (by decide : 3 ≤ 4) (le_max_left 4 hl.K_hl))
            gcongr
  have hcirc1b_size : ((circ1b br as hl n K).size : ℝ) ≤ 8 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
    have hb := br.unrouteSortCircuit_size (lay_d K) (lay_s n)
    rw [h2M_eq] at hb
    calc ((circ1b br as hl n K).size : ℝ)
        = ((br.unrouteSortCircuit (lay_d K) (lay_s n)).size : ℝ) := by
            simp [circ1b, LayeredCircuit.mapWires_size]
      _ ≤ br.C_sort * (lay_M K : ℝ) * ((lay_d K + 1 : ℝ) ^ 2) * (lay_s n + 1 : ℝ) := hb
      _ ≤ br.C_sort * (4 * ((K * lay_s n : ℕ) : ℝ)) * (L : ℝ) ^ 2 * (2 * (L : ℝ)) := by
            have hC := br.hC_sort_pos.le
            have hd1' : (lay_d K + 1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hd1_le_L
            have hs1' : (lay_s n + 1 : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast (by omega : lay_s n + 1 ≤ 2 * L)
            gcongr
      _ = 8 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ 3 := by ring
      _ ≤ 8 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
            have hC := br.hC_sort_pos.le
            have h3 : (L : ℝ) ^ 3 ≤ (L : ℝ) ^ K_sym :=
              pow_le_pow_right₀ hL_pos (le_trans (by decide : 3 ≤ 4) (le_max_left 4 hl.K_hl))
            gcongr
  have hcirc2a_nat : (circ2a arith as hl n K).size ≤ lay_M K * (1 + lay_s n + lay_d K) := by
    have hslot : ∀ lc ∈ (List.finRange (lay_M K)).map (circ2aSlot arith as hl n K),
        lc.size ≤ 1 + lay_s n + lay_d K := by
      intro lc hlc
      rw [List.mem_map] at hlc
      rcases hlc with ⟨p, _, rfl⟩
      dsimp only [circ2aSlot]
      split_ifs
      · simp only [LayeredCircuit.mapWires_size]
        have hcp := arith.copyRegCircuit_size (lay_s n)
        omega
      · simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size]
        have hs1 := arith.setConstMSBCircuit_size 1 1
        have hs2 := arith.setConstMSBCircuit_size (lay_d K) p.1
        omega
    have hle := LayeredCircuit_seqList_size_le _ (1 + lay_s n + lay_d K) hslot
    simpa [circ2a] using hle
  have hcirc2a_size : ((circ2a arith as hl n K).size : ℝ) ≤ 8 * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
    have hw_le : 1 + lay_s n + lay_d K ≤ 2 * L := by omega
    calc ((circ2a arith as hl n K).size : ℝ)
        ≤ (lay_M K : ℝ) * ((1 + lay_s n + lay_d K : ℕ) : ℝ) := by exact_mod_cast hcirc2a_nat
      _ ≤ (4 * ((K * lay_s n : ℕ) : ℝ)) * (2 * (L : ℝ)) := by
            have : ((1 + lay_s n + lay_d K : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hw_le
            gcongr
      _ = 8 * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ 1 := by ring
      _ ≤ 8 * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
            have h1 : (L : ℝ) ^ 1 ≤ (L : ℝ) ^ K_sym :=
              pow_le_pow_right₀ hL_pos (le_trans (by decide : 1 ≤ 4) (le_max_left 4 hl.K_hl))
            gcongr
  have hcirc2b_size : ((circ2b br as hl n K).size : ℝ) ≤ 12 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
    have hb := br.bitonicSortKeyCircuit_size (lay_d K) (lay_w₂ n K) 0 true
    rw [h2M_eq] at hb
    simp only [Nat.cast_zero, add_zero] at hb
    calc ((circ2b br as hl n K).size : ℝ)
        = ((br.bitonicSortKeyCircuit (lay_d K) (lay_w₂ n K) 0 true).size : ℝ) := by
            simp [circ2b, LayeredCircuit.mapWires_size]
      _ ≤ br.C_sort * (lay_M K : ℝ) * ((lay_d K + 1 : ℝ) ^ 2) * (lay_w₂ n K + 1 : ℝ) := hb
      _ ≤ br.C_sort * (4 * ((K * lay_s n : ℕ) : ℝ)) * (L : ℝ) ^ 2 * (3 * (L : ℝ)) := by
            have hC := br.hC_sort_pos.le
            have hd1' : (lay_d K + 1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hd1_le_L
            have hw2' : (lay_w₂ n K + 1 : ℝ) ≤ 3 * (L : ℝ) := by
              have : ((lay_w₂ n K + 1 : ℕ) : ℝ) ≤ 3 * (L : ℝ) := hw2_R
              simpa using this
            gcongr
      _ = 12 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ 3 := by ring
      _ ≤ 12 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
            have hC := br.hC_sort_pos.le
            have h3 : (L : ℝ) ^ 3 ≤ (L : ℝ) ^ K_sym :=
              pow_le_pow_right₀ hL_pos (le_trans (by decide : 3 ≤ 4) (le_max_left 4 hl.K_hl))
            gcongr
  have hcirc2c_size : ((circ2c br as hl n K).size : ℝ) ≤ 4 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
    have hb := br.routeSortCircuit_size (lay_d K) (lay_d K)
    rw [h2M_eq] at hb
    calc ((circ2c br as hl n K).size : ℝ)
        = ((br.routeSortCircuit (lay_d K) (lay_d K)).size : ℝ) := by
            simp [circ2c, LayeredCircuit.mapWires_size]
      _ ≤ br.C_sort * (lay_M K : ℝ) * ((lay_d K + 1 : ℝ) ^ 2) * (lay_d K + 1 : ℝ) := hb
      _ ≤ br.C_sort * (4 * ((K * lay_s n : ℕ) : ℝ)) * (L : ℝ) ^ 2 * (L : ℝ) := by
            have hC := br.hC_sort_pos.le
            have hd1' : (lay_d K + 1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hd1_le_L
            gcongr
      _ = 4 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ 3 := by ring
      _ ≤ 4 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
            have hC := br.hC_sort_pos.le
            have h3 : (L : ℝ) ^ 3 ≤ (L : ℝ) ^ K_sym :=
              pow_le_pow_right₀ hL_pos (le_trans (by decide : 3 ≤ 4) (le_max_left 4 hl.K_hl))
            gcongr
  have hcirc2d_size : ((circ2d as hl n K hn hK).size : ℝ) ≤
      5 * hl.C_hl * (2 : ℝ) ^ hl.K_hl * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
    have hb := hl.harmBucketH_lCircuit_size n K (lay_d K) hn hK hd_pos (two_mul_K_le_arity K)
    calc ((circ2d as hl n K hn hK).size : ℝ)
        = ((hl.harmBucketH_lCircuit n K (lay_d K) hn hK hd_pos (two_mul_K_le_arity K)).size : ℝ) := by
            simp [circ2d]
      _ ≤ hl.C_hl * ((K * lay_s n + lay_M K : ℕ) : ℝ) * ((L + lay_d K : ℕ) : ℝ) ^ hl.K_hl := hb
      _ ≤ hl.C_hl * (5 * ((K * lay_s n : ℕ) : ℝ)) * ((2 : ℝ) ^ hl.K_hl * (L : ℝ) ^ K_sym) := by
            have hC := hl.C_hl_pos.le
            have h5n : K * lay_s n + lay_M K ≤ 5 * (K * lay_s n) := by omega
            have h5 : ((K * lay_s n + lay_M K : ℕ) : ℝ) ≤ 5 * ((K * lay_s n : ℕ) : ℝ) := by
              exact_mod_cast h5n
            have hLd : ((L + lay_d K : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by
              exact_mod_cast (by omega : L + lay_d K ≤ 2 * L)
            have hLd_pow : ((L + lay_d K : ℕ) : ℝ) ^ hl.K_hl ≤ (2 : ℝ) ^ hl.K_hl * (L : ℝ) ^ K_sym :=
              calc ((L + lay_d K : ℕ) : ℝ) ^ hl.K_hl
                  ≤ (2 * (L : ℝ)) ^ hl.K_hl := pow_le_pow_left₀ (by positivity) hLd hl.K_hl
                _ = (2 : ℝ) ^ hl.K_hl * (L : ℝ) ^ hl.K_hl := mul_pow 2 (L : ℝ) hl.K_hl
                _ ≤ (2 : ℝ) ^ hl.K_hl * (L : ℝ) ^ K_sym := by gcongr
            gcongr
      _ = 5 * hl.C_hl * (2 : ℝ) ^ hl.K_hl * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by ring
  have htotal : (fullCirc br arith as hl n K hn hK).size =
      (circ0 as hl n K hK).size +
        (2 * (circ1a br as hl n K).size + (circ1b br as hl n K).size) +
        2 * (circ2a arith as hl n K).size +
        2 * (circ2b br as hl n K).size +
        (circ2c br as hl n K).size +
        (circ2d as hl n K hn hK).size := by
    simp only [fullCirc, circ1, LayeredCircuit.seqList_size, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, LayeredCircuit.seq_size, LayeredCircuit.adj_size]
    omega
  have htotal_R : ((fullCirc br arith as hl n K hn hK).size : ℝ) =
      ((circ0 as hl n K hK).size : ℝ) +
        (2 * ((circ1a br as hl n K).size : ℝ) + ((circ1b br as hl n K).size : ℝ)) +
        2 * ((circ2a arith as hl n K).size : ℝ) +
        2 * ((circ2b br as hl n K).size : ℝ) +
        ((circ2c br as hl n K).size : ℝ) +
        ((circ2d as hl n K hn hK).size : ℝ) := by
    exact_mod_cast htotal
  have hsum_bd :
      ((circ0 as hl n K hK).size : ℝ) +
        (2 * ((circ1a br as hl n K).size : ℝ) + ((circ1b br as hl n K).size : ℝ)) +
        2 * ((circ2a arith as hl n K).size : ℝ) +
        2 * ((circ2b br as hl n K).size : ℝ) +
        ((circ2c br as hl n K).size : ℝ) +
        ((circ2d as hl n K hn hK).size : ℝ) ≤
      (4 * as.C_as * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym) +
        (2 * (4 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym) +
          8 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym) +
        2 * (8 * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym) +
        2 * (12 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym) +
        4 * br.C_sort * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym +
        5 * hl.C_hl * (2 : ℝ) ^ hl.K_hl * ((K * lay_s n : ℕ) : ℝ) * (L : ℝ) ^ K_sym := by
    linarith
  rw [htotal_R]
  refine hsum_bd.trans_eq ?_
  dsimp only [C_sym]
  ring

end Aux_nsil_sym_54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem solution :
    ∃ (C_sym : ℝ), 0 < C_sym ∧ ∃ (K_sym : ℕ),
      ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
        let s := Nat.clog 2 n + 1
        ∃ (e_sym : ℕ) (V_sym : Circuit gates12 (2 * K * s + e_sym)),
          ((V_sym.size : ℕ) : ℝ) ≤
            C_sym * ((K * s : ℕ) : ℝ) *
              ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_sym ∧
          ∀ (α : Fin n → ℕ) (hk : K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K)
            (l : Fin (2 * K) → Fin (n + 1)),
            Monotone l →
            (∀ i : Fin n, (Finset.univ.filter fun p => l p = ⟨i.1, by omega⟩).card = α i) →
            (Finset.univ.filter fun p => l p = ⟨n, Nat.lt_succ_self n⟩).card = 2 * K - ∑ i, α i →
            act V_sym.unitary (padKet e_sym (ket (flatReg (2 * K) s fun p => particleSym54 n s (l p)))) =
              padKet e_sym (multinomKet54 n s K α hk) := by
  rcases QuantumLTF.Membership.Supplement.bitonic_routing_54 with ⟨br⟩
  rcases QuantumLTF.Membership.Supplement.lcg_sym_comb_54 with ⟨comb⟩
  rcases QuantumLTF.Membership.Supplement.lcg_sym_arith_54 with ⟨arith⟩
  rcases QuantumLTF.Membership.Supplement.alonso_schott_sil_54 with ⟨as⟩
  rcases QuantumLTF.Membership.Supplement.harm_bucket_hl_54_v2 with ⟨hl⟩
  refine ⟨4 * as.C_as + 44 * br.C_sort + 16 + 5 * hl.C_hl * (2 : ℝ) ^ hl.K_hl, ?_, max 4 hl.K_hl, ?_⟩
  · have hhl_pow : (0 : ℝ) < 5 * hl.C_hl * (2 : ℝ) ^ hl.K_hl := by
      have hhl := hl.C_hl_pos
      positivity
    linarith [as.C_as_pos, br.hC_sort_pos, hhl_pow]
  · intro n K hn hK s
    refine ⟨Aux_nsil_sym_54.lay_e as hl n K,
      (Aux_nsil_sym_54.fullCirc br arith as hl n K hn hK).toCircuit, ?_, ?_⟩
    · exact Aux_nsil_sym_54.fullCirc_size_bound br arith as hl n K hn hK
    · intro α hk l hlm hα hblank
      change act (Aux_nsil_sym_54.fullCirc br arith as hl n K hn hK).unitary _ = _
      rw [Aux_nsil_sym_54.act_fullCirc br arith as hl n K comb hn hK l hlm]
      congr 1
      exact Aux_nsil_sym_54.orbit_sum_eq_multinomKet54 comb n K α hk l hα hblank
