-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.alonso_schott_sil_54
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T04:56:50.935959+00:00
-- url     : https://prove2.me/submissions/c64f5d0b-d572-4f4d-84e9-84a1dec67898

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Circs
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Theorems.Thm_QuantumLTF_Membership_Supplement_bitonic_routing_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_lcg_sym_comb_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_lcg_sym_arith_54

set_option autoImplicit false

namespace Aux_w54_as

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

/-! ### Part 1: Bitwise & Circuit Sequence Helpers -/

lemma natToBits_mod (comb : LcgSym54Comb) (w x : ℕ) :
    natToBits w (x % 2 ^ w) = natToBits w x := by
  funext i
  rw [← Fin.rev_rev i, comb.natToBits_comp_revPerm, comb.natToBits_comp_revPerm,
    Nat.testBit_mod_two_pow, decide_eq_true i.rev.isLt, Bool.true_and]

lemma natToBits_add_two_pow (comb : LcgSym54Comb) (w x : ℕ) :
    natToBits w (2 ^ w + x) = natToBits w x := by
  rw [← natToBits_mod comb w (2 ^ w + x), Nat.add_mod_left, natToBits_mod comb]

lemma natToBits_zero (comb : LcgSym54Comb) (w : ℕ) : natToBits w 0 = fun _ => false := by
  funext i
  rw [← Fin.rev_rev i, comb.natToBits_comp_revPerm]
  simp

lemma natToBits_bitsToNat (comb : LcgSym54Comb) {w : ℕ} (b : Qubits w) :
    natToBits w (bitsToNat b) = b :=
  comb.bitsToNat_inj (comb.bitsToNat_natToBits (comb.bitsToNat_lt_two_pow b))

lemma natToBits_inj (comb : LcgSym54Comb) {w a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : natToBits w a = natToBits w b) : a = b := by
  have := congrArg bitsToNat h
  rwa [comb.bitsToNat_natToBits ha, comb.bitsToNat_natToBits hb] at this

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

lemma act_seqList_fin {m n : ℕ} (f : Fin n → LayeredCircuit m) (inv : ℕ → Qubits m)
    (hstep : ∀ k : Fin n, act (f k).unitary (ket (inv k.1)) = ket (inv (k.1 + 1))) :
    act (LayeredCircuit.seqList ((List.finRange n).map f)).unitary (ket (inv 0)) = ket (inv n) := by
  have hgen : ∀ lcs : List (LayeredCircuit m), ∀ j : ℕ,
      (∀ t (ht : t < lcs.length),
        act (lcs[t]'ht).unitary (ket (inv (j + t))) = ket (inv (j + t + 1))) →
      act (LayeredCircuit.seqList lcs).unitary (ket (inv j)) = ket (inv (j + lcs.length)) := by
    intro lcs
    induction lcs with
    | nil => intro j _; simp [LayeredCircuit.seqList, act_one]
    | cons lc rest ih =>
      intro j hs
      simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul, List.length_cons]
      have h0 := hs 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at h0
      rw [h0]
      have hrest := ih (j + 1) (fun t ht => by
        rw [show j + 1 + t = j + (t + 1) by omega]
        exact hs (t + 1) (by simp; omega))
      rwa [show j + 1 + rest.length = j + (rest.length + 1) by omega] at hrest
  have hmain := hgen ((List.finRange n).map f) 0 (fun t ht => by
    simp only [List.length_map, List.length_finRange] at ht
    simp only [List.getElem_map, List.getElem_finRange, Nat.zero_add]
    exact hstep ⟨t, ht⟩)
  simpa using hmain

lemma seqList_size_le {m : ℕ} (lcs : List (LayeredCircuit m)) (B : ℕ)
    (hB : ∀ lc ∈ lcs, lc.size ≤ B) : (LayeredCircuit.seqList lcs).size ≤ lcs.length * B := by
  rw [LayeredCircuit.seqList_size]
  induction lcs with
  | nil => simp
  | cons lc rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := hB lc List.mem_cons_self
    have h2 := ih fun lc' hlc' => hB lc' (List.mem_cons_of_mem _ hlc')
    omega

lemma seqList_fin_size_le {m n : ℕ} (f : Fin n → LayeredCircuit m) (B : ℕ)
    (hB : ∀ k : Fin n, (f k).size ≤ B) :
    (LayeredCircuit.seqList ((List.finRange n).map f)).size ≤ n * B := by
  have h := seqList_size_le ((List.finRange n).map f) B (fun lc hlc => by
    rcases List.mem_map.mp hlc with ⟨k, _, rfl⟩
    exact hB k)
  simpa using h

lemma act_adj_ket {m : ℕ} (lc : LayeredCircuit m) {ψ φ : EuclideanSpace ℂ (Qubits m)}
    (h : act lc.unitary ψ = φ) :
    act lc.adj.unitary φ = ψ := by
  rw [← h, ← act_mul, LayeredCircuit.adj_unitary,
    Matrix.mem_unitaryGroup_iff'.mp lc.unitary_mem_unitaryGroup, act_one]

/-! ### Part 2: Embedding & `updateOn` Combinators -/

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

@[simp] lemma regEmb_apply {m : ℕ} (off N w : ℕ) (h : off + N * w ≤ m) (i : Fin (N * w)) :
    regEmb off N w h i = ⟨off + i.1, by omega⟩ := rfl

def slotInReg (N w : ℕ) (j : Fin N) : Fin w ↪ Fin (N * w) where
  toFun b := finProdFinEquiv (j, b)
  inj' _ _ h := (Prod.ext_iff.mp (finProdFinEquiv.injective h)).2

def slotEmb {m : ℕ} (off N w : ℕ) (h : off + N * w ≤ m) (j : Fin N) : Fin w ↪ Fin m :=
  (slotInReg N w j).trans (regEmb off N w h)

lemma slotInReg_disjoint {N w : ℕ} {j1 j2 : Fin N} (hj : j1 ≠ j2) :
    ∀ b1 b2, slotInReg N w j1 b1 ≠ slotInReg N w j2 b2 := by
  intro b1 b2 h
  exact hj (Prod.ext_iff.mp (finProdFinEquiv.injective h)).1

lemma slotEmb_disjoint_slot {m off N w : ℕ} (h : off + N * w ≤ m) {j1 j2 : Fin N} (hj : j1 ≠ j2) :
    ∀ b1 b2, slotEmb off N w h j1 b1 ≠ slotEmb off N w h j2 b2 :=
  fun b1 b2 hij => slotInReg_disjoint hj b1 b2 ((regEmb off N w h).injective hij)

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

@[simp] lemma slotInReg_apply (N w : ℕ) (j : Fin N) (b : Fin w) :
    slotInReg N w j b = finProdFinEquiv (j, b) := rfl

@[simp] lemma flatReg_comp_slotInReg {N w : ℕ} (arr : Fin N → Qubits w) (j : Fin N) :
    flatReg N w arr ∘ slotInReg N w j = arr j := by
  funext b; simp [flatReg, slotInReg_apply]

lemma flatReg_zero {N w : ℕ} : flatReg N w (fun _ _ => false) = fun _ => false := by
  funext i; simp [flatReg]

lemma updateOn_comp_disjoint {k1 k2 m : ℕ} (e1 : Fin k1 ↪ Fin m) (e2 : Fin k2 ↪ Fin m)
    (hdisj : ∀ i j, e1 i ≠ e2 j) (z : Qubits m) (val : Qubits k1) :
    updateOn e1 z val ∘ e2 = z ∘ e2 := by
  funext j; apply updateOn_apply_not_mem; rintro ⟨i, hi⟩; exact hdisj i j hi

lemma updateOn_comp_self' {k m : ℕ} (e : Fin k ↪ Fin m) (z : Qubits m) (val : Qubits k) :
    updateOn e z val ∘ e = val := by
  funext i; exact updateOn_apply_emb e z val i

lemma updateOn_comp_trans {k1 k2 m : ℕ} (f : Fin k1 ↪ Fin k2) (e : Fin k2 ↪ Fin m)
    (z : Qubits m) (val : Qubits k1) :
    updateOn (f.trans e) z val ∘ e = updateOn f (z ∘ e) val := by
  funext i
  dsimp only [Function.comp_apply]
  by_cases hi : i ∈ Set.range f
  · rcases hi with ⟨a, rfl⟩
    change updateOn (f.trans e) z val ((f.trans e) a) = _
    rw [updateOn_apply_emb, updateOn_apply_emb]
  · rw [updateOn_apply_not_mem f (z ∘ e) val hi, updateOn_apply_not_mem]
    · rfl
    · rintro ⟨a, ha⟩; exact hi ⟨a, e.injective ha⟩

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
  · have hnot : regEmb off N w h (finProdFinEquiv (q, b)) ∉ Set.range (slotEmb off N w h j) := by
      rintro ⟨b', hb'⟩
      exact slotInReg_disjoint hq b b' ((regEmb off N w h).injective hb').symm
    rw [updateOn_apply_not_mem _ _ _ hnot, Function.update_of_ne hq]
    have hpt := congrFun hz (finProdFinEquiv (q, b))
    simpa [Function.comp_apply, flatReg] using hpt

lemma updateOn_trans_slotEmb_comp_regEmb {m off N w l : ℕ} (h : off + N * w ≤ m)
    (f : Fin l ↪ Fin w) (z : Qubits m) (arr : Fin N → Qubits w)
    (hz : z ∘ regEmb off N w h = flatReg N w arr) (j : Fin N) (val : Qubits l) :
    updateOn (f.trans (slotEmb off N w h j)) z val ∘ regEmb off N w h =
      flatReg N w (Function.update arr j (updateOn f (arr j) val)) := by
  have hc1 : (f.trans (slotEmb off N w h j)) = ((f.trans (slotInReg N w j)).trans (regEmb off N w h)) := rfl
  rw [hc1, updateOn_comp_trans, hz]
  funext idx
  rcases finProdFinEquiv.surjective idx with ⟨⟨q, b⟩, rfl⟩
  simp only [flatReg, Equiv.symm_apply_apply]
  by_cases hq : q = j
  · subst hq
    rw [Function.update_self]
    by_cases hb : b ∈ Set.range f
    · rcases hb with ⟨a, rfl⟩
      change updateOn (f.trans (slotInReg N w q)) _ val ((f.trans (slotInReg N w q)) a) =
        updateOn f (arr q) val (f a)
      rw [updateOn_apply_emb, updateOn_apply_emb]
    · rw [updateOn_apply_not_mem f (arr q) val hb, updateOn_apply_not_mem]
      · simp [flatReg]
      · rintro ⟨a, ha⟩
        exact hb ⟨a, (slotInReg N w q).injective ha⟩
  · rw [Function.update_of_ne hq]
    rw [updateOn_apply_not_mem]
    · simp [flatReg]
    · rintro ⟨a, ha⟩
      exact slotInReg_disjoint hq b (f a) ha.symm

def prefixRegEmb {m off N K w : ℕ} (h : off + N * w ≤ m) (hKN : K ≤ N) :
    Fin (K * w) ↪ Fin m where
  toFun idx :=
    let p := finProdFinEquiv.symm idx
    regEmb off N w h (finProdFinEquiv (Fin.castLE hKN p.1, p.2))
  inj' i1 i2 hi := by
    have h1 := Prod.ext_iff.mp (finProdFinEquiv.injective ((regEmb off N w h).injective hi))
    have hfst : (finProdFinEquiv.symm i1).1 = (finProdFinEquiv.symm i2).1 :=
      Fin.ext (by have := congrArg Fin.val h1.1; simpa using this)
    exact finProdFinEquiv.symm.injective (Prod.ext hfst h1.2)

lemma prefixRegEmb_mem_regEmb {m off N K w : ℕ} (h : off + N * w ≤ m) (hKN : K ≤ N)
    (idx : Fin (K * w)) :
    prefixRegEmb h hKN idx =
      regEmb off N w h (finProdFinEquiv (Fin.castLE hKN (finProdFinEquiv.symm idx).1,
        (finProdFinEquiv.symm idx).2)) := rfl

lemma comp_prefixRegEmb {m off N K w : ℕ} (h : off + N * w ≤ m) (hKN : K ≤ N)
    (z : Qubits m) (arr : Fin N → Qubits w) (hz : z ∘ regEmb off N w h = flatReg N w arr) :
    z ∘ prefixRegEmb h hKN = flatReg K w (fun p => arr (Fin.castLE hKN p)) := by
  funext idx
  simp only [Function.comp_apply, prefixRegEmb_mem_regEmb]
  have hpt := congrFun hz (finProdFinEquiv (Fin.castLE hKN (finProdFinEquiv.symm idx).1,
    (finProdFinEquiv.symm idx).2))
  simpa [Function.comp_apply, flatReg] using hpt

lemma updateOn_prefixRegEmb_comp_regEmb {m off N K w : ℕ} (h : off + N * w ≤ m) (hKN : K ≤ N)
    (z : Qubits m) (arr : Fin N → Qubits w) (hz : z ∘ regEmb off N w h = flatReg N w arr)
    (arrNew : Fin K → Qubits w) :
    updateOn (prefixRegEmb h hKN) z (flatReg K w arrNew) ∘ regEmb off N w h =
      flatReg N w (fun q => if hq : q.1 < K then arrNew ⟨q.1, hq⟩ else arr q) := by
  funext idx
  rcases finProdFinEquiv.surjective idx with ⟨⟨q, b⟩, rfl⟩
  simp only [Function.comp_apply, flatReg, Equiv.symm_apply_apply]
  by_cases hq : q.1 < K
  · rw [dif_pos hq]
    have hpre : regEmb off N w h (finProdFinEquiv (q, b)) =
        prefixRegEmb h hKN (finProdFinEquiv (⟨q.1, hq⟩, b)) := by
      simp only [prefixRegEmb_mem_regEmb, Equiv.symm_apply_apply]
      rfl
    rw [hpre, updateOn_apply_emb, flatReg, Equiv.symm_apply_apply]
  · rw [dif_neg hq]
    have hnot : regEmb off N w h (finProdFinEquiv (q, b)) ∉ Set.range (prefixRegEmb h hKN) := by
      rintro ⟨idx', hidx'⟩
      have h1 := Prod.ext_iff.mp (finProdFinEquiv.injective ((regEmb off N w h).injective hidx'))
      have hlt : (Fin.castLE hKN (finProdFinEquiv.symm idx').1).1 < K :=
        (finProdFinEquiv.symm idx').1.isLt
      have hqv : q.1 = (Fin.castLE hKN (finProdFinEquiv.symm idx').1).1 :=
        (congrArg Fin.val h1.1).symm
      omega
    rw [updateOn_apply_not_mem _ _ _ hnot]
    have hpt := congrFun hz (finProdFinEquiv (q, b))
    simpa [Function.comp_apply, flatReg] using hpt

lemma sortTraceSize_mono (br : BitonicRouting54) {d1 d2 : ℕ} (h : d1 ≤ d2) :
    sortTraceSize d1 ≤ sortTraceSize d2 := by
  have h1 := br.four_mul_sortTraceSize d1
  have h2 := br.four_mul_sortTraceSize d2
  have hpow : 2 ^ d1 ≤ 2 ^ d2 := Nat.pow_le_pow_right (by norm_num) h
  have hmul : d1 * (d1 + 1) ≤ d2 * (d2 + 1) := Nat.mul_le_mul h (Nat.add_le_add_right h 1)
  have hprod : d1 * (d1 + 1) * 2 ^ d1 ≤ d2 * (d2 + 1) * 2 ^ d2 := Nat.mul_le_mul hmul hpow
  omega

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
  · have hnotB : u ∉ Set.range eB := fun ⟨j, hj⟩ => hu ⟨Fin.natAdd a j, by rw [combineEmb_natAdd]; exact hj⟩
    rw [updateOn_apply_not_mem _ _ _ hu, updateOn_apply_not_mem _ _ _ hnotB]

lemma combineEmb_zero_right {a m : ℕ} (e : Fin a ↪ Fin m) (e0 : Fin 0 ↪ Fin m)
    (h : ∀ i j, e i ≠ e0 j) : combineEmb e e0 h = e := by
  ext i
  have hi : (i : Fin (a + 0)) = Fin.castAdd 0 i := Fin.ext rfl
  conv_lhs => rw [hi]
  rw [combineEmb_castAdd]

lemma act_setConstOn {w c m : ℕ} (arith : LcgSym54ArithV2)
    (eB : Fin w ↪ Fin m) (z : Qubits m) :
    act ((arith.setConstMSBCircuit w c).mapWires eB).unitary (ket z) =
      ket (updateOn eB z (fun j => xor (z (eB j)) (natToBits w c j))) := by
  let embAnc : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have hdisj : ∀ i j, eB i ≠ embAnc j := fun _ j => Fin.elim0 j
  have hsub := arith.act_subReg_perm (arith.setConstMSBCircuit w c) (setConstMSBFn w c)
    (arith.setConstMSBCircuit_implements w c) eB embAnc hdisj z (fun j => Fin.elim0 j)
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

lemma act_addInPlaceOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eA eB : Fin w ↪ Fin m) (eAnc : Fin 1 ↪ Fin m)
    (hAB : ∀ i j, eA i ≠ eB j) (hAA : ∀ i j, eA i ≠ eAnc j) (hBA : ∀ i j, eB i ≠ eAnc j)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.addInPlaceMSBCircuit w).mapWires
        (combineEmb (combineEmb eA eB hAB) eAnc (emb_disjoint_combineEmb hAB hAA hBA))).unitary (ket z) =
      ket (updateOn eB z (natToBits w (bitsToNat (z ∘ eA) + bitsToNat (z ∘ eB)))) := by
  have hsub := arith.act_subReg_perm (arith.addInPlaceMSBCircuit w) (addInPlaceMSBFn w)
    (arith.addInPlaceMSBCircuit_implements w) (combineEmb eA eB hAB) eAnc
    (emb_disjoint_combineEmb hAB hAA hBA) z (fun j => congrFun hzAnc j)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eA eB hAB z (addInPlaceMSBFn w) ?_ _ ?_
  · intro x i
    dsimp only [addInPlaceMSBFn]
    have hlt : (Fin.castAdd w i : Fin (w + w)).1 < w := by dsimp [Fin.castAdd]; exact i.isLt
    rw [dif_pos hlt]
  · intro j
    dsimp only [addInPlaceMSBFn, Function.comp_apply]
    have hge : ¬ ((Fin.natAdd w j : Fin (w + w)).1 < w) := by simp [Fin.natAdd]
    rw [dif_neg hge]
    have hidx : (⟨(Fin.natAdd w j : Fin (w + w)).1 - w, by simp [Fin.natAdd]⟩ : Fin w) = j :=
      Fin.ext (by simp [Fin.natAdd])
    rw [hidx]
    have ha : (fun i : Fin w => z (combineEmb eA eB hAB ⟨i.1, by omega⟩)) = z ∘ eA :=
      funext fun i => by change z (combineEmb eA eB hAB (Fin.castAdd w i)) = z (eA i); rw [combineEmb_castAdd]
    have hb : (fun i : Fin w => z (combineEmb eA eB hAB ⟨w + i.1, by omega⟩)) = z ∘ eB :=
      funext fun i => by change z (combineEmb eA eB hAB (Fin.natAdd w i)) = z (eB i); rw [combineEmb_natAdd]
    rw [ha, hb]

lemma act_subInPlaceOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eA eB : Fin w ↪ Fin m) (eAnc : Fin 1 ↪ Fin m)
    (hAB : ∀ i j, eA i ≠ eB j) (hAA : ∀ i j, eA i ≠ eAnc j) (hBA : ∀ i j, eB i ≠ eAnc j)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.subInPlaceMSBCircuit w).mapWires
        (combineEmb (combineEmb eA eB hAB) eAnc (emb_disjoint_combineEmb hAB hAA hBA))).unitary (ket z) =
      ket (updateOn eB z (natToBits w (2 ^ w + bitsToNat (z ∘ eB) - bitsToNat (z ∘ eA)))) := by
  have hsub := arith.act_subReg_perm (arith.subInPlaceMSBCircuit w) (subInPlaceMSBFn w)
    (arith.subInPlaceMSBCircuit_implements w) (combineEmb eA eB hAB) eAnc
    (emb_disjoint_combineEmb hAB hAA hBA) z (fun j => congrFun hzAnc j)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eA eB hAB z (subInPlaceMSBFn w) ?_ _ ?_
  · intro x i
    dsimp only [subInPlaceMSBFn]
    have hlt : (Fin.castAdd w i : Fin (w + w)).1 < w := by dsimp [Fin.castAdd]; exact i.isLt
    rw [dif_pos hlt]
  · intro j
    dsimp only [subInPlaceMSBFn, Function.comp_apply]
    have hge : ¬ ((Fin.natAdd w j : Fin (w + w)).1 < w) := by simp [Fin.natAdd]
    rw [dif_neg hge]
    have hidx : (⟨(Fin.natAdd w j : Fin (w + w)).1 - w, by simp [Fin.natAdd]⟩ : Fin w) = j :=
      Fin.ext (by simp [Fin.natAdd])
    rw [hidx]
    have ha : (fun i : Fin w => z (combineEmb eA eB hAB ⟨i.1, by omega⟩)) = z ∘ eA :=
      funext fun i => by change z (combineEmb eA eB hAB (Fin.castAdd w i)) = z (eA i); rw [combineEmb_castAdd]
    have hb : (fun i : Fin w => z (combineEmb eA eB hAB ⟨w + i.1, by omega⟩)) = z ∘ eB :=
      funext fun i => by change z (combineEmb eA eB hAB (Fin.natAdd w i)) = z (eB i); rw [combineEmb_natAdd]
    rw [ha, hb]

lemma act_swapRegOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eA eB : Fin w ↪ Fin m) (hAB : ∀ i j, eA i ≠ eB j) (z : Qubits m) :
    act ((arith.swapRegCircuit w).mapWires (combineEmb eA eB hAB)).unitary (ket z) =
      ket (updateOn eB (updateOn eA z (z ∘ eB)) (z ∘ eA)) := by
  let embAnc : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have hdisj : ∀ i j, combineEmb eA eB hAB i ≠ embAnc j := fun _ j => Fin.elim0 j
  have hsub := arith.act_subReg_perm (arith.swapRegCircuit w) (swapRegFn w)
    (arith.swapRegCircuit_implements w) (combineEmb eA eB hAB) embAnc hdisj z (fun j => Fin.elim0 j)
  rw [combineEmb_zero_right] at hsub
  rw [hsub]
  congr 1
  funext u
  by_cases hu : u ∈ Set.range (combineEmb eA eB hAB)
  · rcases hu with ⟨ij, rfl⟩
    induction ij using Fin.addCases with
    | left i =>
      rw [updateOn_apply_emb, combineEmb_castAdd]
      have hnotB : eA i ∉ Set.range eB := by rintro ⟨j, hj⟩; exact hAB i j hj.symm
      rw [updateOn_apply_not_mem _ _ _ hnotB, updateOn_apply_emb]
      dsimp only [swapRegFn, Function.comp_apply]
      have hlt : (Fin.castAdd w i : Fin (w + w)).1 < w := by dsimp [Fin.castAdd]; exact i.isLt
      rw [dif_pos hlt]
      have heq : (⟨w + (Fin.castAdd w i : Fin (w + w)).1, by dsimp [Fin.castAdd]; omega⟩ : Fin (w + w)) =
          Fin.natAdd w i := Fin.ext (by dsimp [Fin.castAdd, Fin.natAdd])
      rw [heq, combineEmb_natAdd]
    | right j =>
      rw [updateOn_apply_emb, combineEmb_natAdd, updateOn_apply_emb]
      dsimp only [swapRegFn, Function.comp_apply]
      have hge : ¬ ((Fin.natAdd w j : Fin (w + w)).1 < w) := by simp [Fin.natAdd]
      rw [dif_neg hge]
      have heq : (⟨(Fin.natAdd w j : Fin (w + w)).1 - w, by simp [Fin.natAdd]; omega⟩ : Fin (w + w)) =
          Fin.castAdd w j := Fin.ext (by simp [Fin.natAdd, Fin.castAdd])
      rw [heq, combineEmb_castAdd]
  · have hnotA : u ∉ Set.range eA := fun ⟨i, hi⟩ => hu ⟨Fin.castAdd w i, by rw [combineEmb_castAdd]; exact hi⟩
    have hnotB : u ∉ Set.range eB := fun ⟨j, hj⟩ => hu ⟨Fin.natAdd w j, by rw [combineEmb_natAdd]; exact hj⟩
    rw [updateOn_apply_not_mem _ _ _ hu, updateOn_apply_not_mem _ _ _ hnotB, updateOn_apply_not_mem _ _ _ hnotA]

lemma act_ctrlConstXorOn {w c m : ℕ} (arith : LcgSym54ArithV2)
    (eC : Fin 1 ↪ Fin m) (eB : Fin w ↪ Fin m) (hCB : ∀ i j, eC i ≠ eB j) (z : Qubits m) :
    act ((arith.ctrlConstXorMSBCircuit w c).mapWires (combineEmb eC eB hCB)).unitary (ket z) =
      ket (updateOn eB z (if z (eC 0) then fun j => xor (z (eB j)) (natToBits w c j) else z ∘ eB)) := by
  let embAnc : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have hdisj : ∀ i j, combineEmb eC eB hCB i ≠ embAnc j := fun _ j => Fin.elim0 j
  have hsub := arith.act_subReg_perm (arith.ctrlConstXorMSBCircuit w c) (ctrlConstXorMSBFn w c)
    (arith.ctrlConstXorMSBCircuit_implements w c) (combineEmb eC eB hCB) embAnc hdisj z (fun j => Fin.elim0 j)
  rw [combineEmb_zero_right] at hsub
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eC eB hCB z (ctrlConstXorMSBFn w c) ?_ _ ?_
  · intro x i
    have hi0 : i = 0 := Fin.ext (by omega); subst hi0
    dsimp only [ctrlConstXorMSBFn]
    have hlt : ¬ (1 ≤ (Fin.castAdd w (0 : Fin 1) : Fin (1 + w)).1) := by simp
    split_ifs <;> simp
  · intro j
    dsimp only [ctrlConstXorMSBFn, Function.comp_apply]
    have hc0 : z (combineEmb eC eB hCB ⟨0, by omega⟩) = z (eC 0) := by
      change z (combineEmb eC eB hCB (Fin.castAdd w 0)) = z (eC 0); simp
    have hge : 1 ≤ (Fin.natAdd 1 j : Fin (1 + w)).1 := by simp [Fin.natAdd]
    cases hx : z (eC 0)
    · rw [if_neg (by rw [hc0, hx]; decide), if_neg (by simp)]
      simp [combineEmb_natAdd]
    · rw [if_pos (by rw [hc0, hx]), if_pos (by simp), dif_pos hge, combineEmb_natAdd]
      have hidx : (⟨(Fin.natAdd 1 j : Fin (1 + w)).1 - 1, by simp [Fin.natAdd]⟩ : Fin w) = j :=
        Fin.ext (by simp [Fin.natAdd])
      rw [hidx]

lemma act_ltConstOn {w H m : ℕ} (arith : LcgSym54ArithV2)
    (eIn : Fin w ↪ Fin m) (eOut : Fin 1 ↪ Fin m) (eAnc : Fin w ↪ Fin m)
    (hIO : ∀ i j, eIn i ≠ eOut j) (hIA : ∀ i k, eIn i ≠ eAnc k) (hOA : ∀ j k, eOut j ≠ eAnc k)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.ltConstMSBCircuit w H).mapWires
        (combineEmb (combineEmb eIn eOut hIO) eAnc (emb_disjoint_combineEmb hIO hIA hOA))).unitary (ket z) =
      ket (updateOn eOut z (fun _ => xor (z (eOut 0)) (decide (bitsToNat (z ∘ eIn) < H)))) := by
  have hsub := arith.act_subReg_perm (arith.ltConstMSBCircuit w H) (ltConstMSBFn w H)
    (arith.ltConstMSBCircuit_implements w H) (combineEmb eIn eOut hIO) eAnc
    (emb_disjoint_combineEmb hIO hIA hOA) z (fun j => congrFun hzAnc j)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eIn eOut hIO z (ltConstMSBFn w H) ?_ _ ?_
  · intro x i
    dsimp only [ltConstMSBFn]
    have hne : Fin.castAdd 1 i ≠ ⟨w, Nat.lt_succ_self w⟩ := Fin.ne_of_val_ne (by simp; omega)
    rw [Function.update_of_ne hne]
  · intro j
    have hj0 : j = 0 := Fin.ext (by omega); subst hj0
    dsimp only [ltConstMSBFn, Function.comp_apply]
    have hnw : Fin.natAdd w (0 : Fin 1) = ⟨w, Nat.lt_succ_self w⟩ := rfl
    rw [hnw, Function.update_self]
    have hc : combineEmb eIn eOut hIO ⟨w, Nat.lt_succ_self w⟩ = eOut 0 := by
      rw [← hnw, combineEmb_natAdd]
    have hin : (fun i : Fin w => z (combineEmb eIn eOut hIO ⟨i.1, by omega⟩)) = z ∘ eIn :=
      funext fun i => by change z (combineEmb eIn eOut hIO (Fin.castAdd 1 i)) = z (eIn i); rw [combineEmb_castAdd]
    rw [hc, hin]

lemma act_ctrlAddInPlaceOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eC : Fin 1 ↪ Fin m) (eA eB : Fin w ↪ Fin m) (eAnc : Fin (w + 1) ↪ Fin m)
    (hCA : ∀ i j, eC i ≠ eA j) (hCB : ∀ i j, eC i ≠ eB j) (hAB : ∀ i j, eA i ≠ eB j)
    (hCAnc : ∀ i k, eC i ≠ eAnc k) (hAAnc : ∀ i k, eA i ≠ eAnc k) (hBAnc : ∀ i k, eB i ≠ eAnc k)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.ctrlAddInPlaceMSBCircuit w).mapWires
        (combineEmb (combineEmb (combineEmb eC eA hCA) eB (emb_disjoint_combineEmb hCA hCB hAB))
          eAnc (emb_disjoint_combineEmb (emb_disjoint_combineEmb hCA hCB hAB)
            (emb_disjoint_combineEmb hCA hCAnc hAAnc) hBAnc))).unitary (ket z) =
      ket (updateOn eB z (if z (eC 0) then natToBits w (bitsToNat (z ∘ eA) + bitsToNat (z ∘ eB)) else z ∘ eB)) := by
  let embM := combineEmb (combineEmb eC eA hCA) eB (emb_disjoint_combineEmb hCA hCB hAB)
  have hsub := arith.act_subReg_perm (arith.ctrlAddInPlaceMSBCircuit w) (ctrlAddInPlaceMSBFn w)
    (arith.ctrlAddInPlaceMSBCircuit_implements w) embM eAnc
    (emb_disjoint_combineEmb (emb_disjoint_combineEmb hCA hCB hAB)
      (emb_disjoint_combineEmb hCA hCAnc hAAnc) hBAnc) z (fun k => congrFun hzAnc k)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right (combineEmb eC eA hCA) eB (emb_disjoint_combineEmb hCA hCB hAB) z
    (ctrlAddInPlaceMSBFn w) ?_ _ ?_
  · intro x i
    dsimp only [ctrlAddInPlaceMSBFn]
    have hlt : ¬ (1 + w ≤ (Fin.castAdd w i : Fin (1 + w + w)).1) := by dsimp [Fin.castAdd]; exact Nat.not_le_of_lt i.isLt
    split_ifs <;> simp
  · intro j
    dsimp only [ctrlAddInPlaceMSBFn, Function.comp_apply]
    have hc0 : z (embM ⟨0, by omega⟩) = z (eC 0) := by
      change z (combineEmb (combineEmb eC eA hCA) eB _ (Fin.castAdd w (Fin.castAdd w 0))) = z (eC 0); simp
    have ha : (fun i : Fin w => z (combineEmb (combineEmb eC eA hCA) eB (emb_disjoint_combineEmb hCA hCB hAB) ⟨1 + i.1, by omega⟩)) = z ∘ eA := funext fun i => by
      change z (combineEmb (combineEmb eC eA hCA) eB _ (Fin.castAdd w (Fin.natAdd 1 i))) = z (eA i); simp
    have hb : (fun i : Fin w => z (combineEmb (combineEmb eC eA hCA) eB (emb_disjoint_combineEmb hCA hCB hAB) ⟨1 + w + i.1, by omega⟩)) = z ∘ eB := funext fun i => by
      change z (combineEmb (combineEmb eC eA hCA) eB _ (Fin.natAdd (1 + w) i)) = z (eB i); simp
    have hge : 1 + w ≤ (Fin.natAdd (1 + w) j : Fin (1 + w + w)).1 := by simp [Fin.natAdd]
    cases hx : z (eC 0)
    · rw [if_neg (by dsimp only [embM] at hc0; rw [hc0, hx]; decide), if_neg (by simp)]
      simp [combineEmb_natAdd]
    · rw [if_pos (by dsimp only [embM] at hc0; rw [hc0, hx]), if_pos (by simp), dif_pos hge, ha, hb]
      have hidx : (⟨(Fin.natAdd (1 + w) j : Fin (1 + w + w)).1 - (1 + w), by simp [Fin.natAdd]⟩ : Fin w) = j :=
        Fin.ext (by simp [Fin.natAdd])
      rw [hidx]

lemma act_ctrlSubInPlaceOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eC : Fin 1 ↪ Fin m) (eA eB : Fin w ↪ Fin m) (eAnc : Fin (w + 1) ↪ Fin m)
    (hCA : ∀ i j, eC i ≠ eA j) (hCB : ∀ i j, eC i ≠ eB j) (hAB : ∀ i j, eA i ≠ eB j)
    (hCAnc : ∀ i k, eC i ≠ eAnc k) (hAAnc : ∀ i k, eA i ≠ eAnc k) (hBAnc : ∀ i k, eB i ≠ eAnc k)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.ctrlSubInPlaceMSBCircuit w).mapWires
        (combineEmb (combineEmb (combineEmb eC eA hCA) eB (emb_disjoint_combineEmb hCA hCB hAB))
          eAnc (emb_disjoint_combineEmb (emb_disjoint_combineEmb hCA hCB hAB)
            (emb_disjoint_combineEmb hCA hCAnc hAAnc) hBAnc))).unitary (ket z) =
      ket (updateOn eB z (if z (eC 0) then natToBits w (2 ^ w + bitsToNat (z ∘ eB) - bitsToNat (z ∘ eA)) else z ∘ eB)) := by
  let embM := combineEmb (combineEmb eC eA hCA) eB (emb_disjoint_combineEmb hCA hCB hAB)
  have hsub := arith.act_subReg_perm (arith.ctrlSubInPlaceMSBCircuit w) (ctrlSubInPlaceMSBFn w)
    (arith.ctrlSubInPlaceMSBCircuit_implements w) embM eAnc
    (emb_disjoint_combineEmb (emb_disjoint_combineEmb hCA hCB hAB)
      (emb_disjoint_combineEmb hCA hCAnc hAAnc) hBAnc) z (fun k => congrFun hzAnc k)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right (combineEmb eC eA hCA) eB (emb_disjoint_combineEmb hCA hCB hAB) z
    (ctrlSubInPlaceMSBFn w) ?_ _ ?_
  · intro x i
    dsimp only [ctrlSubInPlaceMSBFn]
    have hlt : ¬ (1 + w ≤ (Fin.castAdd w i : Fin (1 + w + w)).1) := by dsimp [Fin.castAdd]; exact Nat.not_le_of_lt i.isLt
    split_ifs <;> simp
  · intro j
    dsimp only [ctrlSubInPlaceMSBFn, Function.comp_apply]
    have hc0 : z (embM ⟨0, by omega⟩) = z (eC 0) := by
      change z (combineEmb (combineEmb eC eA hCA) eB _ (Fin.castAdd w (Fin.castAdd w 0))) = z (eC 0); simp
    have ha : (fun i : Fin w => z (combineEmb (combineEmb eC eA hCA) eB (emb_disjoint_combineEmb hCA hCB hAB) ⟨1 + i.1, by omega⟩)) = z ∘ eA := funext fun i => by
      change z (combineEmb (combineEmb eC eA hCA) eB _ (Fin.castAdd w (Fin.natAdd 1 i))) = z (eA i); simp
    have hb : (fun i : Fin w => z (combineEmb (combineEmb eC eA hCA) eB (emb_disjoint_combineEmb hCA hCB hAB) ⟨1 + w + i.1, by omega⟩)) = z ∘ eB := funext fun i => by
      change z (combineEmb (combineEmb eC eA hCA) eB _ (Fin.natAdd (1 + w) i)) = z (eB i); simp
    have hge : 1 + w ≤ (Fin.natAdd (1 + w) j : Fin (1 + w + w)).1 := by simp [Fin.natAdd]
    cases hx : z (eC 0)
    · rw [if_neg (by dsimp only [embM] at hc0; rw [hc0, hx]; decide), if_neg (by simp)]
      simp [combineEmb_natAdd]
    · rw [if_pos (by dsimp only [embM] at hc0; rw [hc0, hx]), if_pos (by simp), dif_pos hge, ha, hb]
      have hidx : (⟨(Fin.natAdd (1 + w) j : Fin (1 + w + w)).1 - (1 + w), by simp [Fin.natAdd]⟩ : Fin w) = j :=
        Fin.ext (by simp [Fin.natAdd])
      rw [hidx]

lemma act_ctrlAddConstOn {w c m : ℕ} (arith : LcgSym54ArithV2)
    (eC : Fin 1 ↪ Fin m) (eB : Fin w ↪ Fin m) (eAnc : Fin (w + 1) ↪ Fin m)
    (hCB : ∀ i j, eC i ≠ eB j) (hCA : ∀ i k, eC i ≠ eAnc k) (hBA : ∀ j k, eB j ≠ eAnc k)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.ctrlAddConstInPlaceMSBCircuit w c).mapWires
        (combineEmb (combineEmb eC eB hCB) eAnc (emb_disjoint_combineEmb hCB hCA hBA))).unitary (ket z) =
      ket (updateOn eB z (if z (eC 0) then natToBits w (c % 2 ^ w + bitsToNat (z ∘ eB)) else z ∘ eB)) := by
  let embM := combineEmb eC eB hCB
  have hsub := arith.act_subReg_perm (arith.ctrlAddConstInPlaceMSBCircuit w c) (ctrlAddConstInPlaceMSBFn w c)
    (arith.ctrlAddConstInPlaceMSBCircuit_implements w c) embM eAnc
    (emb_disjoint_combineEmb hCB hCA hBA) z (fun k => congrFun hzAnc k)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eC eB hCB z (ctrlAddConstInPlaceMSBFn w c) ?_ _ ?_
  · intro x i
    have hi0 : i = 0 := Fin.ext (by omega); subst hi0
    dsimp only [ctrlAddConstInPlaceMSBFn]
    have hlt : ¬ (1 ≤ (Fin.castAdd w (0 : Fin 1) : Fin (1 + w)).1) := by simp
    split_ifs <;> simp
  · intro j
    dsimp only [ctrlAddConstInPlaceMSBFn, Function.comp_apply]
    have hc0 : z (embM ⟨0, by omega⟩) = z (eC 0) := by change z (combineEmb eC eB hCB (Fin.castAdd w 0)) = z (eC 0); simp
    have hb : (fun i : Fin w => z (combineEmb eC eB hCB ⟨1 + i.1, by omega⟩)) = z ∘ eB := funext fun i => by
      change z (combineEmb eC eB hCB (Fin.natAdd 1 i)) = z (eB i); simp
    have hge : 1 ≤ (Fin.natAdd 1 j : Fin (1 + w)).1 := by simp [Fin.natAdd]
    cases hx : z (eC 0)
    · rw [if_neg (by dsimp only [embM] at hc0; rw [hc0, hx]; decide), if_neg (by simp)]
      simp [combineEmb_natAdd]
    · rw [if_pos (by dsimp only [embM] at hc0; rw [hc0, hx]), if_pos (by simp), dif_pos hge, hb]
      have hidx : (⟨(Fin.natAdd 1 j : Fin (1 + w)).1 - 1, by simp [Fin.natAdd]⟩ : Fin w) = j :=
        Fin.ext (by simp [Fin.natAdd])
      rw [hidx]

/-! ### Part 3: Alonso–Schott Layout, Record Packing & State Snapshot -/

abbrev wT (d : ℕ) : ℕ := (d + (1 + d)) + (d + d)
abbrev wOut (d : ℕ) : ℕ := d + d
abbrev wB (d : ℕ) : ℕ := d + (d + d)

def oR (d : ℕ) : ℕ := arity d * d
def oC (d : ℕ) : ℕ := oR d + arity d * d
def oT (d : ℕ) : ℕ := oC d + arity d * d
def oOut (d : ℕ) : ℕ := oT d + arity d * wT d
def oB (d : ℕ) : ℕ := oOut d + arity d * wOut d
def oTr (d : ℕ) : ℕ := oB d + arity d * wB d
def oSA (d : ℕ) : ℕ := oTr d + sortTraceSize d
def oDR (d : ℕ) : ℕ := oSA d + (2 * d + 1)
def oFlag (d : ℕ) : ℕ := oDR d + d
def oTmp (d : ℕ) : ℕ := oFlag d + 1
def oPA (d : ℕ) : ℕ := oTmp d + d
def totAS (d : ℕ) : ℕ := oPA d + (d + 1)
def ancAS (d : ℕ) : ℕ := totAS d - arity d * d

lemma totAS_eq (d : ℕ) : arity d * d + ancAS d = totAS d := by
  dsimp only [ancAS, totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]
  omega

def eMain (d : ℕ) : Fin (arity d * d) ↪ Fin (totAS d) :=
  regEmb 0 (arity d) d (by dsimp [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)
def eR (d : ℕ) : Fin (arity d * d) ↪ Fin (totAS d) :=
  regEmb (oR d) (arity d) d (by dsimp [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)
def eC (d : ℕ) : Fin (arity d * d) ↪ Fin (totAS d) :=
  regEmb (oC d) (arity d) d (by dsimp [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC]; omega)
def eT (d : ℕ) : Fin (arity d * wT d) ↪ Fin (totAS d) :=
  regEmb (oT d) (arity d) (wT d) (by dsimp [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT]; omega)
def eOut (d : ℕ) : Fin (arity d * wOut d) ↪ Fin (totAS d) :=
  regEmb (oOut d) (arity d) (wOut d) (by dsimp [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut]; omega)
def eB (d : ℕ) : Fin (arity d * wB d) ↪ Fin (totAS d) :=
  regEmb (oB d) (arity d) (wB d) (by dsimp [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB]; omega)
def eTr (d : ℕ) : Fin (sortTraceSize d) ↪ Fin (totAS d) :=
  sliceEmb (oTr d) (sortTraceSize d) (by dsimp [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr]; omega)
def eSA (d : ℕ) : Fin (2 * d + 1) ↪ Fin (totAS d) :=
  sliceEmb (oSA d) (2 * d + 1) (by dsimp [totAS, oPA, oTmp, oFlag, oDR, oSA]; omega)
def eDR (d : ℕ) : Fin d ↪ Fin (totAS d) :=
  sliceEmb (oDR d) d (by dsimp [totAS, oPA, oTmp, oFlag, oDR]; omega)
def eFlag (d : ℕ) : Fin 1 ↪ Fin (totAS d) :=
  sliceEmb (oFlag d) 1 (by dsimp [totAS, oPA, oTmp, oFlag]; omega)
def eTmp (d : ℕ) : Fin d ↪ Fin (totAS d) :=
  sliceEmb (oTmp d) d (by dsimp [totAS, oPA, oTmp]; omega)
def ePA (d : ℕ) : Fin (d + 1) ↪ Fin (totAS d) :=
  sliceEmb (oPA d) (d + 1) (by dsimp [totAS]; omega)

@[ext] structure AsSnap (d : ℕ) where
  main : Fin (arity d) → Qubits d
  R : Fin (arity d) → Qubits d
  C : Fin (arity d) → Qubits d
  T : Fin (arity d) → Qubits (wT d)
  Out : Fin (arity d) → Qubits (wOut d)
  B : Fin (arity d) → Qubits (wB d)
  tr1 : Qubits (sortTraceSize d)
  sortAnc : Qubits (2 * d + 1)
  dR : Qubits d
  flagBit : Qubits 1
  tmpD : Qubits d
  primAnc : Qubits (d + 1)

def zeroSnap (d : ℕ) (main0 : Fin (arity d) → Qubits d) : AsSnap d where
  main := main0
  R := fun _ _ => false
  C := fun _ _ => false
  T := fun _ _ => false
  Out := fun _ _ => false
  B := fun _ _ => false
  tr1 := fun _ => false
  sortAnc := fun _ => false
  dR := fun _ => false
  flagBit := fun _ => false
  tmpD := fun _ => false
  primAnc := fun _ => false

def packAS (d : ℕ) (S : AsSnap d) : Qubits (totAS d) := fun k =>
  if h1 : k.1 < oR d then flatReg (arity d) d S.main ⟨k.1, h1⟩
  else if h2 : k.1 < oC d then flatReg (arity d) d S.R ⟨k.1 - oR d, by dsimp [oC] at h2; omega⟩
  else if h3 : k.1 < oT d then flatReg (arity d) d S.C ⟨k.1 - oC d, by dsimp [oT] at h3; omega⟩
  else if h4 : k.1 < oOut d then flatReg (arity d) (wT d) S.T ⟨k.1 - oT d, by dsimp [oOut] at h4; omega⟩
  else if h5 : k.1 < oB d then flatReg (arity d) (wOut d) S.Out ⟨k.1 - oOut d, by dsimp [oB] at h5; omega⟩
  else if h6 : k.1 < oTr d then flatReg (arity d) (wB d) S.B ⟨k.1 - oB d, by dsimp [oTr] at h6; omega⟩
  else if h7 : k.1 < oSA d then S.tr1 ⟨k.1 - oTr d, by dsimp [oSA] at h7; omega⟩
  else if h8 : k.1 < oDR d then S.sortAnc ⟨k.1 - oSA d, by dsimp [oDR] at h8; omega⟩
  else if h9 : k.1 < oFlag d then S.dR ⟨k.1 - oDR d, by dsimp [oFlag] at h9; omega⟩
  else if h10 : k.1 < oTmp d then S.flagBit ⟨k.1 - oFlag d, by dsimp [oTmp] at h10; omega⟩
  else if h11 : k.1 < oPA d then S.tmpD ⟨k.1 - oTmp d, by dsimp [oPA] at h11; omega⟩
  else S.primAnc ⟨k.1 - oPA d, by have := k.isLt; dsimp [totAS] at this; omega⟩

@[simp] lemma packAS_main (d : ℕ) (S : AsSnap d) : packAS d S ∘ eMain d = flatReg (arity d) d S.main := by
  funext i; have := i.isLt
  have h1 : (eMain d i).1 < oR d := by simp only [eMain, regEmb_apply, oR]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_pos h1]
  congr 1; apply Fin.ext; simp only [eMain, regEmb_apply]; omega

@[simp] lemma packAS_R (d : ℕ) (S : AsSnap d) : packAS d S ∘ eR d = flatReg (arity d) d S.R := by
  funext i; have := i.isLt
  have hn1 : ¬ (eR d i).1 < oR d := by simp only [eR, regEmb_apply]; omega
  have h2 : (eR d i).1 < oC d := by simp only [eR, regEmb_apply, oC]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_neg hn1, dif_pos h2]
  congr 1; apply Fin.ext; simp only [eR, regEmb_apply]; omega

@[simp] lemma packAS_C (d : ℕ) (S : AsSnap d) : packAS d S ∘ eC d = flatReg (arity d) d S.C := by
  funext i; have := i.isLt
  have hn1 : ¬ (eC d i).1 < oR d := by simp only [eC, regEmb_apply, oC]; omega
  have hn2 : ¬ (eC d i).1 < oC d := by simp only [eC, regEmb_apply]; omega
  have h3 : (eC d i).1 < oT d := by simp only [eC, regEmb_apply, oT]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_neg hn1, dif_neg hn2, dif_pos h3]
  congr 1; apply Fin.ext; simp only [eC, regEmb_apply]; omega

@[simp] lemma packAS_T (d : ℕ) (S : AsSnap d) : packAS d S ∘ eT d = flatReg (arity d) (wT d) S.T := by
  funext i; have := i.isLt
  have hn1 : ¬ (eT d i).1 < oR d := by simp only [eT, regEmb_apply, oT, oC]; omega
  have hn2 : ¬ (eT d i).1 < oC d := by simp only [eT, regEmb_apply, oT]; omega
  have hn3 : ¬ (eT d i).1 < oT d := by simp only [eT, regEmb_apply]; omega
  have h4 : (eT d i).1 < oOut d := by simp only [eT, regEmb_apply, oOut]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_neg hn1, dif_neg hn2, dif_neg hn3, dif_pos h4]
  congr 1; apply Fin.ext; simp only [eT, regEmb_apply]; omega

@[simp] lemma packAS_Out (d : ℕ) (S : AsSnap d) : packAS d S ∘ eOut d = flatReg (arity d) (wOut d) S.Out := by
  funext i; have := i.isLt
  have hn1 : ¬ (eOut d i).1 < oR d := by simp only [eOut, regEmb_apply, oOut, oT, oC]; omega
  have hn2 : ¬ (eOut d i).1 < oC d := by simp only [eOut, regEmb_apply, oOut, oT]; omega
  have hn3 : ¬ (eOut d i).1 < oT d := by simp only [eOut, regEmb_apply, oOut]; omega
  have hn4 : ¬ (eOut d i).1 < oOut d := by simp only [eOut, regEmb_apply]; omega
  have h5 : (eOut d i).1 < oB d := by simp only [eOut, regEmb_apply, oB]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_neg hn1, dif_neg hn2, dif_neg hn3, dif_neg hn4, dif_pos h5]
  congr 1; apply Fin.ext; simp only [eOut, regEmb_apply]; omega

@[simp] lemma packAS_B (d : ℕ) (S : AsSnap d) : packAS d S ∘ eB d = flatReg (arity d) (wB d) S.B := by
  funext i; have := i.isLt
  have hn1 : ¬ (eB d i).1 < oR d := by simp only [eB, regEmb_apply, oB, oOut, oT, oC]; omega
  have hn2 : ¬ (eB d i).1 < oC d := by simp only [eB, regEmb_apply, oB, oOut, oT]; omega
  have hn3 : ¬ (eB d i).1 < oT d := by simp only [eB, regEmb_apply, oB, oOut]; omega
  have hn4 : ¬ (eB d i).1 < oOut d := by simp only [eB, regEmb_apply, oB]; omega
  have hn5 : ¬ (eB d i).1 < oB d := by simp only [eB, regEmb_apply]; omega
  have h6 : (eB d i).1 < oTr d := by simp only [eB, regEmb_apply, oTr]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_neg hn1, dif_neg hn2, dif_neg hn3, dif_neg hn4, dif_neg hn5, dif_pos h6]
  congr 1; apply Fin.ext; simp only [eB, regEmb_apply]; omega

@[simp] lemma packAS_tr1 (d : ℕ) (S : AsSnap d) : packAS d S ∘ eTr d = S.tr1 := by
  funext i; have := i.isLt
  have hn1 : ¬ (eTr d i).1 < oR d := by simp only [eTr, sliceEmb_apply, oTr, oB, oOut, oT, oC]; omega
  have hn2 : ¬ (eTr d i).1 < oC d := by simp only [eTr, sliceEmb_apply, oTr, oB, oOut, oT]; omega
  have hn3 : ¬ (eTr d i).1 < oT d := by simp only [eTr, sliceEmb_apply, oTr, oB, oOut]; omega
  have hn4 : ¬ (eTr d i).1 < oOut d := by simp only [eTr, sliceEmb_apply, oTr, oB]; omega
  have hn5 : ¬ (eTr d i).1 < oB d := by simp only [eTr, sliceEmb_apply, oTr]; omega
  have hn6 : ¬ (eTr d i).1 < oTr d := by simp only [eTr, sliceEmb_apply]; omega
  have h7 : (eTr d i).1 < oSA d := by simp only [eTr, sliceEmb_apply, oSA]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_neg hn1, dif_neg hn2, dif_neg hn3, dif_neg hn4, dif_neg hn5, dif_neg hn6, dif_pos h7]
  congr 1; apply Fin.ext; simp only [eTr, sliceEmb_apply]; omega

@[simp] lemma packAS_sortAnc (d : ℕ) (S : AsSnap d) : packAS d S ∘ eSA d = S.sortAnc := by
  funext i; have := i.isLt
  have hn1 : ¬ (eSA d i).1 < oR d := by simp only [eSA, sliceEmb_apply, oSA, oTr, oB, oOut, oT, oC]; omega
  have hn2 : ¬ (eSA d i).1 < oC d := by simp only [eSA, sliceEmb_apply, oSA, oTr, oB, oOut, oT]; omega
  have hn3 : ¬ (eSA d i).1 < oT d := by simp only [eSA, sliceEmb_apply, oSA, oTr, oB, oOut]; omega
  have hn4 : ¬ (eSA d i).1 < oOut d := by simp only [eSA, sliceEmb_apply, oSA, oTr, oB]; omega
  have hn5 : ¬ (eSA d i).1 < oB d := by simp only [eSA, sliceEmb_apply, oSA, oTr]; omega
  have hn6 : ¬ (eSA d i).1 < oTr d := by simp only [eSA, sliceEmb_apply, oSA]; omega
  have hn7 : ¬ (eSA d i).1 < oSA d := by simp only [eSA, sliceEmb_apply]; omega
  have h8 : (eSA d i).1 < oDR d := by simp only [eSA, sliceEmb_apply, oDR]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_neg hn1, dif_neg hn2, dif_neg hn3, dif_neg hn4, dif_neg hn5, dif_neg hn6, dif_neg hn7, dif_pos h8]
  congr 1; apply Fin.ext; simp only [eSA, sliceEmb_apply]; omega

@[simp] lemma packAS_dR (d : ℕ) (S : AsSnap d) : packAS d S ∘ eDR d = S.dR := by
  funext i; have := i.isLt
  have hn1 : ¬ (eDR d i).1 < oR d := by simp only [eDR, sliceEmb_apply, oDR, oSA, oTr, oB, oOut, oT, oC]; omega
  have hn2 : ¬ (eDR d i).1 < oC d := by simp only [eDR, sliceEmb_apply, oDR, oSA, oTr, oB, oOut, oT]; omega
  have hn3 : ¬ (eDR d i).1 < oT d := by simp only [eDR, sliceEmb_apply, oDR, oSA, oTr, oB, oOut]; omega
  have hn4 : ¬ (eDR d i).1 < oOut d := by simp only [eDR, sliceEmb_apply, oDR, oSA, oTr, oB]; omega
  have hn5 : ¬ (eDR d i).1 < oB d := by simp only [eDR, sliceEmb_apply, oDR, oSA, oTr]; omega
  have hn6 : ¬ (eDR d i).1 < oTr d := by simp only [eDR, sliceEmb_apply, oDR, oSA]; omega
  have hn7 : ¬ (eDR d i).1 < oSA d := by simp only [eDR, sliceEmb_apply, oDR]; omega
  have hn8 : ¬ (eDR d i).1 < oDR d := by simp only [eDR, sliceEmb_apply]; omega
  have h9 : (eDR d i).1 < oFlag d := by simp only [eDR, sliceEmb_apply, oFlag]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_neg hn1, dif_neg hn2, dif_neg hn3, dif_neg hn4, dif_neg hn5, dif_neg hn6, dif_neg hn7, dif_neg hn8, dif_pos h9]
  congr 1; apply Fin.ext; simp only [eDR, sliceEmb_apply]; omega

@[simp] lemma packAS_flagBit (d : ℕ) (S : AsSnap d) : packAS d S ∘ eFlag d = S.flagBit := by
  funext i; have := i.isLt
  have hn1 : ¬ (eFlag d i).1 < oR d := by simp only [eFlag, sliceEmb_apply, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC]; omega
  have hn2 : ¬ (eFlag d i).1 < oC d := by simp only [eFlag, sliceEmb_apply, oFlag, oDR, oSA, oTr, oB, oOut, oT]; omega
  have hn3 : ¬ (eFlag d i).1 < oT d := by simp only [eFlag, sliceEmb_apply, oFlag, oDR, oSA, oTr, oB, oOut]; omega
  have hn4 : ¬ (eFlag d i).1 < oOut d := by simp only [eFlag, sliceEmb_apply, oFlag, oDR, oSA, oTr, oB]; omega
  have hn5 : ¬ (eFlag d i).1 < oB d := by simp only [eFlag, sliceEmb_apply, oFlag, oDR, oSA, oTr]; omega
  have hn6 : ¬ (eFlag d i).1 < oTr d := by simp only [eFlag, sliceEmb_apply, oFlag, oDR, oSA]; omega
  have hn7 : ¬ (eFlag d i).1 < oSA d := by simp only [eFlag, sliceEmb_apply, oFlag, oDR]; omega
  have hn8 : ¬ (eFlag d i).1 < oDR d := by simp only [eFlag, sliceEmb_apply, oFlag]; omega
  have hn9 : ¬ (eFlag d i).1 < oFlag d := by simp only [eFlag, sliceEmb_apply]; omega
  have h10 : (eFlag d i).1 < oTmp d := by simp only [eFlag, sliceEmb_apply, oTmp]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_neg hn1, dif_neg hn2, dif_neg hn3, dif_neg hn4, dif_neg hn5, dif_neg hn6, dif_neg hn7, dif_neg hn8, dif_neg hn9, dif_pos h10]
  congr 1; apply Fin.ext; simp only [eFlag, sliceEmb_apply]; omega

@[simp] lemma packAS_tmpD (d : ℕ) (S : AsSnap d) : packAS d S ∘ eTmp d = S.tmpD := by
  funext i; have := i.isLt
  have hn1 : ¬ (eTmp d i).1 < oR d := by simp only [eTmp, sliceEmb_apply, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC]; omega
  have hn2 : ¬ (eTmp d i).1 < oC d := by simp only [eTmp, sliceEmb_apply, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT]; omega
  have hn3 : ¬ (eTmp d i).1 < oT d := by simp only [eTmp, sliceEmb_apply, oTmp, oFlag, oDR, oSA, oTr, oB, oOut]; omega
  have hn4 : ¬ (eTmp d i).1 < oOut d := by simp only [eTmp, sliceEmb_apply, oTmp, oFlag, oDR, oSA, oTr, oB]; omega
  have hn5 : ¬ (eTmp d i).1 < oB d := by simp only [eTmp, sliceEmb_apply, oTmp, oFlag, oDR, oSA, oTr]; omega
  have hn6 : ¬ (eTmp d i).1 < oTr d := by simp only [eTmp, sliceEmb_apply, oTmp, oFlag, oDR, oSA]; omega
  have hn7 : ¬ (eTmp d i).1 < oSA d := by simp only [eTmp, sliceEmb_apply, oTmp, oFlag, oDR]; omega
  have hn8 : ¬ (eTmp d i).1 < oDR d := by simp only [eTmp, sliceEmb_apply, oTmp, oFlag]; omega
  have hn9 : ¬ (eTmp d i).1 < oFlag d := by simp only [eTmp, sliceEmb_apply, oTmp]; omega
  have hn10 : ¬ (eTmp d i).1 < oTmp d := by simp only [eTmp, sliceEmb_apply]; omega
  have h11 : (eTmp d i).1 < oPA d := by simp only [eTmp, sliceEmb_apply, oPA]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_neg hn1, dif_neg hn2, dif_neg hn3, dif_neg hn4, dif_neg hn5, dif_neg hn6, dif_neg hn7, dif_neg hn8, dif_neg hn9, dif_neg hn10, dif_pos h11]
  congr 1; apply Fin.ext; simp only [eTmp, sliceEmb_apply]; omega

@[simp] lemma packAS_primAnc (d : ℕ) (S : AsSnap d) : packAS d S ∘ ePA d = S.primAnc := by
  funext i; have := i.isLt
  have hn1 : ¬ (ePA d i).1 < oR d := by simp only [ePA, sliceEmb_apply, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC]; omega
  have hn2 : ¬ (ePA d i).1 < oC d := by simp only [ePA, sliceEmb_apply, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT]; omega
  have hn3 : ¬ (ePA d i).1 < oT d := by simp only [ePA, sliceEmb_apply, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut]; omega
  have hn4 : ¬ (ePA d i).1 < oOut d := by simp only [ePA, sliceEmb_apply, oPA, oTmp, oFlag, oDR, oSA, oTr, oB]; omega
  have hn5 : ¬ (ePA d i).1 < oB d := by simp only [ePA, sliceEmb_apply, oPA, oTmp, oFlag, oDR, oSA, oTr]; omega
  have hn6 : ¬ (ePA d i).1 < oTr d := by simp only [ePA, sliceEmb_apply, oPA, oTmp, oFlag, oDR, oSA]; omega
  have hn7 : ¬ (ePA d i).1 < oSA d := by simp only [ePA, sliceEmb_apply, oPA, oTmp, oFlag, oDR]; omega
  have hn8 : ¬ (ePA d i).1 < oDR d := by simp only [ePA, sliceEmb_apply, oPA, oTmp, oFlag]; omega
  have hn9 : ¬ (ePA d i).1 < oFlag d := by simp only [ePA, sliceEmb_apply, oPA, oTmp]; omega
  have hn10 : ¬ (ePA d i).1 < oTmp d := by simp only [ePA, sliceEmb_apply, oPA]; omega
  have hn11 : ¬ (ePA d i).1 < oPA d := by simp only [ePA, sliceEmb_apply]; omega
  dsimp only [Function.comp_apply, packAS]; rw [dif_neg hn1, dif_neg hn2, dif_neg hn3, dif_neg hn4, dif_neg hn5, dif_neg hn6, dif_neg hn7, dif_neg hn8, dif_neg hn9, dif_neg hn10, dif_neg hn11]
  congr 1; apply Fin.ext; simp only [ePA, sliceEmb_apply]; omega

lemma packAS_zeroSnap_eq_padZero (d : ℕ) (main0 : Fin (arity d) → Qubits d) :
    packAS d (zeroSnap d main0) =
      padZero (arity d * d) (ancAS d) (flatReg (arity d) d main0) ∘
        Fin.cast (totAS_eq d).symm := by
  funext k
  by_cases h1 : k.1 < oR d
  · have hlt : (Fin.cast (totAS_eq d).symm k).1 < arity d * d := by simpa [oR] using h1
    rw [Function.comp_apply, padZero_val_lt _ _ hlt]
    dsimp only [packAS]; rw [dif_pos h1]; rfl
  · have hge : arity d * d ≤ (Fin.cast (totAS_eq d).symm k).1 := by dsimp [oR] at h1; simpa using h1
    rw [Function.comp_apply, padZero_val_ge _ _ hge]
    dsimp only [packAS]; rw [dif_neg h1]
    by_cases h2 : k.1 < oC d
    · rw [dif_pos h2]; simp [zeroSnap, flatReg]
    · rw [dif_neg h2]
      by_cases h3 : k.1 < oT d
      · rw [dif_pos h3]; simp [zeroSnap, flatReg]
      · rw [dif_neg h3]
        by_cases h4 : k.1 < oOut d
        · rw [dif_pos h4]; simp [zeroSnap, flatReg]
        · rw [dif_neg h4]
          by_cases h5 : k.1 < oB d
          · rw [dif_pos h5]; simp [zeroSnap, flatReg]
          · rw [dif_neg h5]
            by_cases h6 : k.1 < oTr d
            · rw [dif_pos h6]; simp [zeroSnap, flatReg]
            · rw [dif_neg h6]
              by_cases h7 : k.1 < oSA d
              · rw [dif_pos h7]; rfl
              · rw [dif_neg h7]
                by_cases h8 : k.1 < oDR d
                · rw [dif_pos h8]; rfl
                · rw [dif_neg h8]
                  by_cases h9 : k.1 < oFlag d
                  · rw [dif_pos h9]; rfl
                  · rw [dif_neg h9]
                    by_cases h10 : k.1 < oTmp d
                    · rw [dif_pos h10]; rfl
                    · rw [dif_neg h10]
                      by_cases h11 : k.1 < oPA d
                      · rw [dif_pos h11]; rfl
                      · rw [dif_neg h11]; rfl

lemma as_funext {d : ℕ} {z1 z2 : Qubits (totAS d)}
    (h1 : z1 ∘ eMain d = z2 ∘ eMain d)
    (h2 : z1 ∘ eR d = z2 ∘ eR d)
    (h3 : z1 ∘ eC d = z2 ∘ eC d)
    (h4 : z1 ∘ eT d = z2 ∘ eT d)
    (h5 : z1 ∘ eOut d = z2 ∘ eOut d)
    (h6 : z1 ∘ eB d = z2 ∘ eB d)
    (h7 : z1 ∘ eTr d = z2 ∘ eTr d)
    (h8 : z1 ∘ eSA d = z2 ∘ eSA d)
    (h9 : z1 ∘ eDR d = z2 ∘ eDR d)
    (h10 : z1 ∘ eFlag d = z2 ∘ eFlag d)
    (h11 : z1 ∘ eTmp d = z2 ∘ eTmp d)
    (h12 : z1 ∘ ePA d = z2 ∘ ePA d) : z1 = z2 := by
  funext k
  by_cases c1 : k.1 < oR d
  · have := congrFun h1 ⟨k.1, c1⟩; simpa [eMain, regEmb] using this
  · by_cases c2 : k.1 < oC d
    · have := congrFun h2 ⟨k.1 - oR d, by dsimp [oC] at c2; omega⟩
      simpa [eR, regEmb, show oR d + (k.1 - oR d) = k.1 by omega] using this
    · by_cases c3 : k.1 < oT d
      · have := congrFun h3 ⟨k.1 - oC d, by dsimp [oT] at c3; omega⟩
        simpa [eC, regEmb, show oC d + (k.1 - oC d) = k.1 by omega] using this
      · by_cases c4 : k.1 < oOut d
        · have := congrFun h4 ⟨k.1 - oT d, by dsimp [oOut] at c4; omega⟩
          simpa [eT, regEmb, show oT d + (k.1 - oT d) = k.1 by omega] using this
        · by_cases c5 : k.1 < oB d
          · have := congrFun h5 ⟨k.1 - oOut d, by dsimp [oB] at c5; omega⟩
            simpa [eOut, regEmb, show oOut d + (k.1 - oOut d) = k.1 by omega] using this
          · by_cases c6 : k.1 < oTr d
            · have := congrFun h6 ⟨k.1 - oB d, by dsimp [oTr] at c6; omega⟩
              simpa [eB, regEmb, show oB d + (k.1 - oB d) = k.1 by omega] using this
            · by_cases c7 : k.1 < oSA d
              · have := congrFun h7 ⟨k.1 - oTr d, by dsimp [oSA] at c7; omega⟩
                simpa [eTr, show oTr d + (k.1 - oTr d) = k.1 by omega] using this
              · by_cases c8 : k.1 < oDR d
                · have := congrFun h8 ⟨k.1 - oSA d, by dsimp [oDR] at c8; omega⟩
                  simpa [eSA, show oSA d + (k.1 - oSA d) = k.1 by omega] using this
                · by_cases c9 : k.1 < oFlag d
                  · have := congrFun h9 ⟨k.1 - oDR d, by dsimp [oFlag] at c9; omega⟩
                    simpa [eDR, show oDR d + (k.1 - oDR d) = k.1 by omega] using this
                  · by_cases c10 : k.1 < oTmp d
                    · have := congrFun h10 ⟨k.1 - oFlag d, by dsimp [oTmp] at c10; omega⟩
                      simpa [eFlag, show oFlag d + (k.1 - oFlag d) = k.1 by omega] using this
                    · by_cases c11 : k.1 < oPA d
                      · have := congrFun h11 ⟨k.1 - oTmp d, by dsimp [oPA] at c11; omega⟩
                        simpa [eTmp, show oTmp d + (k.1 - oTmp d) = k.1 by omega] using this
                      · have := congrFun h12 ⟨k.1 - oPA d, by have := k.isLt; dsimp [totAS] at this; omega⟩
                        simpa [ePA, show oPA d + (k.1 - oPA d) = k.1 by omega] using this

lemma packAS_eq_of {d : ℕ} {z : Qubits (totAS d)} {S : AsSnap d}
    (h1 : z ∘ eMain d = flatReg (arity d) d S.main)
    (h2 : z ∘ eR d = flatReg (arity d) d S.R)
    (h3 : z ∘ eC d = flatReg (arity d) d S.C)
    (h4 : z ∘ eT d = flatReg (arity d) (wT d) S.T)
    (h5 : z ∘ eOut d = flatReg (arity d) (wOut d) S.Out)
    (h6 : z ∘ eB d = flatReg (arity d) (wB d) S.B)
    (h7 : z ∘ eTr d = S.tr1)
    (h8 : z ∘ eSA d = S.sortAnc)
    (h9 : z ∘ eDR d = S.dR)
    (h10 : z ∘ eFlag d = S.flagBit)
    (h11 : z ∘ eTmp d = S.tmpD)
    (h12 : z ∘ ePA d = S.primAnc) : z = packAS d S :=
  as_funext (by rw [h1, packAS_main]) (by rw [h2, packAS_R]) (by rw [h3, packAS_C])
    (by rw [h4, packAS_T]) (by rw [h5, packAS_Out]) (by rw [h6, packAS_B])
    (by rw [h7, packAS_tr1]) (by rw [h8, packAS_sortAnc]) (by rw [h9, packAS_dR])
    (by rw [h10, packAS_flagBit]) (by rw [h11, packAS_tmpD]) (by rw [h12, packAS_primAnc])

/-! ### Part 4: `InRange`, Slot & Field Embeddings, and Record Packing -/

def InRange {m k : ℕ} (lo hi : ℕ) (e : Fin k ↪ Fin m) : Prop :=
  ∀ i : Fin k, lo ≤ (e i).1 ∧ (e i).1 < hi

lemma inRange_trans {m k1 k2 lo hi : ℕ} (f : Fin k1 ↪ Fin k2) (e : Fin k2 ↪ Fin m)
    (he : InRange lo hi e) : InRange lo hi (f.trans e) :=
  fun i => he (f i)

lemma inRange_prefixRegEmb {m off N K w : ℕ} (h : off + N * w ≤ m) (hKN : K ≤ N) :
    InRange off (off + N * w) (prefixRegEmb h hKN) :=
  fun idx => ⟨by simp only [prefixRegEmb_mem_regEmb, regEmb_apply]; omega,
    by simp only [prefixRegEmb_mem_regEmb, regEmb_apply]; have := (finProdFinEquiv (Fin.castLE hKN (finProdFinEquiv.symm idx).1, (finProdFinEquiv.symm idx).2)).isLt; omega⟩

lemma inRange_mono {m k lo1 hi1 lo2 hi2 : ℕ} {e : Fin k ↪ Fin m}
    (h : InRange lo1 hi1 e) (hlo : lo2 ≤ lo1) (hhi : hi1 ≤ hi2) : InRange lo2 hi2 e :=
  fun i => ⟨le_trans hlo (h i).1, lt_of_lt_of_le (h i).2 hhi⟩

lemma inRange_combineEmb {m a b lo hi : ℕ} {ea : Fin a ↪ Fin m} {eb : Fin b ↪ Fin m}
    (hdisj : ∀ i j, ea i ≠ eb j) (ha : InRange lo hi ea) (hb : InRange lo hi eb) :
    InRange lo hi (combineEmb ea eb hdisj) := by
  intro u
  induction u using Fin.addCases with
  | left i => simpa using ha i
  | right j => simpa using hb j

lemma disjoint_of_inRange {m k1 k2 l1 h1 l2 h2 : ℕ} {e1 : Fin k1 ↪ Fin m} {e2 : Fin k2 ↪ Fin m}
    (he1 : InRange l1 h1 e1) (he2 : InRange l2 h2 e2) (hsep : h1 ≤ l2 ∨ h2 ≤ l1) :
    ∀ i j, e1 i ≠ e2 j := by
  intro i j hij
  have a1 := he1 i
  have a2 := he2 j
  have hv := congrArg Fin.val hij
  omega

lemma inRange_eMain (d : ℕ) : InRange 0 (oR d) (eMain d) :=
  fun i => ⟨Nat.zero_le _, by simp only [eMain, regEmb_apply, oR]; have := i.isLt; omega⟩
lemma inRange_eR (d : ℕ) : InRange (oR d) (oC d) (eR d) :=
  fun i => ⟨by simp only [eR, regEmb_apply]; omega, by simp only [eR, regEmb_apply, oC]; have := i.isLt; omega⟩
lemma inRange_eC (d : ℕ) : InRange (oC d) (oT d) (eC d) :=
  fun i => ⟨by simp only [eC, regEmb_apply]; omega, by simp only [eC, regEmb_apply, oT]; have := i.isLt; omega⟩
lemma inRange_eT (d : ℕ) : InRange (oT d) (oOut d) (eT d) :=
  fun i => ⟨by simp only [eT, regEmb_apply]; omega, by simp only [eT, regEmb_apply, oOut]; have := i.isLt; omega⟩
lemma inRange_eOut (d : ℕ) : InRange (oOut d) (oB d) (eOut d) :=
  fun i => ⟨by simp only [eOut, regEmb_apply]; omega, by simp only [eOut, regEmb_apply, oB]; have := i.isLt; omega⟩
lemma inRange_eB (d : ℕ) : InRange (oB d) (oTr d) (eB d) :=
  fun i => ⟨by simp only [eB, regEmb_apply]; omega, by simp only [eB, regEmb_apply, oTr]; have := i.isLt; omega⟩
lemma inRange_eTr (d : ℕ) : InRange (oTr d) (oSA d) (eTr d) :=
  fun i => ⟨by simp only [eTr, sliceEmb_apply]; omega, by simp only [eTr, sliceEmb_apply, oSA]; have := i.isLt; omega⟩
lemma inRange_eSA (d : ℕ) : InRange (oSA d) (oDR d) (eSA d) :=
  fun i => ⟨by simp only [eSA, sliceEmb_apply]; omega, by simp only [eSA, sliceEmb_apply, oDR]; have := i.isLt; omega⟩
lemma inRange_eDR (d : ℕ) : InRange (oDR d) (oFlag d) (eDR d) :=
  fun i => ⟨by simp only [eDR, sliceEmb_apply]; omega, by simp only [eDR, sliceEmb_apply, oFlag]; have := i.isLt; omega⟩
lemma inRange_eFlag (d : ℕ) : InRange (oFlag d) (oTmp d) (eFlag d) :=
  fun i => ⟨by simp only [eFlag, sliceEmb_apply]; omega, by simp only [eFlag, sliceEmb_apply, oTmp]; have := i.isLt; omega⟩
lemma inRange_eTmp (d : ℕ) : InRange (oTmp d) (oPA d) (eTmp d) :=
  fun i => ⟨by simp only [eTmp, sliceEmb_apply]; omega, by simp only [eTmp, sliceEmb_apply, oPA]; have := i.isLt; omega⟩
lemma inRange_ePA (d : ℕ) : InRange (oPA d) (totAS d) (ePA d) :=
  fun i => ⟨by simp only [ePA, sliceEmb_apply]; omega, by simp only [ePA, totAS]; have := i.isLt; omega⟩

def mainSlot (d : ℕ) (p : Fin (arity d)) : Fin d ↪ Fin (totAS d) :=
  (slotInReg (arity d) d p).trans (eMain d)
def rSlot (d : ℕ) (p : Fin (arity d)) : Fin d ↪ Fin (totAS d) :=
  (slotInReg (arity d) d p).trans (eR d)
def cSlot (d : ℕ) (p : Fin (arity d)) : Fin d ↪ Fin (totAS d) :=
  (slotInReg (arity d) d p).trans (eC d)
def tSlot (d : ℕ) (pos : Fin (arity d)) : Fin (wT d) ↪ Fin (totAS d) :=
  (slotInReg (arity d) (wT d) pos).trans (eT d)
def outSlot (d : ℕ) (pos : Fin (arity d)) : Fin (wOut d) ↪ Fin (totAS d) :=
  (slotInReg (arity d) (wOut d) pos).trans (eOut d)
def bSlot (d : ℕ) (pos : Fin (arity d)) : Fin (wB d) ↪ Fin (totAS d) :=
  (slotInReg (arity d) (wB d) pos).trans (eB d)

def fTK (d : ℕ) : Fin d ↪ Fin (wT d) := sliceEmb 0 d (by simp [wT]; omega)
def fTTag (d : ℕ) : Fin 1 ↪ Fin (wT d) := sliceEmb d 1 (by simp [wT]; omega)
def fTIdx (d : ℕ) : Fin d ↪ Fin (wT d) := sliceEmb (d + 1) d (by simp [wT]; omega)
def fTR (d : ℕ) : Fin d ↪ Fin (wT d) := sliceEmb (d + 1 + d) d (by simp [wT]; omega)
def fTC (d : ℕ) : Fin d ↪ Fin (wT d) := sliceEmb (d + 1 + d + d) d (by simp [wT]; omega)

def tKeyEmb (d : ℕ) (pos : Fin (arity d)) : Fin d ↪ Fin (totAS d) := (fTK d).trans (tSlot d pos)
def tTagEmb (d : ℕ) (pos : Fin (arity d)) : Fin 1 ↪ Fin (totAS d) := (fTTag d).trans (tSlot d pos)
def tIdxEmb (d : ℕ) (pos : Fin (arity d)) : Fin d ↪ Fin (totAS d) := (fTIdx d).trans (tSlot d pos)
def tREmb (d : ℕ) (pos : Fin (arity d)) : Fin d ↪ Fin (totAS d) := (fTR d).trans (tSlot d pos)
def tCEmb (d : ℕ) (pos : Fin (arity d)) : Fin d ↪ Fin (totAS d) := (fTC d).trans (tSlot d pos)

def fOutR (d : ℕ) : Fin d ↪ Fin (wOut d) := sliceEmb 0 d (by simp [wOut])
def fOutC (d : ℕ) : Fin d ↪ Fin (wOut d) := sliceEmb d d (by simp [wOut])

def outREmb (d : ℕ) (pos : Fin (arity d)) : Fin d ↪ Fin (totAS d) := (fOutR d).trans (outSlot d pos)
def outCEmb (d : ℕ) (pos : Fin (arity d)) : Fin d ↪ Fin (totAS d) := (fOutC d).trans (outSlot d pos)

def fBIdx (d : ℕ) : Fin d ↪ Fin (wB d) := sliceEmb 0 d (by dsimp [wB]; omega)
def fBR (d : ℕ) : Fin d ↪ Fin (wB d) := sliceEmb d d (by dsimp [wB]; omega)
def fBC (d : ℕ) : Fin d ↪ Fin (wB d) := sliceEmb (d + d) d (by dsimp [wB]; omega)

def bIdxEmb (d : ℕ) (pos : Fin (arity d)) : Fin d ↪ Fin (totAS d) := (fBIdx d).trans (bSlot d pos)
def bREmb (d : ℕ) (pos : Fin (arity d)) : Fin d ↪ Fin (totAS d) := (fBR d).trans (bSlot d pos)
def bCEmb (d : ℕ) (pos : Fin (arity d)) : Fin d ↪ Fin (totAS d) := (fBC d).trans (bSlot d pos)

@[simp] lemma packAS_slot_comp_main (d : ℕ) (S : AsSnap d) (p : Fin (arity d)) :
    packAS d S ∘ mainSlot d p = S.main p := by
  change (packAS d S ∘ eMain d) ∘ slotInReg (arity d) d p = S.main p; rw [packAS_main, flatReg_comp_slotInReg]

@[simp] lemma packAS_slot_comp_R (d : ℕ) (S : AsSnap d) (p : Fin (arity d)) :
    packAS d S ∘ rSlot d p = S.R p := by
  change (packAS d S ∘ eR d) ∘ slotInReg (arity d) d p = S.R p; rw [packAS_R, flatReg_comp_slotInReg]

@[simp] lemma packAS_slot_comp_C (d : ℕ) (S : AsSnap d) (p : Fin (arity d)) :
    packAS d S ∘ cSlot d p = S.C p := by
  change (packAS d S ∘ eC d) ∘ slotInReg (arity d) d p = S.C p; rw [packAS_C, flatReg_comp_slotInReg]

@[simp] lemma packAS_slot_comp_T (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) :
    packAS d S ∘ tSlot d pos = S.T pos := by
  change (packAS d S ∘ eT d) ∘ slotInReg (arity d) (wT d) pos = S.T pos; rw [packAS_T, flatReg_comp_slotInReg]

@[simp] lemma packAS_slot_comp_Out (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) :
    packAS d S ∘ outSlot d pos = S.Out pos := by
  change (packAS d S ∘ eOut d) ∘ slotInReg (arity d) (wOut d) pos = S.Out pos; rw [packAS_Out, flatReg_comp_slotInReg]

@[simp] lemma packAS_slot_comp_B (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) :
    packAS d S ∘ bSlot d pos = S.B pos := by
  change (packAS d S ∘ eB d) ∘ slotInReg (arity d) (wB d) pos = S.B pos; rw [packAS_B, flatReg_comp_slotInReg]

@[simp] lemma packAS_field_t (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) {l : ℕ} (f : Fin l ↪ Fin (wT d)) :
    packAS d S ∘ (f.trans (tSlot d pos)) = S.T pos ∘ f := by
  change (packAS d S ∘ tSlot d pos) ∘ f = _; rw [packAS_slot_comp_T]

@[simp] lemma packAS_field_out (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) {l : ℕ} (f : Fin l ↪ Fin (wOut d)) :
    packAS d S ∘ (f.trans (outSlot d pos)) = S.Out pos ∘ f := by
  change (packAS d S ∘ outSlot d pos) ∘ f = _; rw [packAS_slot_comp_Out]

@[simp] lemma packAS_field_b (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) {l : ℕ} (f : Fin l ↪ Fin (wB d)) :
    packAS d S ∘ (f.trans (bSlot d pos)) = S.B pos ∘ f := by
  change (packAS d S ∘ bSlot d pos) ∘ f = _; rw [packAS_slot_comp_B]

def tKeyPack (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx : Qubits d) : Qubits (d + (1 + d)) :=
  Fin.append kR (Fin.append tag idx)

def tRecPack (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) : Qubits (wT d) :=
  Fin.append (tKeyPack d kR tag idx) (Fin.append r c)

def outRecPack (d : ℕ) (r c : Qubits d) : Qubits (wOut d) := Fin.append r c

def bRecPack (d : ℕ) (idx r c : Qubits d) : Qubits (wB d) := Fin.append idx (Fin.append r c)

@[simp] lemma recKey54_tRecPack (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) :
    recKey54 (tRecPack d kR tag idx r c) = tKeyPack d kR tag idx := by
  funext i; simp [recKey54, tRecPack]

@[simp] lemma recPay54_tRecPack (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) :
    recPay54 (tRecPack d kR tag idx r c) = Fin.append r c := by
  funext i; simp [recPay54, tRecPack]

@[simp] lemma recKey54_bRecPack (d : ℕ) (idx r c : Qubits d) :
    recKey54 (bRecPack d idx r c) = idx := by
  funext i; simp [recKey54, bRecPack]

@[simp] lemma recPay54_bRecPack (d : ℕ) (idx r c : Qubits d) :
    recPay54 (bRecPack d idx r c) = Fin.append r c := by
  funext i; simp [recPay54, bRecPack]

@[simp] lemma tRecPack_comp_fTK (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) :
    tRecPack d kR tag idx r c ∘ fTK d = kR := by
  funext i
  have h : fTK d i = Fin.castAdd (d + d) (Fin.castAdd (1 + d) i) := Fin.ext (by simp [fTK])
  change Fin.append (Fin.append kR (Fin.append tag idx)) (Fin.append r c) (fTK d i) = kR i
  rw [h, Fin.append_left, Fin.append_left]

@[simp] lemma tRecPack_comp_fTTag (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) :
    tRecPack d kR tag idx r c ∘ fTTag d = tag := by
  funext i
  have h : fTTag d i = Fin.castAdd (d + d) (Fin.natAdd d (Fin.castAdd d i)) := Fin.ext (by simp [fTTag])
  change Fin.append (Fin.append kR (Fin.append tag idx)) (Fin.append r c) (fTTag d i) = tag i
  rw [h, Fin.append_left, Fin.append_right, Fin.append_left]

@[simp] lemma tRecPack_comp_fTIdx (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) :
    tRecPack d kR tag idx r c ∘ fTIdx d = idx := by
  funext i
  have h : fTIdx d i = Fin.castAdd (d + d) (Fin.natAdd d (Fin.natAdd 1 i)) := Fin.ext (by simp [fTIdx]; omega)
  change Fin.append (Fin.append kR (Fin.append tag idx)) (Fin.append r c) (fTIdx d i) = idx i
  rw [h, Fin.append_left, Fin.append_right, Fin.append_right]

@[simp] lemma tRecPack_comp_fTR (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) :
    tRecPack d kR tag idx r c ∘ fTR d = r := by
  funext i
  have h : fTR d i = Fin.natAdd (d + (1 + d)) (Fin.castAdd d i) := Fin.ext (by simp [fTR]; omega)
  change Fin.append (Fin.append kR (Fin.append tag idx)) (Fin.append r c) (fTR d i) = r i
  rw [h, Fin.append_right, Fin.append_left]

@[simp] lemma tRecPack_comp_fTC (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) :
    tRecPack d kR tag idx r c ∘ fTC d = c := by
  funext i
  have h : fTC d i = Fin.natAdd (d + (1 + d)) (Fin.natAdd d i) := Fin.ext (by simp [fTC]; omega)
  change Fin.append (Fin.append kR (Fin.append tag idx)) (Fin.append r c) (fTC d i) = c i
  rw [h, Fin.append_right, Fin.append_right]

@[simp] lemma tRecPack_apply_fTK (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) (j : Fin d) :
    tRecPack d kR tag idx r c (fTK d j) = kR j := congrFun (tRecPack_comp_fTK d kR tag idx r c) j

@[simp] lemma tRecPack_apply_fTTag (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) (j : Fin 1) :
    tRecPack d kR tag idx r c (fTTag d j) = tag j := congrFun (tRecPack_comp_fTTag d kR tag idx r c) j

@[simp] lemma tRecPack_apply_fTIdx (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) (j : Fin d) :
    tRecPack d kR tag idx r c (fTIdx d j) = idx j := congrFun (tRecPack_comp_fTIdx d kR tag idx r c) j

@[simp] lemma tRecPack_apply_fTR (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) (j : Fin d) :
    tRecPack d kR tag idx r c (fTR d j) = r j := congrFun (tRecPack_comp_fTR d kR tag idx r c) j

@[simp] lemma tRecPack_apply_fTC (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) (j : Fin d) :
    tRecPack d kR tag idx r c (fTC d j) = c j := congrFun (tRecPack_comp_fTC d kR tag idx r c) j

lemma tRecPack_ext {d : ℕ} {x y : Qubits (wT d)}
    (h1 : x ∘ fTK d = y ∘ fTK d) (h2 : x ∘ fTTag d = y ∘ fTTag d) (h3 : x ∘ fTIdx d = y ∘ fTIdx d)
    (h4 : x ∘ fTR d = y ∘ fTR d) (h5 : x ∘ fTC d = y ∘ fTC d) : x = y := by
  funext i
  by_cases c1 : i.1 < d
  · simpa [fTK] using congrFun h1 ⟨i.1, c1⟩
  · by_cases c2 : i.1 < d + 1
    · simpa [fTTag, show d + (i.1 - d) = i.1 by omega] using congrFun h2 ⟨i.1 - d, by omega⟩
    · by_cases c3 : i.1 < d + 1 + d
      · simpa [fTIdx, show d + 1 + (i.1 - (d + 1)) = i.1 by omega] using congrFun h3 ⟨i.1 - (d + 1), by omega⟩
      · by_cases c4 : i.1 < d + 1 + d + d
        · simpa [fTR, show d + 1 + d + (i.1 - (d + 1 + d)) = i.1 by omega] using congrFun h4 ⟨i.1 - (d + 1 + d), by omega⟩
        · have hi := i.isLt
          dsimp only [wT] at hi
          simpa [fTC, show d + 1 + d + d + (i.1 - (d + 1 + d + d)) = i.1 by omega] using
            congrFun h5 ⟨i.1 - (d + 1 + d + d), by omega⟩

@[simp] lemma update_fTK (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c kR' : Qubits d) :
    updateOn (fTK d) (tRecPack d kR tag idx r c) kR' = tRecPack d kR' tag idx r c := by
  refine tRecPack_ext ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_self', tRecPack_comp_fTK]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTK, fTTag]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTTag, tRecPack_comp_fTTag]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTK, fTIdx]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTIdx, tRecPack_comp_fTIdx]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTK, fTR]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTR, tRecPack_comp_fTR]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTK, fTC]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTC, tRecPack_comp_fTC]

@[simp] lemma update_fTTag (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c : Qubits d) (tag' : Qubits 1) :
    updateOn (fTTag d) (tRecPack d kR tag idx r c) tag' = tRecPack d kR tag' idx r c := by
  refine tRecPack_ext ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTTag, fTK]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTK, tRecPack_comp_fTK]
  · rw [updateOn_comp_self', tRecPack_comp_fTTag]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTTag, fTIdx]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTIdx, tRecPack_comp_fTIdx]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTTag, fTR]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTR, tRecPack_comp_fTR]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTTag, fTC]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTC, tRecPack_comp_fTC]

@[simp] lemma update_fTIdx (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c idx' : Qubits d) :
    updateOn (fTIdx d) (tRecPack d kR tag idx r c) idx' = tRecPack d kR tag idx' r c := by
  refine tRecPack_ext ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTIdx, fTK]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTK, tRecPack_comp_fTK]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTIdx, fTTag]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTTag, tRecPack_comp_fTTag]
  · rw [updateOn_comp_self', tRecPack_comp_fTIdx]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTIdx, fTR]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTR, tRecPack_comp_fTR]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTIdx, fTC]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTC, tRecPack_comp_fTC]

@[simp] lemma update_fTR (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c r' : Qubits d) :
    updateOn (fTR d) (tRecPack d kR tag idx r c) r' = tRecPack d kR tag idx r' c := by
  refine tRecPack_ext ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTR, fTK]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTK, tRecPack_comp_fTK]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTR, fTTag]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTTag, tRecPack_comp_fTTag]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTR, fTIdx]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTIdx, tRecPack_comp_fTIdx]
  · rw [updateOn_comp_self', tRecPack_comp_fTR]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTR, fTC]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTC, tRecPack_comp_fTC]

@[simp] lemma update_fTC (d : ℕ) (kR : Qubits d) (tag : Qubits 1) (idx r c c' : Qubits d) :
    updateOn (fTC d) (tRecPack d kR tag idx r c) c' = tRecPack d kR tag idx r c' := by
  refine tRecPack_ext ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTC, fTK]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTK, tRecPack_comp_fTK]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTC, fTTag]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTTag, tRecPack_comp_fTTag]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTC, fTIdx]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTIdx, tRecPack_comp_fTIdx]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fTC, fTR]; exact sliceEmb_disjoint _ _ (by omega)), tRecPack_comp_fTR, tRecPack_comp_fTR]
  · rw [updateOn_comp_self', tRecPack_comp_fTC]

lemma tRecPack_zero (d : ℕ) :
    tRecPack d (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) =
      fun _ => false := by
  refine tRecPack_ext ?_ ?_ ?_ ?_ ?_ <;> simp

@[simp] lemma outRecPack_comp_fOutR (d : ℕ) (r c : Qubits d) : outRecPack d r c ∘ fOutR d = r := by
  funext i
  have h : fOutR d i = Fin.castAdd d i := Fin.ext (Nat.zero_add i.1)
  change Fin.append r c (fOutR d i) = r i; rw [h, Fin.append_left]

@[simp] lemma outRecPack_comp_fOutC (d : ℕ) (r c : Qubits d) : outRecPack d r c ∘ fOutC d = c := by
  funext i
  have h : fOutC d i = Fin.natAdd d i := Fin.ext rfl
  change Fin.append r c (fOutC d i) = c i; rw [h, Fin.append_right]

@[simp] lemma outRecPack_apply_fOutR (d : ℕ) (r c : Qubits d) (j : Fin d) :
    outRecPack d r c (fOutR d j) = r j := congrFun (outRecPack_comp_fOutR d r c) j

@[simp] lemma outRecPack_apply_fOutC (d : ℕ) (r c : Qubits d) (j : Fin d) :
    outRecPack d r c (fOutC d j) = c j := congrFun (outRecPack_comp_fOutC d r c) j

lemma outRecPack_ext {d : ℕ} {x y : Qubits (wOut d)}
    (h1 : x ∘ fOutR d = y ∘ fOutR d) (h2 : x ∘ fOutC d = y ∘ fOutC d) : x = y := by
  funext i
  by_cases hi : i.1 < d
  · have he : fOutR d ⟨i.1, hi⟩ = i := Fin.ext (Nat.zero_add i.1)
    rw [← he]; exact congrFun h1 ⟨i.1, hi⟩
  · have hlt := i.isLt
    dsimp only [wOut] at hlt
    have he : fOutC d ⟨i.1 - d, by omega⟩ = i := Fin.ext (by change d + (i.1 - d) = i.1; omega)
    rw [← he]; exact congrFun h2 ⟨i.1 - d, by omega⟩

@[simp] lemma update_fOutR (d : ℕ) (r c r' : Qubits d) :
    updateOn (fOutR d) (outRecPack d r c) r' = outRecPack d r' c := by
  refine outRecPack_ext ?_ ?_
  · rw [updateOn_comp_self', outRecPack_comp_fOutR]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fOutR, fOutC]; exact sliceEmb_disjoint _ _ (by omega)), outRecPack_comp_fOutC, outRecPack_comp_fOutC]

@[simp] lemma update_fOutC (d : ℕ) (r c c' : Qubits d) :
    updateOn (fOutC d) (outRecPack d r c) c' = outRecPack d r c' := by
  refine outRecPack_ext ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fOutC, fOutR]; exact sliceEmb_disjoint _ _ (by omega)), outRecPack_comp_fOutR, outRecPack_comp_fOutR]
  · rw [updateOn_comp_self', outRecPack_comp_fOutC]

lemma outRecPack_zero (d : ℕ) : outRecPack d (fun _ => false) (fun _ => false) = fun _ => false := by
  refine outRecPack_ext ?_ ?_ <;> simp

@[simp] lemma bRecPack_comp_fBIdx (d : ℕ) (idx r c : Qubits d) : bRecPack d idx r c ∘ fBIdx d = idx := by
  funext i
  have h : fBIdx d i = Fin.castAdd (d + d) i := Fin.ext (by simp [fBIdx])
  change Fin.append idx (Fin.append r c) (fBIdx d i) = idx i; rw [h, Fin.append_left]

@[simp] lemma bRecPack_comp_fBR (d : ℕ) (idx r c : Qubits d) : bRecPack d idx r c ∘ fBR d = r := by
  funext i
  have h : fBR d i = Fin.natAdd d (Fin.castAdd d i) := Fin.ext (by simp [fBR])
  change Fin.append idx (Fin.append r c) (fBR d i) = r i; rw [h, Fin.append_right, Fin.append_left]

@[simp] lemma bRecPack_comp_fBC (d : ℕ) (idx r c : Qubits d) : bRecPack d idx r c ∘ fBC d = c := by
  funext i
  have h : fBC d i = Fin.natAdd d (Fin.natAdd d i) := Fin.ext (by simp [fBC]; omega)
  change Fin.append idx (Fin.append r c) (fBC d i) = c i; rw [h, Fin.append_right, Fin.append_right]

@[simp] lemma bRecPack_apply_fBIdx (d : ℕ) (idx r c : Qubits d) (j : Fin d) :
    bRecPack d idx r c (fBIdx d j) = idx j := congrFun (bRecPack_comp_fBIdx d idx r c) j

@[simp] lemma bRecPack_apply_fBR (d : ℕ) (idx r c : Qubits d) (j : Fin d) :
    bRecPack d idx r c (fBR d j) = r j := congrFun (bRecPack_comp_fBR d idx r c) j

@[simp] lemma bRecPack_apply_fBC (d : ℕ) (idx r c : Qubits d) (j : Fin d) :
    bRecPack d idx r c (fBC d j) = c j := congrFun (bRecPack_comp_fBC d idx r c) j

lemma bRecPack_ext {d : ℕ} {x y : Qubits (wB d)}
    (h1 : x ∘ fBIdx d = y ∘ fBIdx d) (h2 : x ∘ fBR d = y ∘ fBR d) (h3 : x ∘ fBC d = y ∘ fBC d) : x = y := by
  funext i
  by_cases c1 : i.1 < d
  · simpa [fBIdx] using congrFun h1 ⟨i.1, c1⟩
  · by_cases c2 : i.1 < d + d
    · simpa [fBR, show d + (i.1 - d) = i.1 by omega] using congrFun h2 ⟨i.1 - d, by omega⟩
    · have hi := i.isLt
      dsimp only [wB] at hi
      simpa [fBC, show d + d + (i.1 - (d + d)) = i.1 by omega] using congrFun h3 ⟨i.1 - (d + d), by omega⟩

@[simp] lemma update_fBIdx (d : ℕ) (idx r c idx' : Qubits d) :
    updateOn (fBIdx d) (bRecPack d idx r c) idx' = bRecPack d idx' r c := by
  refine bRecPack_ext ?_ ?_ ?_
  · rw [updateOn_comp_self', bRecPack_comp_fBIdx]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fBIdx, fBR]; exact sliceEmb_disjoint _ _ (by omega)), bRecPack_comp_fBR, bRecPack_comp_fBR]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fBIdx, fBC]; exact sliceEmb_disjoint _ _ (by omega)), bRecPack_comp_fBC, bRecPack_comp_fBC]

@[simp] lemma update_fBR (d : ℕ) (idx r c r' : Qubits d) :
    updateOn (fBR d) (bRecPack d idx r c) r' = bRecPack d idx r' c := by
  refine bRecPack_ext ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fBR, fBIdx]; exact sliceEmb_disjoint _ _ (by omega)), bRecPack_comp_fBIdx, bRecPack_comp_fBIdx]
  · rw [updateOn_comp_self', bRecPack_comp_fBR]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fBR, fBC]; exact sliceEmb_disjoint _ _ (by omega)), bRecPack_comp_fBC, bRecPack_comp_fBC]

@[simp] lemma update_fBC (d : ℕ) (idx r c c' : Qubits d) :
    updateOn (fBC d) (bRecPack d idx r c) c' = bRecPack d idx r c' := by
  refine bRecPack_ext ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fBC, fBIdx]; exact sliceEmb_disjoint _ _ (by omega)), bRecPack_comp_fBIdx, bRecPack_comp_fBIdx]
  · rw [updateOn_comp_disjoint _ _ (by dsimp only [fBC, fBR]; exact sliceEmb_disjoint _ _ (by omega)), bRecPack_comp_fBR, bRecPack_comp_fBR]
  · rw [updateOn_comp_self', bRecPack_comp_fBC]

lemma bRecPack_zero (d : ℕ) : bRecPack d (fun _ => false) (fun _ => false) (fun _ => false) = fun _ => false := by
  refine bRecPack_ext ?_ ?_ ?_ <;> simp

/-! ### Part 5: Snapshot Update Lemmas, `InRange` Instances, and `prepTtilde0` / `Sort 1` / `fwdScan` -/

lemma inRange_mainSlot (d : ℕ) (p : Fin (arity d)) : InRange 0 (oR d) (mainSlot d p) :=
  inRange_trans _ _ (inRange_eMain d)
lemma inRange_rSlot (d : ℕ) (p : Fin (arity d)) : InRange (oR d) (oC d) (rSlot d p) :=
  inRange_trans _ _ (inRange_eR d)
lemma inRange_cSlot (d : ℕ) (p : Fin (arity d)) : InRange (oC d) (oT d) (cSlot d p) :=
  inRange_trans _ _ (inRange_eC d)
lemma inRange_tSlot (d : ℕ) (pos : Fin (arity d)) : InRange (oT d) (oOut d) (tSlot d pos) :=
  inRange_trans _ _ (inRange_eT d)
lemma inRange_outSlot (d : ℕ) (pos : Fin (arity d)) : InRange (oOut d) (oB d) (outSlot d pos) :=
  inRange_trans _ _ (inRange_eOut d)
lemma inRange_bSlot (d : ℕ) (pos : Fin (arity d)) : InRange (oB d) (oTr d) (bSlot d pos) :=
  inRange_trans _ _ (inRange_eB d)
lemma inRange_tField (d : ℕ) (pos : Fin (arity d)) {l : ℕ} (f : Fin l ↪ Fin (wT d)) :
    InRange (oT d) (oOut d) (f.trans (tSlot d pos)) :=
  inRange_trans _ _ (inRange_tSlot d pos)
lemma inRange_outField (d : ℕ) (pos : Fin (arity d)) {l : ℕ} (f : Fin l ↪ Fin (wOut d)) :
    InRange (oOut d) (oB d) (f.trans (outSlot d pos)) :=
  inRange_trans _ _ (inRange_outSlot d pos)
lemma inRange_bField (d : ℕ) (pos : Fin (arity d)) {l : ℕ} (f : Fin l ↪ Fin (wB d)) :
    InRange (oB d) (oTr d) (f.trans (bSlot d pos)) :=
  inRange_trans _ _ (inRange_bSlot d pos)

lemma inRange_tKeyEmb (d : ℕ) (p : Fin (arity d)) : InRange (oT d) (oOut d) (tKeyEmb d p) := inRange_tField d p _
lemma inRange_tTagEmb (d : ℕ) (p : Fin (arity d)) : InRange (oT d) (oOut d) (tTagEmb d p) := inRange_tField d p _
lemma inRange_tIdxEmb (d : ℕ) (p : Fin (arity d)) : InRange (oT d) (oOut d) (tIdxEmb d p) := inRange_tField d p _
lemma inRange_tREmb (d : ℕ) (p : Fin (arity d)) : InRange (oT d) (oOut d) (tREmb d p) := inRange_tField d p _
lemma inRange_tCEmb (d : ℕ) (p : Fin (arity d)) : InRange (oT d) (oOut d) (tCEmb d p) := inRange_tField d p _
lemma inRange_outREmb (d : ℕ) (p : Fin (arity d)) : InRange (oOut d) (oB d) (outREmb d p) := inRange_outField d p _
lemma inRange_outCEmb (d : ℕ) (p : Fin (arity d)) : InRange (oOut d) (oB d) (outCEmb d p) := inRange_outField d p _
lemma inRange_bIdxEmb (d : ℕ) (p : Fin (arity d)) : InRange (oB d) (oTr d) (bIdxEmb d p) := inRange_bField d p _
lemma inRange_bREmb (d : ℕ) (p : Fin (arity d)) : InRange (oB d) (oTr d) (bREmb d p) := inRange_bField d p _
lemma inRange_bCEmb (d : ℕ) (p : Fin (arity d)) : InRange (oB d) (oTr d) (bCEmb d p) := inRange_bField d p _

class HasInRange {m k : ℕ} (e : Fin k ↪ Fin m) (lo hi : outParam ℕ) : Prop where
  inRange : InRange lo hi e

instance (d : ℕ) (p : Fin (arity d)) : HasInRange (mainSlot d p) 0 (oR d) := ⟨inRange_mainSlot d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (rSlot d p) (oR d) (oC d) := ⟨inRange_rSlot d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (cSlot d p) (oC d) (oT d) := ⟨inRange_cSlot d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (tSlot d p) (oT d) (oOut d) := ⟨inRange_tSlot d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (outSlot d p) (oOut d) (oB d) := ⟨inRange_outSlot d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (bSlot d p) (oB d) (oTr d) := ⟨inRange_bSlot d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (tKeyEmb d p) (oT d) (oOut d) := ⟨inRange_tKeyEmb d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (tTagEmb d p) (oT d) (oOut d) := ⟨inRange_tTagEmb d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (tIdxEmb d p) (oT d) (oOut d) := ⟨inRange_tIdxEmb d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (tREmb d p) (oT d) (oOut d) := ⟨inRange_tREmb d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (tCEmb d p) (oT d) (oOut d) := ⟨inRange_tCEmb d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (outREmb d p) (oOut d) (oB d) := ⟨inRange_outREmb d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (outCEmb d p) (oOut d) (oB d) := ⟨inRange_outCEmb d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (bIdxEmb d p) (oB d) (oTr d) := ⟨inRange_bIdxEmb d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (bREmb d p) (oB d) (oTr d) := ⟨inRange_bREmb d p⟩
instance (d : ℕ) (p : Fin (arity d)) : HasInRange (bCEmb d p) (oB d) (oTr d) := ⟨inRange_bCEmb d p⟩
instance (d : ℕ) : HasInRange (eMain d) 0 (oR d) := ⟨inRange_eMain d⟩
instance (d : ℕ) : HasInRange (eR d) (oR d) (oC d) := ⟨inRange_eR d⟩
instance (d : ℕ) : HasInRange (eC d) (oC d) (oT d) := ⟨inRange_eC d⟩
instance (d : ℕ) : HasInRange (eT d) (oT d) (oOut d) := ⟨inRange_eT d⟩
instance (d : ℕ) : HasInRange (eOut d) (oOut d) (oB d) := ⟨inRange_eOut d⟩
instance (d : ℕ) : HasInRange (eB d) (oB d) (oTr d) := ⟨inRange_eB d⟩
instance (d : ℕ) : HasInRange (eTr d) (oTr d) (oSA d) := ⟨inRange_eTr d⟩
instance (d : ℕ) : HasInRange (eSA d) (oSA d) (oDR d) := ⟨inRange_eSA d⟩
instance (d : ℕ) : HasInRange (eDR d) (oDR d) (oFlag d) := ⟨inRange_eDR d⟩
instance (d : ℕ) : HasInRange (eFlag d) (oFlag d) (oTmp d) := ⟨inRange_eFlag d⟩
instance (d : ℕ) : HasInRange (eTmp d) (oTmp d) (oPA d) := ⟨inRange_eTmp d⟩
instance (d : ℕ) : HasInRange (ePA d) (oPA d) (totAS d) := ⟨inRange_ePA d⟩
instance {m k1 k2 lo hi : ℕ} (f : Fin k1 ↪ Fin k2) (e : Fin k2 ↪ Fin m) [h : HasInRange e lo hi] :
    HasInRange (f.trans e) lo hi := ⟨inRange_trans f e h.inRange⟩
lemma inRange_regEmb {m off N w : ℕ} (h : off + N * w ≤ m) :
    InRange off (off + N * w) (regEmb off N w h) := by
  intro idx
  have := idx.isLt
  simp only [regEmb_apply]
  omega

instance {m off N w : ℕ} (h : off + N * w ≤ m) :
    HasInRange (regEmb off N w h) off (off + N * w) := ⟨inRange_regEmb h⟩

instance {m off N K w : ℕ} (h : off + N * w ≤ m) (hKN : K ≤ N) :
    HasInRange (prefixRegEmb h hKN) off (off + N * w) := ⟨inRange_prefixRegEmb h hKN⟩

lemma sep_of {m k1 k2 l1 h1 l2 h2 : ℕ} (e1 : Fin k1 ↪ Fin m) (e2 : Fin k2 ↪ Fin m)
    [h1i : HasInRange e1 l1 h1] [h2i : HasInRange e2 l2 h2]
    (hsep : h1 ≤ l2 ∨ h2 ≤ l1) : ∀ i j, e1 i ≠ e2 j :=
  disjoint_of_inRange h1i.inRange h2i.inRange hsep

@[simp] lemma packAS_slot_apply_main (d : ℕ) (S : AsSnap d) (p : Fin (arity d)) (j : Fin d) :
    packAS d S (mainSlot d p j) = S.main p j := congrFun (packAS_slot_comp_main d S p) j
@[simp] lemma packAS_slot_apply_R (d : ℕ) (S : AsSnap d) (p : Fin (arity d)) (j : Fin d) :
    packAS d S (rSlot d p j) = S.R p j := congrFun (packAS_slot_comp_R d S p) j
@[simp] lemma packAS_slot_apply_C (d : ℕ) (S : AsSnap d) (p : Fin (arity d)) (j : Fin d) :
    packAS d S (cSlot d p j) = S.C p j := congrFun (packAS_slot_comp_C d S p) j
@[simp] lemma packAS_field_t_apply (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) {l : ℕ}
    (f : Fin l ↪ Fin (wT d)) (j : Fin l) :
    packAS d S ((f.trans (tSlot d pos)) j) = S.T pos (f j) := congrFun (packAS_field_t d S pos f) j
@[simp] lemma packAS_field_out_apply (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) {l : ℕ}
    (f : Fin l ↪ Fin (wOut d)) (j : Fin l) :
    packAS d S ((f.trans (outSlot d pos)) j) = S.Out pos (f j) := congrFun (packAS_field_out d S pos f) j
@[simp] lemma packAS_field_b_apply (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) {l : ℕ}
    (f : Fin l ↪ Fin (wB d)) (j : Fin l) :
    packAS d S ((f.trans (bSlot d pos)) j) = S.B pos (f j) := congrFun (packAS_field_b d S pos f) j
@[simp] lemma packAS_dR_apply (d : ℕ) (S : AsSnap d) (j : Fin d) :
    packAS d S (eDR d j) = S.dR j := congrFun (packAS_dR d S) j
@[simp] lemma packAS_tmpD_apply (d : ℕ) (S : AsSnap d) (j : Fin d) :
    packAS d S (eTmp d j) = S.tmpD j := congrFun (packAS_tmpD d S) j
@[simp] lemma packAS_flagBit_apply (d : ℕ) (S : AsSnap d) (j : Fin 1) :
    packAS d S (eFlag d j) = S.flagBit j := congrFun (packAS_flagBit d S) j

lemma updateOn_mainSlot (d : ℕ) (S : AsSnap d) (p : Fin (arity d)) (val : Qubits d) :
    updateOn (mainSlot d p) (packAS d S) val =
      packAS d { S with main := Function.update S.main p val } := by
  refine packAS_eq_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact updateOn_slotEmb_comp_regEmb _ (packAS d S) S.main (packAS_main d S) p val
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_R]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_C]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_T]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_Out]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_B]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tr1]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_sortAnc]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_dR]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_flagBit]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tmpD]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_primAnc]

lemma updateOn_rSlot (d : ℕ) (S : AsSnap d) (p : Fin (arity d)) (val : Qubits d) :
    updateOn (rSlot d p) (packAS d S) val =
      packAS d { S with R := Function.update S.R p val } := by
  refine packAS_eq_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_main]
  · exact updateOn_slotEmb_comp_regEmb _ (packAS d S) S.R (packAS_R d S) p val
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_C]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_T]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_Out]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_B]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tr1]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_sortAnc]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_dR]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_flagBit]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tmpD]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_primAnc]

lemma updateOn_cSlot (d : ℕ) (S : AsSnap d) (p : Fin (arity d)) (val : Qubits d) :
    updateOn (cSlot d p) (packAS d S) val =
      packAS d { S with C := Function.update S.C p val } := by
  refine packAS_eq_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_main]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_R]
  · exact updateOn_slotEmb_comp_regEmb _ (packAS d S) S.C (packAS_C d S) p val
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_T]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_Out]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_B]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tr1]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_sortAnc]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_dR]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_flagBit]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tmpD]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_primAnc]

lemma updateOn_tField (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) {l : ℕ}
    (f : Fin l ↪ Fin (wT d)) (val : Qubits l) :
    updateOn (f.trans (tSlot d pos)) (packAS d S) val =
      packAS d { S with T := Function.update S.T pos (updateOn f (S.T pos) val) } := by
  refine packAS_eq_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_main]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_R]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_C]
  · exact updateOn_trans_slotEmb_comp_regEmb _ f (packAS d S) S.T (packAS_T d S) pos val
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_Out]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_B]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tr1]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_sortAnc]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_dR]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_flagBit]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tmpD]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_primAnc]

lemma updateOn_outField (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) {l : ℕ}
    (f : Fin l ↪ Fin (wOut d)) (val : Qubits l) :
    updateOn (f.trans (outSlot d pos)) (packAS d S) val =
      packAS d { S with Out := Function.update S.Out pos (updateOn f (S.Out pos) val) } := by
  refine packAS_eq_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_main]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_R]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_C]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_T]
  · exact updateOn_trans_slotEmb_comp_regEmb _ f (packAS d S) S.Out (packAS_Out d S) pos val
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_B]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tr1]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_sortAnc]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_dR]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_flagBit]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tmpD]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_primAnc]

lemma updateOn_bField (d : ℕ) (S : AsSnap d) (pos : Fin (arity d)) {l : ℕ}
    (f : Fin l ↪ Fin (wB d)) (val : Qubits l) :
    updateOn (f.trans (bSlot d pos)) (packAS d S) val =
      packAS d { S with B := Function.update S.B pos (updateOn f (S.B pos) val) } := by
  refine packAS_eq_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_main]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_R]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_C]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_T]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_Out]
  · exact updateOn_trans_slotEmb_comp_regEmb _ f (packAS d S) S.B (packAS_B d S) pos val
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tr1]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_sortAnc]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_dR]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_flagBit]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tmpD]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_primAnc]

lemma updateOn_dR (d : ℕ) (S : AsSnap d) (val : Qubits d) :
    updateOn (eDR d) (packAS d S) val = packAS d { S with dR := val } := by
  refine packAS_eq_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_main]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_R]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_C]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_T]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_Out]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_B]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tr1]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_sortAnc]
  · exact updateOn_comp_self' _ _ _
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_flagBit]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tmpD]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_primAnc]

lemma updateOn_flagBit (d : ℕ) (S : AsSnap d) (val : Qubits 1) :
    updateOn (eFlag d) (packAS d S) val = packAS d { S with flagBit := val } := by
  refine packAS_eq_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_main]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_R]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_C]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_T]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_Out]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_B]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tr1]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_sortAnc]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_dR]
  · exact updateOn_comp_self' _ _ _
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tmpD]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_primAnc]

lemma updateOn_tmpD (d : ℕ) (S : AsSnap d) (val : Qubits d) :
    updateOn (eTmp d) (packAS d S) val = packAS d { S with tmpD := val } := by
  refine packAS_eq_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_main]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_R]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_C]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_T]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_Out]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_B]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tr1]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_sortAnc]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_dR]
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_flagBit]
  · exact updateOn_comp_self' _ _ _
  · rw [updateOn_comp_disjoint _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_primAnc]

lemma inRange_slot_t (d : ℕ) (pos : Fin (arity d)) {l : ℕ} (f : Fin l ↪ Fin (wT d)) :
    InRange (oT d) (oOut d) (f.trans (tSlot d pos)) := inRange_tField d pos f

lemma fT_disjoint {d l1 l2 : ℕ} (pos : Fin (arity d)) (f1 : Fin l1 ↪ Fin (wT d))
    (f2 : Fin l2 ↪ Fin (wT d)) (hf : ∀ a b, f1 a ≠ f2 b) :
    ∀ a b, (f1.trans (tSlot d pos)) a ≠ (f2.trans (tSlot d pos)) b := by
  intro a b hab
  exact hf a b ((tSlot d pos).injective hab)

lemma fOut_disjoint {d l1 l2 : ℕ} (pos : Fin (arity d)) (f1 : Fin l1 ↪ Fin (wOut d))
    (f2 : Fin l2 ↪ Fin (wOut d)) (hf : ∀ a b, f1 a ≠ f2 b) :
    ∀ a b, (f1.trans (outSlot d pos)) a ≠ (f2.trans (outSlot d pos)) b :=
  fun a b hab => hf a b ((outSlot d pos).injective hab)

lemma fB_disjoint {d l1 l2 : ℕ} (pos : Fin (arity d)) (f1 : Fin l1 ↪ Fin (wB d))
    (f2 : Fin l2 ↪ Fin (wB d)) (hf : ∀ a b, f1 a ≠ f2 b) :
    ∀ a b, (f1.trans (bSlot d pos)) a ≠ (f2.trans (bSlot d pos)) b :=
  fun a b hab => hf a b ((bSlot d pos).injective hab)

lemma ePA_head_comp {d : ℕ} (z : Qubits (d + 1)) (hz : z = fun _ => false) :
    z ∘ Fin.castLEEmb (by omega : 1 ≤ d + 1) = fun _ => false := by
  funext i; simp [hz]

lemma ePA_prefix_comp {d k : ℕ} (hk : k ≤ d + 1) (z : Qubits (d + 1)) (hz : z = fun _ => false) :
    z ∘ Fin.castLEEmb hk = fun _ => false := by
  funext i; simp [hz]

/-! ### Part 6: `tRecOf`, `mergePhi` Key Equivalence, `prepTtilde0`, `Sort 1`, `fwdScan` -/

def tRecOf (d k idx r c : ℕ) : Qubits (wT d) :=
  let kR := if idx < k then r else r - (idx - k)
  let tag : Qubits 1 := fun _ => decide (idx < k)
  tRecPack d (natToBits d kR) tag (natToBits d idx) (natToBits d r) (natToBits d c)

lemma bitsToNat_fin1 (comb : LcgSym54Comb) (b : Bool) :
    bitsToNat (fun _ : Fin 1 => b) = if b then 1 else 0 := by
  have h : (fun _ : Fin 1 => b) = natToBits 1 (if b then 1 else 0) := by
    funext i
    have hi0 : i = (0 : Fin 1) := Fin.ext (by omega)
    subst hi0
    have hrev : (0 : Fin 1).rev = 0 := Fin.ext (by omega)
    have ht := comb.natToBits_comp_revPerm 1 (if b then 1 else 0) 0
    rw [hrev] at ht
    rw [ht]
    cases b <;> simp
  rw [h, comb.bitsToNat_natToBits (by cases b <;> norm_num)]

lemma bitsToNat_tKeyPack (comb : LcgSym54Comb) (d : ℕ) (kR : Qubits d) (tag : Bool) (idx : Qubits d) :
    bitsToNat (tKeyPack d kR (fun _ => tag) idx) =
      2 ^ (1 + d) * bitsToNat kR + 2 ^ d * (if tag then 1 else 0) + bitsToNat idx := by
  dsimp only [tKeyPack]
  rw [comb.bitsToNat_append, comb.bitsToNat_append, bitsToNat_fin1 comb]
  ring

lemma two_mul_add_le_iff {P a b c d : ℕ} (hc : c < P) (hd : d < P) :
    P * a + c ≤ P * b + d ↔ (a < b ∨ (a = b ∧ c ≤ d)) := by
  constructor
  · intro h
    rcases lt_or_eq_of_le (by
      by_contra hgt
      have hab : b + 1 ≤ a := Nat.lt_of_not_ge hgt
      have : P * (b + 1) ≤ P * a := Nat.mul_le_mul_left P hab
      nlinarith) with hlt | heq
    · left; exact hlt
    · right; subst heq; exact ⟨rfl, by omega⟩
  · rintro (hlt | ⟨rfl, hcd⟩)
    · have : P * (a + 1) ≤ P * b := Nat.mul_le_mul_left P hlt
      nlinarith
    · omega

lemma two_step_lex_le_iff {d k1 t1 i1 k2 t2 i2 : ℕ}
    (ht1 : t1 < 2) (ht2 : t2 < 2) (hi1 : i1 < 2 ^ d) (hi2 : i2 < 2 ^ d) :
    2 ^ (1 + d) * k1 + 2 ^ d * t1 + i1 ≤ 2 ^ (1 + d) * k2 + 2 ^ d * t2 + i2 ↔
      toLex (k1, toLex (t1, i1)) ≤ toLex (k2, toLex (t2, i2)) := by
  have hpow : 2 ^ (1 + d) = 2 * 2 ^ d := by rw [Nat.add_comm 1 d, pow_succ, mul_comm]
  rw [hpow, add_assoc (2 * 2 ^ d * k1), add_assoc (2 * 2 ^ d * k2)]
  have hb1 : 2 ^ d * t1 + i1 < 2 * 2 ^ d := by nlinarith
  have hb2 : 2 ^ d * t2 + i2 < 2 * 2 ^ d := by nlinarith
  rw [two_mul_add_le_iff hb1 hb2, two_mul_add_le_iff hi1 hi2]
  simp [Prod.Lex.le_iff]

lemma tRecOf_key_le_iff (comb : LcgSym54Comb) (d k : ℕ)
    {idx1 r1 c1 idx2 r2 c2 : ℕ}
    (hi1 : idx1 < 2 ^ d) (hr1 : r1 < 2 ^ d) (hi2 : idx2 < 2 ^ d) (hr2 : r2 < 2 ^ d) :
    bitsToNat (recKey54 (tRecOf d k idx1 r1 c1)) ≤ bitsToNat (recKey54 (tRecOf d k idx2 r2 c2)) ↔
      mergePhi k (idx1, r1, c1) ≤ mergePhi k (idx2, r2, c2) := by
  dsimp only [tRecOf]
  rw [recKey54_tRecPack, recKey54_tRecPack, bitsToNat_tKeyPack comb, bitsToNat_tKeyPack comb]
  have hk1 : (if idx1 < k then r1 else r1 - (idx1 - k)) < 2 ^ d := by split_ifs <;> omega
  have hk2 : (if idx2 < k then r2 else r2 - (idx2 - k)) < 2 ^ d := by split_ifs <;> omega
  rw [comb.bitsToNat_natToBits hk1, comb.bitsToNat_natToBits hi1,
    comb.bitsToNat_natToBits hk2, comb.bitsToNat_natToBits hi2]
  rw [two_step_lex_le_iff (by split_ifs <;> omega) (by split_ifs <;> omega) hi1 hi2]
  dsimp only [mergePhi]
  by_cases c1 : idx1 < k <;> by_cases c2 : idx2 < k <;> simp [c1, c2]

def liftPos {d ℓ : ℕ} (hℓ : ℓ < d) (pos : Fin (arity (ℓ + 1))) : Fin (arity d) :=
  ⟨pos.1, lt_of_lt_of_le pos.isLt (by simp only [arity_eq_two_pow]; exact Nat.pow_le_pow_right (by norm_num) hℓ)⟩

lemma arity_succ_le {d ℓ : ℕ} (hℓ : ℓ < d) : arity (ℓ + 1) ≤ arity d := by
  simp only [arity_eq_two_pow]; exact Nat.pow_le_pow_right (by norm_num) hℓ

lemma arity_succ_eq (ℓ : ℕ) : arity (ℓ + 1) = 2 * arity ℓ := by
  rw [arity_eq_two_pow, arity_eq_two_pow, pow_succ, mul_comm]

lemma lr_length (comb : LcgSym54Comb) (s : ℕ → ℕ) (lo len : ℕ)
    (hs : ∀ c, c < lo + 2 * len → s c ≤ c) :
    (greedyDiag s lo (lo + len) ++ greedyDiag s (lo + len) (lo + 2 * len)).length = 2 * len := by
  have h1 := comb.greedyDiag_length s lo (lo + len) (by omega) (fun c _ hc => hs c (by omega))
  have h2 := comb.greedyDiag_length s (lo + len) (lo + 2 * len) (by omega) (fun c _ hc => hs c (by omega))
  rw [List.length_append, h1, h2]
  omega

lemma ttilde0_length (comb : LcgSym54Comb) (s : ℕ → ℕ) (lo ℓ : ℕ)
    (hs : ∀ c, c < lo + 2 * arity ℓ → s c ≤ c) :
    ((((greedyDiag s lo (lo + arity ℓ) ++ greedyDiag s (lo + arity ℓ) (lo + 2 * arity ℓ)).zipIdx).map
      (fun ((r, c), idx) => (idx, r, c))).length) = arity (ℓ + 1) := by
  rw [List.length_map, List.length_zipIdx, lr_length comb s lo (arity ℓ) hs, arity_succ_eq]

lemma ttilde1_length (comb : LcgSym54Comb) (s : ℕ → ℕ) (lo ℓ : ℕ)
    (hs : ∀ c, c < lo + 2 * arity ℓ → s c ≤ c) :
    (((((greedyDiag s lo (lo + arity ℓ) ++ greedyDiag s (lo + arity ℓ) (lo + 2 * arity ℓ)).zipIdx).map
      (fun ((r, c), idx) => (idx, r, c))).mergeSort
        (fun a b => decide (mergePhi (arity ℓ) a ≤ mergePhi (arity ℓ) b))).length) = arity (ℓ + 1) := by
  rw [(List.mergeSort_perm _ _).length_eq, ttilde0_length comb s lo ℓ hs]

def padTr (T0 T1 : ℕ) (_hT : T0 ≤ T1) (flags : Qubits T0) : Qubits T1 :=
  fun i => if h : i.1 < T0 then flags ⟨i.1, h⟩ else false

lemma padTr_comp_castLE (T0 T1 : ℕ) (hT : T0 ≤ T1) (flags : Qubits T0) :
    padTr T0 T1 hT flags ∘ Fin.castLEEmb hT = flags := by
  funext i; have := i.isLt; simp [padTr, this]

lemma updateOn_castLE_zero (T0 T1 : ℕ) (hT : T0 ≤ T1) (flags : Qubits T0) :
    updateOn (Fin.castLEEmb hT) (fun _ => false) flags = padTr T0 T1 hT flags := by
  funext i
  by_cases hi : i.1 < T0
  · have hmem : i = Fin.castLEEmb hT ⟨i.1, hi⟩ := Fin.ext rfl
    conv_lhs => rw [hmem]
    rw [updateOn_apply_emb]
    simp [padTr, hi]
  · have hnot : i ∉ Set.range (Fin.castLEEmb hT) := by
      rintro ⟨j, hj⟩
      have := congrArg Fin.val hj
      have hjlt := j.isLt
      simp at this
      omega
    rw [updateOn_apply_not_mem _ _ _ hnot]
    simp [padTr, hi]

lemma updateOn_castLE_zero_zero (T0 T1 : ℕ) (hT : T0 ≤ T1) :
    updateOn (Fin.castLEEmb hT) (fun _ => false) (fun _ => false) = fun _ => false := by
  funext i
  by_cases hi : i ∈ Set.range (Fin.castLEEmb hT)
  · rcases hi with ⟨j, rfl⟩; rw [updateOn_apply_emb]
  · rw [updateOn_apply_not_mem _ _ _ hi]

lemma tPrefixRange_le (d : ℕ) : oT d + arity d * wT d ≤ totAS d := by
  dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut]; omega

lemma bPrefixRange_le (d : ℕ) : oB d + arity d * wB d ≤ totAS d := by
  dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr]; omega

def prepTtilde0Step (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d)
    (pos : Fin (arity (ℓ + 1))) : LayeredCircuit (totAS d) :=
  let lo := b * (2 * arity ℓ)
  let p : Fin (arity d) := ⟨lo + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩
  let pos' := liftPos hℓ pos
  let c1 := (arith.copyRegCircuit d).mapWires (combineEmb (rSlot d p) (tREmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
  let c2 := (arith.copyRegCircuit d).mapWires (combineEmb (cSlot d p) (tCEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
  let c3 := (arith.setConstMSBCircuit d pos.1).mapWires (tIdxEmb d pos')
  if pos.1 < arity ℓ then
    let c4 := (arith.setConstMSBCircuit 1 1).mapWires (tTagEmb d pos')
    let c5 := (arith.copyRegCircuit d).mapWires (combineEmb (rSlot d p) (tKeyEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
    LayeredCircuit.seqList [c1, c2, c3, c4, c5]
  else
    let c4 := (arith.copyRegCircuit d).mapWires (combineEmb (rSlot d p) (tKeyEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
    let c5 := (arith.setConstMSBCircuit d (pos.1 - arity ℓ)).mapWires (eTmp d)
    let c6 := (arith.subInPlaceMSBCircuit d).mapWires
      (combineEmb (combineEmb (eTmp d) (tKeyEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
        ((Fin.castLEEmb (by omega : 1 ≤ d + 1)).trans (ePA d))
        (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
    let c7 := (arith.setConstMSBCircuit d (pos.1 - arity ℓ)).mapWires (eTmp d)
    LayeredCircuit.seqList [c1, c2, c3, c4, c5, c6, c7]

lemma prepTtilde0Step_size (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) (pos : Fin (arity (ℓ + 1))) :
    (prepTtilde0Step arith d ℓ b hℓ hb pos).size ≤ 20 * d + 1 := by
  dsimp only [prepTtilde0Step]
  split_ifs
  · simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      LayeredCircuit.mapWires_size, arith.copyRegCircuit_size]
    have hs3 := arith.setConstMSBCircuit_size d pos.1
    have hs4 := arith.setConstMSBCircuit_size 1 1
    omega
  · simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      LayeredCircuit.mapWires_size, arith.copyRegCircuit_size, arith.subInPlaceMSBCircuit_size]
    have hs3 := arith.setConstMSBCircuit_size d pos.1
    have hs5 := arith.setConstMSBCircuit_size d (pos.1 - arity ℓ)
    omega

lemma prepTtilde0Step_act (comb : LcgSym54Comb) (arith : LcgSym54ArithV2)
    (d ℓ b : ℕ) (hℓ : ℓ < d) (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d)
    (pos : Fin (arity (ℓ + 1))) (S : AsSnap d)
    (hTpos : S.T (liftPos hℓ pos) = fun _ => false)
    (htmp : S.tmpD = fun _ => false) (hpa : S.primAnc = fun _ => false)
    (rVal cVal : ℕ) (hrLt : rVal < 2 ^ d) (_hcLt : cVal < 2 ^ d)
    (hpR : S.R ⟨b * (2 * arity ℓ) + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩ = natToBits d rVal)
    (hpC : S.C ⟨b * (2 * arity ℓ) + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩ = natToBits d cVal)
    (hgeR : arity ℓ ≤ pos.1 → pos.1 - arity ℓ ≤ rVal) :
    act (prepTtilde0Step arith d ℓ b hℓ hb pos).unitary (ket (packAS d S)) =
      ket (packAS d { S with
        T := Function.update S.T (liftPos hℓ pos) (tRecOf d (arity ℓ) pos.1 rVal cVal) }) := by
  let lo := b * (2 * arity ℓ)
  let p : Fin (arity d) := ⟨lo + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩
  let pos' := liftPos hℓ pos
  have hpR' : S.R p = natToBits d rVal := hpR
  have hpC' : S.C p = natToBits d cVal := hpC
  have hT0 : S.T pos' = tRecPack d (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) := by
    rw [hTpos, tRecPack_zero]
  have step1 : act ((arith.copyRegCircuit d).mapWires (combineEmb (rSlot d p) (tREmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary (ket (packAS d S)) =
      ket (packAS d { S with T := Function.update S.T pos' (tRecPack d (fun _ => false) (fun _ => false) (fun _ => false) (natToBits d rVal) (fun _ => false)) }) := by
    rw [act_copyRegOn]
    rw [tREmb, updateOn_tField]
    simp only [packAS_field_t_apply, packAS_slot_apply_R, hT0, tRecPack_apply_fTR, hpR', Bool.false_xor, update_fTR]
  have step2 : ∀ (kR0 : Qubits d) (tag0 : Qubits 1) (idx0 : Qubits d),
      act ((arith.copyRegCircuit d).mapWires (combineEmb (cSlot d p) (tCEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary
        (ket (packAS d { S with T := Function.update S.T pos' (tRecPack d kR0 tag0 idx0 (natToBits d rVal) (fun _ => false)) })) =
      ket (packAS d { S with T := Function.update S.T pos' (tRecPack d kR0 tag0 idx0 (natToBits d rVal) (natToBits d cVal)) }) := by
    intro kR0 tag0 idx0
    rw [act_copyRegOn]
    rw [tCEmb, updateOn_tField]
    simp only [packAS_field_t_apply, packAS_slot_apply_C, Function.update_self, tRecPack_apply_fTC, hpC', Bool.false_xor, update_fTC, Function.update_idem]
  have step3 : ∀ (kR0 : Qubits d) (tag0 : Qubits 1),
      act ((arith.setConstMSBCircuit d pos.1).mapWires (tIdxEmb d pos')).unitary
        (ket (packAS d { S with T := Function.update S.T pos' (tRecPack d kR0 tag0 (fun _ => false) (natToBits d rVal) (natToBits d cVal)) })) =
      ket (packAS d { S with T := Function.update S.T pos' (tRecPack d kR0 tag0 (natToBits d pos.1) (natToBits d rVal) (natToBits d cVal)) }) := by
    intro kR0 tag0
    rw [act_setConstOn]
    rw [tIdxEmb, updateOn_tField]
    simp only [packAS_field_t_apply, Function.update_self, tRecPack_apply_fTIdx, Bool.false_xor, update_fTIdx, Function.update_idem]
  have h1bit : natToBits 1 1 0 = true := by
    have ht := comb.natToBits_comp_revPerm 1 1 0
    have hr : (0 : Fin 1).rev = 0 := Fin.ext (by omega)
    rw [hr] at ht; simpa using ht
  dsimp only [prepTtilde0Step]
  by_cases hlt : pos.1 < arity ℓ
  · rw [if_pos hlt]
    simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, LayeredCircuit.id_unitary, act_mul, act_one]
    rw [step1, step2, step3]
    have h4 : act ((arith.setConstMSBCircuit 1 1).mapWires (tTagEmb d pos')).unitary
        (ket (packAS d { S with T := Function.update S.T pos' (tRecPack d (fun _ => false) (fun _ => false) (natToBits d pos.1) (natToBits d rVal) (natToBits d cVal)) })) =
        ket (packAS d { S with T := Function.update S.T pos' (tRecPack d (fun _ => false) (fun _ => true) (natToBits d pos.1) (natToBits d rVal) (natToBits d cVal)) }) := by
      rw [act_setConstOn]
      rw [tTagEmb, updateOn_tField]
      simp only [packAS_field_t_apply, Function.update_self, tRecPack_apply_fTTag]
      have hx : (fun j : Fin 1 => xor false (natToBits 1 1 j)) = fun _ => true := by
        funext j; have hj : j = 0 := Fin.ext (by omega); subst hj; simp [h1bit]
      rw [hx, update_fTTag, Function.update_idem]
    rw [h4, act_copyRegOn]
    change ket (updateOn (tKeyEmb d pos') _ _) = _
    rw [tKeyEmb, updateOn_tField]
    simp only [packAS_field_t_apply, packAS_slot_apply_R, Function.update_self, tRecPack_apply_fTK, hpR, Bool.false_xor, update_fTK, Function.update_idem]
    congr 2; apply AsSnap.ext <;> try rfl
    dsimp only; simp only [tRecOf, if_pos hlt, decide_eq_true hlt]; rfl
  · rw [if_neg hlt]
    simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, LayeredCircuit.id_unitary, act_mul, act_one]
    rw [step1, step2, step3]
    have h4 : act ((arith.copyRegCircuit d).mapWires (combineEmb (rSlot d p) (tKeyEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary
        (ket (packAS d { S with T := Function.update S.T pos' (tRecPack d (fun _ => false) (fun _ => false) (natToBits d pos.1) (natToBits d rVal) (natToBits d cVal)) })) =
        ket (packAS d { S with T := Function.update S.T pos' (tRecPack d (natToBits d rVal) (fun _ => false) (natToBits d pos.1) (natToBits d rVal) (natToBits d cVal)) }) := by
      rw [act_copyRegOn]
      rw [tKeyEmb, updateOn_tField]
      simp only [packAS_field_t_apply, packAS_slot_apply_R, Function.update_self, tRecPack_apply_fTK, hpR', Bool.false_xor, update_fTK, Function.update_idem]
    have h5 : act ((arith.setConstMSBCircuit d (pos.1 - arity ℓ)).mapWires (eTmp d)).unitary
        (ket (packAS d { S with T := Function.update S.T pos' (tRecPack d (natToBits d rVal) (fun _ => false) (natToBits d pos.1) (natToBits d rVal) (natToBits d cVal)) })) =
        ket (packAS d { S with
          T := Function.update S.T pos' (tRecPack d (natToBits d rVal) (fun _ => false) (natToBits d pos.1) (natToBits d rVal) (natToBits d cVal))
          tmpD := natToBits d (pos.1 - arity ℓ) }) := by
      rw [act_setConstOn, updateOn_tmpD]
      simp only [packAS_tmpD_apply, htmp, Bool.false_xor]
    rw [h4, h5]
    let S5 : AsSnap d := { S with
      T := Function.update S.T pos' (tRecPack d (natToBits d rVal) (fun _ => false) (natToBits d pos.1) (natToBits d rVal) (natToBits d cVal))
      tmpD := natToBits d (pos.1 - arity ℓ) }
    have h6 : act ((arith.subInPlaceMSBCircuit d).mapWires
        (combineEmb (combineEmb (eTmp d) (tKeyEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
          ((Fin.castLEEmb (by omega : 1 ≤ d + 1)).trans (ePA d))
          (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))).unitary (ket (packAS d S5)) =
        ket (packAS d { S5 with
          T := Function.update S5.T pos' (tRecPack d (natToBits d (rVal - (pos.1 - arity ℓ))) (fun _ => false) (natToBits d pos.1) (natToBits d rVal) (natToBits d cVal)) }) := by
      rw [act_subInPlaceOn arith (eTmp d) (tKeyEmb d pos')
        ((Fin.castLEEmb (by omega : 1 ≤ d + 1)).trans (ePA d)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (packAS d S5)
        (by change (packAS d S5 ∘ ePA d) ∘ Fin.castLEEmb _ = _; rw [packAS_primAnc]; exact ePA_head_comp _ hpa)]
      rw [tKeyEmb, updateOn_tField, packAS_field_t]
      dsimp only [S5]; rw [Function.update_self, tRecPack_comp_fTK, packAS_tmpD]
      have hsub_lt : pos.1 - arity ℓ < 2 ^ d := lt_of_le_of_lt (hgeR (Nat.le_of_not_lt hlt)) hrLt
      rw [comb.bitsToNat_natToBits hsub_lt, comb.bitsToNat_natToBits hrLt]
      have heq_sub : 2 ^ d + rVal - (pos.1 - arity ℓ) = 2 ^ d + (rVal - (pos.1 - arity ℓ)) := by
        have := hgeR (Nat.le_of_not_lt hlt); omega
      rw [heq_sub, natToBits_add_two_pow comb, update_fTK]
    rw [h6, act_setConstOn, updateOn_tmpD]
    have hx0 : (fun j => xor (packAS d { S5 with
        T := Function.update S5.T pos' (tRecPack d (natToBits d (rVal - (pos.1 - arity ℓ))) (fun _ => false) (natToBits d pos.1) (natToBits d rVal) (natToBits d cVal)) } (eTmp d j))
        (natToBits d (pos.1 - arity ℓ) j)) = fun _ => false := by
      funext j; simp only [packAS_tmpD_apply]; dsimp only [S5]; rw [Bool.xor_self]
    rw [hx0]
    congr 2; apply AsSnap.ext <;> try rfl
    · dsimp only [S5]; simp only [Function.update_idem, tRecOf, if_neg hlt, decide_eq_false hlt]; rfl
    · exact htmp.symm

def prepTtilde0 (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) : LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList ((List.finRange (arity (ℓ + 1))).map (prepTtilde0Step arith d ℓ b hℓ hb))

lemma prepTtilde0_size (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) :
    (prepTtilde0 arith d ℓ b hℓ hb).size ≤ arity (ℓ + 1) * (20 * d + 1) :=
  seqList_fin_size_le _ _ (prepTtilde0Step_size arith d ℓ b hℓ hb)

lemma prepTtilde0_act (comb : LcgSym54Comb) (arith : LcgSym54ArithV2)
    (d ℓ b : ℕ) (hℓ : ℓ < d) (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d)
    (S : AsSnap d) (hT : S.T = fun _ _ => false)
    (htmp : S.tmpD = fun _ => false) (hpa : S.primAnc = fun _ => false)
    (rOf cOf : Fin (arity (ℓ + 1)) → ℕ)
    (hrLt : ∀ pos, rOf pos < 2 ^ d) (hcLt : ∀ pos, cOf pos < 2 ^ d)
    (hgeR : ∀ pos : Fin (arity (ℓ + 1)), arity ℓ ≤ pos.1 → pos.1 - arity ℓ ≤ rOf pos)
    (hR : ∀ pos : Fin (arity (ℓ + 1)),
      S.R ⟨b * (2 * arity ℓ) + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩ = natToBits d (rOf pos))
    (hC : ∀ pos : Fin (arity (ℓ + 1)),
      S.C ⟨b * (2 * arity ℓ) + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩ = natToBits d (cOf pos)) :
    act (prepTtilde0 arith d ℓ b hℓ hb).unitary (ket (packAS d S)) =
      ket (packAS d { S with
        T := fun q =>
          if hq : q.1 < arity (ℓ + 1) then
            let pos : Fin (arity (ℓ + 1)) := ⟨q.1, hq⟩
            tRecOf d (arity ℓ) pos.1 (rOf pos) (cOf pos)
          else fun _ => false }) := by
  let inv : ℕ → Qubits (totAS d) := fun k =>
    packAS d { S with
      T := fun q =>
        if hqk : q.1 < k then
          if hq : q.1 < arity (ℓ + 1) then
            let pos : Fin (arity (ℓ + 1)) := ⟨q.1, hq⟩
            tRecOf d (arity ℓ) pos.1 (rOf pos) (cOf pos)
          else fun _ => false
        else fun _ => false }
  have h0 : inv 0 = packAS d S := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> simp [hT]
  have hn : inv (arity (ℓ + 1)) = packAS d { S with
      T := fun q =>
        if hq : q.1 < arity (ℓ + 1) then
          let pos : Fin (arity (ℓ + 1)) := ⟨q.1, hq⟩
          tRecOf d (arity ℓ) pos.1 (rOf pos) (cOf pos)
        else fun _ => false } := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    dsimp only; funext q; by_cases hq : q.1 < arity (ℓ + 1) <;> simp only [hq, ↓reduceDIte]
  rw [← h0, ← hn]
  refine act_seqList_fin _ inv fun pos => ?_
  have hstep := prepTtilde0Step_act comb arith d ℓ b hℓ hb pos
    { S with
      T := fun q =>
        if hqk : q.1 < pos.1 then
          if hq : q.1 < arity (ℓ + 1) then
            let pos₀ : Fin (arity (ℓ + 1)) := ⟨q.1, hq⟩
            tRecOf d (arity ℓ) pos₀.1 (rOf pos₀) (cOf pos₀)
          else fun _ => false
        else fun _ => false }
    (by dsimp only [liftPos]; rw [dif_neg (Nat.lt_irrefl _)]) htmp hpa (rOf pos) (cOf pos) (hrLt pos) (hcLt pos)
    (hR pos) (hC pos) (hgeR pos)
  rw [hstep]
  dsimp only [inv]
  congr 2; apply AsSnap.ext <;> try rfl
  funext q; dsimp only
  by_cases hq : q = liftPos hℓ pos
  · subst hq
    rw [Function.update_self,
      dif_pos (show (liftPos hℓ pos).1 < pos.1 + 1 by dsimp only [liftPos]; exact Nat.lt_succ_self pos.1),
      dif_pos (show (liftPos hℓ pos).1 < arity (ℓ + 1) by dsimp only [liftPos]; exact pos.isLt)]
    rfl
  · rw [Function.update_of_ne hq]
    have hq_ne : q.1 ≠ pos.1 := fun h => hq (Fin.ext h)
    by_cases hqk : q.1 < pos.1
    · have hqk1 : q.1 < pos.1 + 1 := by omega
      rw [dif_pos hqk, dif_pos hqk1]
    · have hnqk1 : ¬ q.1 < pos.1 + 1 := by omega
      rw [dif_neg hqk, dif_neg hnqk1]

/-! ### Part 6b: `packDTA54Emb`, `Sort 1`, and `fwdScan` -/

lemma act_mapWires_ket_singleton {m₀ m : ℕ} (lc : LayeredCircuit m₀) (emb : Fin m₀ ↪ Fin m)
    (z : Qubits m) (y₀ : Qubits m₀) (h : act lc.unitary (ket (z ∘ emb)) = ket y₀) :
    act (lc.mapWires emb).unitary (ket z) = ket (updateOn emb z y₀) := by
  have hsum := LcgSym54.act_mapWires_ket_sum lc emb z ({()} : Finset Unit) (fun _ => 1) (fun _ => y₀)
    (by simpa using h)
  simpa using hsum

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

lemma updateOn_packDTA54_disjoint {N w T anc m k2 : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (eOther : Fin k2 ↪ Fin m)
    (hoA : ∀ i x, eArr i ≠ eOther x) (hoT : ∀ j x, eTr j ≠ eOther x) (hoAnc : ∀ k x, eAnc k ≠ eOther x)
    (z : Qubits m) (arr : Fin N → Qubits w) (tr : Qubits T) :
    updateOn (packDTA54Emb eArr eTr eAnc hAT hAA hTA) z (packDTA54 N w T anc arr tr) ∘ eOther =
      z ∘ eOther :=
  updateOn_comp_disjoint _ _
    (emb_disjoint_combineEmb (emb_disjoint_combineEmb hAT hAA hTA)
      (emb_disjoint_combineEmb hAT hoA hoT) hoAnc) z _

lemma updateOn_packDTA54_prefixReg {m off N K w T anc : ℕ} (h : off + N * w ≤ m) (hKN : K ≤ N)
    (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, prefixRegEmb h hKN i ≠ eTr j)
    (hAA : ∀ i k, prefixRegEmb h hKN i ≠ eAnc k)
    (hTA : ∀ j k, eTr j ≠ eAnc k)
    (hTR : ∀ j r, eTr j ≠ regEmb off N w h r)
    (hAR : ∀ k r, eAnc k ≠ regEmb off N w h r)
    (z : Qubits m) (arr0 : Fin N → Qubits w) (hz : z ∘ regEmb off N w h = flatReg N w arr0)
    (arr : Fin K → Qubits w) (tr : Qubits T) :
    updateOn (packDTA54Emb (prefixRegEmb h hKN) eTr eAnc hAT hAA hTA) z
        (packDTA54 K w T anc arr tr) ∘ regEmb off N w h =
      flatReg N w (fun q => if hq : q.1 < K then arr ⟨q.1, hq⟩ else arr0 q) := by
  funext idx
  rcases finProdFinEquiv.surjective idx with ⟨⟨q, b⟩, rfl⟩
  simp only [Function.comp_apply, flatReg, Equiv.symm_apply_apply]
  by_cases hq : q.1 < K
  · rw [dif_pos hq]
    have hpre : regEmb off N w h (finProdFinEquiv (q, b)) =
        packDTA54Emb (prefixRegEmb h hKN) eTr eAnc hAT hAA hTA
          (Fin.castAdd anc (Fin.castAdd T (finProdFinEquiv (⟨q.1, hq⟩, b)))) := by
      rw [packDTA54Emb_arr]; simp only [prefixRegEmb_mem_regEmb, Equiv.symm_apply_apply]; rfl
    rw [hpre, updateOn_apply_emb, packDTA54, padZero_castAdd, Fin.append_left, flatReg, Equiv.symm_apply_apply]
  · rw [dif_neg hq]
    have hnot : regEmb off N w h (finProdFinEquiv (q, b)) ∉
        Set.range (packDTA54Emb (prefixRegEmb h hKN) eTr eAnc hAT hAA hTA) := by
      rintro ⟨u, hu⟩
      refine Fin.addCases (fun ij => ?_) (fun k => ?_) u hu
      · refine Fin.addCases (fun i => ?_) (fun j => ?_) ij
        · rw [packDTA54Emb_arr, prefixRegEmb_mem_regEmb]
          intro hi
          have h1 := Prod.ext_iff.mp (finProdFinEquiv.injective ((regEmb off N w h).injective hi))
          have hlt := (finProdFinEquiv.symm i).1.isLt
          have hv := congrArg Fin.val h1.1
          simp only [Fin.val_castLE] at hv
          omega
        · rw [packDTA54Emb_tr]; exact fun hje => hTR j _ hje
      · rw [packDTA54Emb_anc]; exact fun hke => hAR k _ hke
    rw [updateOn_apply_not_mem _ _ _ hnot]
    have hpt := congrFun hz (finProdFinEquiv (q, b))
    simpa [Function.comp_apply, flatReg] using hpt

lemma updateOn_packDTA54_prefixSlice {m N w T0 T1 anc : ℕ} (hT : T0 ≤ T1)
    (eArr : Fin (N * w) ↪ Fin m) (eFull : Fin T1 ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ (Fin.castLEEmb hT).trans eFull j)
    (hAA : ∀ i k, eArr i ≠ eAnc k)
    (hTA : ∀ j k, (Fin.castLEEmb hT).trans eFull j ≠ eAnc k)
    (hFA : ∀ i r, eArr i ≠ eFull r)
    (hFAnc : ∀ k r, eAnc k ≠ eFull r)
    (z : Qubits m) (hz : z ∘ eFull = fun _ => false)
    (arr : Fin N → Qubits w) (tr : Qubits T0) :
    updateOn (packDTA54Emb eArr ((Fin.castLEEmb hT).trans eFull) eAnc hAT hAA hTA) z
        (packDTA54 N w T0 anc arr tr) ∘ eFull =
      padTr T0 T1 hT tr := by
  funext r
  by_cases hr : r.1 < T0
  · have hmem : eFull r = packDTA54Emb eArr ((Fin.castLEEmb hT).trans eFull) eAnc hAT hAA hTA
        (Fin.castAdd anc (Fin.natAdd (N * w) ⟨r.1, hr⟩)) := by
      rw [packDTA54Emb_tr]; rfl
    rw [Function.comp_apply, hmem, updateOn_apply_emb, packDTA54, padZero_castAdd, Fin.append_right]
    simp [padTr, hr]
  · have hnot : eFull r ∉ Set.range (packDTA54Emb eArr ((Fin.castLEEmb hT).trans eFull) eAnc hAT hAA hTA) := by
      rintro ⟨u, hu⟩
      refine Fin.addCases (fun ij => ?_) (fun k => ?_) u hu
      · refine Fin.addCases (fun i => ?_) (fun j => ?_) ij
        · rw [packDTA54Emb_arr]; exact hFA i r
        · rw [packDTA54Emb_tr]
          intro hj
          change eFull (Fin.castLEEmb hT j) = eFull r at hj
          have hv : r.1 = j.1 := congrArg Fin.val (eFull.injective hj).symm
          have hjlt := j.isLt
          omega
      · rw [packDTA54Emb_anc]; exact hFAnc k r
    rw [Function.comp_apply, updateOn_apply_not_mem _ _ _ hnot]
    have hpt := congrFun hz r
    simpa [padTr, hr] using hpt

lemma updateOn_packDTA54_prefixAncZero {m N w T A0 A1 : ℕ} (hA : A0 ≤ A1)
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eFull : Fin A1 ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j)
    (hAA : ∀ i k, eArr i ≠ (Fin.castLEEmb hA).trans eFull k)
    (hTA : ∀ j k, eTr j ≠ (Fin.castLEEmb hA).trans eFull k)
    (hFA : ∀ i r, eArr i ≠ eFull r)
    (hFT : ∀ j r, eTr j ≠ eFull r)
    (z : Qubits m) (hz : z ∘ eFull = fun _ => false)
    (arr : Fin N → Qubits w) (tr : Qubits T) :
    updateOn (packDTA54Emb eArr eTr ((Fin.castLEEmb hA).trans eFull) hAT hAA hTA) z
        (packDTA54 N w T A0 arr tr) ∘ eFull =
      fun _ => false := by
  funext r
  by_cases hr : r.1 < A0
  · have hmem : eFull r = packDTA54Emb eArr eTr ((Fin.castLEEmb hA).trans eFull) hAT hAA hTA
        (Fin.natAdd (N * w + T) ⟨r.1, hr⟩) := by
      rw [packDTA54Emb_anc]; rfl
    rw [Function.comp_apply, hmem, updateOn_apply_emb, packDTA54, padZero_natAdd]
  · have hnot : eFull r ∉ Set.range (packDTA54Emb eArr eTr ((Fin.castLEEmb hA).trans eFull) hAT hAA hTA) := by
      rintro ⟨u, hu⟩
      refine Fin.addCases (fun ij => ?_) (fun k => ?_) u hu
      · refine Fin.addCases (fun i => ?_) (fun j => ?_) ij
        · rw [packDTA54Emb_arr]; exact hFA i r
        · rw [packDTA54Emb_tr]; exact hFT j r
      · rw [packDTA54Emb_anc]
        intro hk
        change eFull (Fin.castLEEmb hA k) = eFull r at hk
        have hv : r.1 = k.1 := congrArg Fin.val (eFull.injective hk).symm
        have hklt := k.isLt
        omega
    rw [Function.comp_apply, updateOn_apply_not_mem _ _ _ hnot]
    exact congrFun hz r

def tPrefEmb (d ℓ : ℕ) (hℓ : ℓ < d) : Fin (arity (ℓ + 1) * wT d) ↪ Fin (totAS d) :=
  prefixRegEmb (tPrefixRange_le d) (arity_succ_le hℓ)

def bPrefEmb (d ℓ : ℕ) (hℓ : ℓ < d) : Fin (arity (ℓ + 1) * wB d) ↪ Fin (totAS d) :=
  prefixRegEmb (bPrefixRange_le d) (arity_succ_le hℓ)

def trPrefEmb (br : BitonicRouting54) (d ℓ : ℕ) (hℓ : ℓ < d) :
    Fin (sortTraceSize (ℓ + 1)) ↪ Fin (totAS d) :=
  (Fin.castLEEmb (sortTraceSize_mono br (by omega : ℓ + 1 ≤ d))).trans (eTr d)

def saSort1Emb (d : ℕ) : Fin (d + (1 + d)) ↪ Fin (totAS d) :=
  (Fin.castLEEmb (by omega : d + (1 + d) ≤ 2 * d + 1)).trans (eSA d)

def saSort2Emb (d : ℕ) : Fin d ↪ Fin (totAS d) :=
  (Fin.castLEEmb (by omega : d ≤ 2 * d + 1)).trans (eSA d)

lemma inRange_tPrefEmb (d ℓ : ℕ) (hℓ : ℓ < d) : InRange (oT d) (oOut d) (tPrefEmb d ℓ hℓ) :=
  inRange_prefixRegEmb (tPrefixRange_le d) (arity_succ_le hℓ)

lemma inRange_bPrefEmb (d ℓ : ℕ) (hℓ : ℓ < d) : InRange (oB d) (oTr d) (bPrefEmb d ℓ hℓ) :=
  inRange_prefixRegEmb (bPrefixRange_le d) (arity_succ_le hℓ)

lemma inRange_trPrefEmb (br : BitonicRouting54) (d ℓ : ℕ) (hℓ : ℓ < d) :
    InRange (oTr d) (oSA d) (trPrefEmb br d ℓ hℓ) :=
  inRange_trans _ _ (inRange_eTr d)

lemma inRange_saSort1Emb (d : ℕ) : InRange (oSA d) (oDR d) (saSort1Emb d) :=
  inRange_trans _ _ (inRange_eSA d)

lemma inRange_saSort2Emb (d : ℕ) : InRange (oSA d) (oDR d) (saSort2Emb d) :=
  inRange_trans _ _ (inRange_eSA d)

instance (d ℓ : ℕ) (hℓ : ℓ < d) : HasInRange (tPrefEmb d ℓ hℓ) (oT d) (oOut d) := ⟨inRange_tPrefEmb d ℓ hℓ⟩
instance (d ℓ : ℕ) (hℓ : ℓ < d) : HasInRange (bPrefEmb d ℓ hℓ) (oB d) (oTr d) := ⟨inRange_bPrefEmb d ℓ hℓ⟩
instance (br : BitonicRouting54) (d ℓ : ℕ) (hℓ : ℓ < d) :
    HasInRange (trPrefEmb br d ℓ hℓ) (oTr d) (oSA d) := ⟨inRange_trPrefEmb br d ℓ hℓ⟩
instance (d : ℕ) : HasInRange (saSort1Emb d) (oSA d) (oDR d) := ⟨inRange_saSort1Emb d⟩
instance (d : ℕ) : HasInRange (saSort2Emb d) (oSA d) (oDR d) := ⟨inRange_saSort2Emb d⟩

def sort1Emb (br : BitonicRouting54) (d ℓ : ℕ) (hℓ : ℓ < d) :
    Fin ((arity (ℓ + 1) * (d + (1 + d) + (d + d)) + sortTraceSize (ℓ + 1)) + (d + (1 + d))) ↪
      Fin (totAS d) :=
  packDTA54Emb (tPrefEmb d ℓ hℓ) (trPrefEmb br d ℓ hℓ) (saSort1Emb d)
    (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))

def sort1Circ (br : BitonicRouting54) (d ℓ : ℕ) (hℓ : ℓ < d) : LayeredCircuit (totAS d) :=
  (br.bitonicSortKeyCircuit (ℓ + 1) (d + (1 + d)) (d + d) true).mapWires (sort1Emb br d ℓ hℓ)

lemma sort1Circ_size (br : BitonicRouting54) (d ℓ : ℕ) (hℓ : ℓ < d) :
    ((sort1Circ br d ℓ hℓ).size : ℝ) ≤
      br.C_sort * (arity (ℓ + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 * ((4 * d + 2 : ℕ) : ℝ) := by
  dsimp only [sort1Circ]
  rw [LayeredCircuit.mapWires_size]
  have hs := br.bitonicSortKeyCircuit_size (ℓ + 1) (d + (1 + d)) (d + d) true
  have hc := le_of_lt br.hC_sort_pos
  have h1 : ((ℓ + 1 : ℕ) + 1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by norm_cast; omega
  have h2 : (2 ^ (ℓ + 1) : ℝ) = (arity (ℓ + 1) : ℝ) := by rw [arity_eq_two_pow]; push_cast; rfl
  have h3 : ((d + (1 + d) + (d + d) + 1 : ℕ) : ℝ) = ((4 * d + 2 : ℕ) : ℝ) := by push_cast; ring
  have hsq : (((ℓ + 1 : ℕ) + 1 : ℝ)) ^ 2 ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by gcongr
  calc
    ((br.bitonicSortKeyCircuit (ℓ + 1) (d + (1 + d)) (d + d) true).size : ℝ)
      ≤ br.C_sort * (2 ^ (ℓ + 1) : ℝ) * ((ℓ + 1 : ℕ) + 1 : ℝ) ^ 2 *
          ((d + (1 + d) + (d + d) + 1 : ℕ) : ℝ) := by
        simpa [Nat.cast_add, Nat.cast_one] using hs
    _ ≤ br.C_sort * (arity (ℓ + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 * ((4 * d + 2 : ℕ) : ℝ) := by
        rw [h2, h3]; gcongr

lemma pairwise_le_mergeSort_key {α κ : Type*} [LinearOrder κ]
    (key : α → κ) (L : List α) :
    (L.mergeSort (fun x y => decide (key x ≤ key y))).Pairwise (fun x y => key x ≤ key y) := by
  have hp := List.pairwise_mergeSort (le := fun x y => decide (key x ≤ key y))
    (fun a b c h1 h2 => by
      rw [decide_eq_true_iff] at h1 h2 ⊢
      exact le_trans h1 h2)
    (fun a b => by
      rcases le_total (key a) (key b) with h | h <;> simp [h]) L
  exact hp.imp fun h => decide_eq_true_eq.mp h

lemma sort1Circ_act (comb : LcgSym54Comb) (br : BitonicRouting54)
    (s : ℕ → ℕ) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (_hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d)
    (hs : ∀ c, c < b * (2 * arity ℓ) + 2 * arity ℓ → s c ≤ c)
    (S : AsSnap d)
    (htr : S.tr1 = fun _ => false) (hsa : S.sortAnc = fun _ => false)
    (hT : ∀ pos : Fin (arity (ℓ + 1)),
      S.T (liftPos hℓ pos) =
        let L := greedyDiag s (b * (2 * arity ℓ)) (b * (2 * arity ℓ) + arity ℓ)
        let R := greedyDiag s (b * (2 * arity ℓ) + arity ℓ) (b * (2 * arity ℓ) + 2 * arity ℓ)
        let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
        let t := Ttilde0[pos.1]'(by rw [ttilde0_length comb s (b * (2 * arity ℓ)) ℓ hs]; exact pos.isLt)
        tRecOf d (arity ℓ) t.1 t.2.1 t.2.2) :
    let lo := b * (2 * arity ℓ)
    let L := greedyDiag s lo (lo + arity ℓ)
    let R := greedyDiag s (lo + arity ℓ) (lo + 2 * arity ℓ)
    let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
    let Ttilde1 := Ttilde0.mergeSort (fun a b => decide (mergePhi (arity ℓ) a ≤ mergePhi (arity ℓ) b))
    let x0 : Fin (arity (ℓ + 1)) → Qubits (wT d) := fun pos => S.T (liftPos hℓ pos)
    act (sort1Circ br d ℓ hℓ).unitary (ket (packAS d S)) =
      ket (packAS d { S with
        T := fun q =>
          if hq : q.1 < arity (ℓ + 1) then
            let t := Ttilde1[q.1]'(by rw [ttilde1_length comb s lo ℓ hs]; exact hq)
            tRecOf d (arity ℓ) t.1 t.2.1 t.2.2
          else S.T q
        tr1 := padTr (sortTraceSize (ℓ + 1)) (sortTraceSize d)
          (sortTraceSize_mono br (by omega : ℓ + 1 ≤ d))
          (sortTrace (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0) }) := by
  intro lo L R Ttilde0 Ttilde1 x0
  have hT0_len : Ttilde0.length = arity (ℓ + 1) := ttilde0_length comb s lo ℓ hs
  have hT1_len : Ttilde1.length = arity (ℓ + 1) := ttilde1_length comb s lo ℓ hs
  have hx0_comp : packAS d S ∘ sort1Emb br d ℓ hℓ =
      packDTA54 (arity (ℓ + 1)) (wT d) (sortTraceSize (ℓ + 1)) (d + (1 + d)) x0 (fun _ => false) := by
    refine comp_packDTA54Emb _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    · change (packAS d S ∘ eT d) ∘ _ = _
      exact comp_prefixRegEmb (tPrefixRange_le d) (arity_succ_le hℓ) _ _ (packAS_T d S)
    · change (packAS d S ∘ eTr d) ∘ _ = _
      rw [packAS_tr1, htr]; rfl
    · change (packAS d S ∘ eSA d) ∘ _ = _
      rw [packAS_sortAnc, hsa]; rfl
  have hcirc := act_mapWires_ket_singleton (br.bitonicSortKeyCircuit (ℓ + 1) (d + (1 + d)) (d + d) true)
    (sort1Emb br d ℓ hℓ) (packAS d S) _ (by rw [hx0_comp]; exact br.act_bitonicSortKeyCircuit_ket _ _ _ _ x0)
  dsimp only [sort1Circ]
  rw [hcirc]
  set x1 := sort (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0
  have hx1_eq : ∀ pos : Fin (arity (ℓ + 1)),
      x1 pos = let t := Ttilde1[pos.1]'(by omega); tRecOf d (arity ℓ) t.1 t.2.1 t.2.2 := by
    let fT : ℕ × ℕ × ℕ → Qubits (wT d) := fun t => tRecOf d (arity ℓ) t.1 t.2.1 t.2.2
    have hL0_eq : List.ofFn x0 = Ttilde0.map fT := by
      refine List.ext_getElem (by simp [hT0_len]) fun i hi1 hi2 => ?_
      have hilt : i < arity (ℓ + 1) := by simpa using hi1
      simp only [List.getElem_ofFn, List.getElem_map]
      exact hT ⟨i, hilt⟩
    have hperm : List.Perm (List.ofFn x1) (Ttilde1.map fT) := by
      have hp1 := br.sort_perm (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0
      have hp2 : List.Perm Ttilde0 Ttilde1 := (List.mergeSort_perm _ _).symm
      rw [hL0_eq] at hp1
      exact hp1.trans (hp2.map fT)
    have hpw1 : (List.ofFn x1).Pairwise (fun a b => bitsToNat (recKey54 a) ≤ bitsToNat (recKey54 b)) := by
      have hm := br.monotone_sort (fun r => bitsToNat (recKey54 r)) (ℓ + 1) x0
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.getElem_ofFn]
      exact hm (Nat.le_of_lt hij)
    have hT0_lt : ∀ t ∈ Ttilde0, t.1 < 2 ^ d ∧ t.2.1 < 2 ^ d := by
      intro t ht
      have har := arity_succ_eq ℓ
      have hprop := comb.Ttilde1_col_lt_iff s lo (lo + arity ℓ) (lo + 2 * arity ℓ)
        (by omega) (by omega) hs t ht
      have hsub1 : arity d = 2 ^ d := arity_eq_two_pow d
      omega
    have hpw2 : (Ttilde1.map fT).Pairwise (fun a b => bitsToNat (recKey54 a) ≤ bitsToNat (recKey54 b)) := by
      rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ (pairwise_le_mergeSort_key (mergePhi (arity ℓ)) Ttilde0)
      intro t₁ t₂ ht₁ ht₂ hle
      have h1 := hT0_lt t₁ ((List.mergeSort_perm _ _).mem_iff.mp ht₁)
      have h2 := hT0_lt t₂ ((List.mergeSort_perm _ _).mem_iff.mp ht₂)
      exact (tRecOf_key_le_iff comb d (arity ℓ) h1.1 h1.2 h2.1 h2.2).mpr hle
    have hinj : ∀ a ∈ Ttilde1.map fT, ∀ c ∈ Ttilde1.map fT,
        bitsToNat (recKey54 a) = bitsToNat (recKey54 c) → a = c := by
      rintro _ ha _ hc heq
      rcases List.mem_map.mp ha with ⟨t₁, ht₁, rfl⟩
      rcases List.mem_map.mp hc with ⟨t₂, ht₂, rfl⟩
      have ht₁0 := (List.mergeSort_perm _ _).mem_iff.mp ht₁
      have ht₂0 := (List.mergeSort_perm _ _).mem_iff.mp ht₂
      have h1 := hT0_lt t₁ ht₁0
      have h2 := hT0_lt t₂ ht₂0
      have hiff12 := tRecOf_key_le_iff comb d (arity ℓ) (c1 := t₁.2.2) (c2 := t₂.2.2) h1.1 h1.2 h2.1 h2.2
      have hiff21 := tRecOf_key_le_iff comb d (arity ℓ) (c1 := t₂.2.2) (c2 := t₁.2.2) h2.1 h2.2 h1.1 h1.2
      dsimp only [fT] at heq
      have hphi : mergePhi (arity ℓ) t₁ = mergePhi (arity ℓ) t₂ :=
        le_antisymm (hiff12.mp (le_of_eq heq)) (hiff21.mp (le_of_eq heq.symm))
      have hfst : t₁.1 = t₂.1 := comb.mergePhi_fst_inj (arity ℓ) t₁ t₂ hphi
      rcases List.getElem_of_mem ht₁0 with ⟨i₁, hi₁, rfl⟩
      rcases List.getElem_of_mem ht₂0 with ⟨i₂, hi₂, rfl⟩
      have hi12 : i₁ = i₂ := by
        simp only [Ttilde0, List.getElem_map, List.getElem_zipIdx, zero_add] at hfst
        exact hfst
      subst hi12
      rfl
    have heq_list := comb.perm_eq_of_sorted_of_inj (fun r => bitsToNat (recKey54 r))
      (List.ofFn x1) (Ttilde1.map fT) hperm hpw1 hpw2 hinj
    intro pos
    have hget := congrArg (fun l : List (Qubits (wT d)) => l[pos.1]?) heq_list
    simp only [List.getElem?_ofFn, pos.isLt, ↓reduceDIte,
      List.getElem?_eq_getElem (show pos.1 < (Ttilde1.map fT).length by rw [List.length_map, hT1_len]; exact pos.isLt),
      Option.some.injEq] at hget
    rw [hget, List.getElem_map]
  congr 1
  dsimp only [sort1Emb]
  refine packAS_eq_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_main]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_R]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_C]
  · change updateOn (packDTA54Emb (prefixRegEmb (tPrefixRange_le d) (arity_succ_le hℓ)) (trPrefEmb br d ℓ hℓ) (saSort1Emb d)
        (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
        (packAS d S) (packDTA54 (arity (ℓ + 1)) (wT d) (sortTraceSize (ℓ + 1)) (d + (1 + d)) x1
          (sortTrace (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0)) ∘
        regEmb (oT d) (arity d) (wT d) (tPrefixRange_le d) = _
    rw [updateOn_packDTA54_prefixReg (tPrefixRange_le d) (arity_succ_le hℓ) (trPrefEmb br d ℓ hℓ)
      (saSort1Emb d) _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (packAS d S) S.T (packAS_T d S)]
    congr 1; funext q; dsimp only
    by_cases hq : q.1 < arity (ℓ + 1)
    · rw [dif_pos hq, dif_pos hq, hx1_eq ⟨q.1, hq⟩]
    · rw [dif_neg hq, dif_neg hq]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_Out]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_B]
  · change updateOn (packDTA54Emb (tPrefEmb d ℓ hℓ)
        ((Fin.castLEEmb (sortTraceSize_mono br (by omega : ℓ + 1 ≤ d))).trans (eTr d))
        (saSort1Emb d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
        (packAS d S) (packDTA54 (arity (ℓ + 1)) (wT d) (sortTraceSize (ℓ + 1)) (d + (1 + d)) x1
          (sortTrace (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0)) ∘ eTr d = _
    exact updateOn_packDTA54_prefixSlice (sortTraceSize_mono br (by omega : ℓ + 1 ≤ d))
      (tPrefEmb d ℓ hℓ) (eTr d) (saSort1Emb d) _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))
      (packAS d S) (packAS_tr1 d S |>.trans htr) x1 _
  · change updateOn (packDTA54Emb (tPrefEmb d ℓ hℓ) (trPrefEmb br d ℓ hℓ)
        ((Fin.castLEEmb (by omega : d + (1 + d) ≤ 2 * d + 1)).trans (eSA d))
        (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
        (packAS d S) (packDTA54 (arity (ℓ + 1)) (wT d) (sortTraceSize (ℓ + 1)) (d + (1 + d)) x1
          (sortTrace (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0)) ∘ eSA d = S.sortAnc
    rw [hsa]
    exact updateOn_packDTA54_prefixAncZero (by omega : d + (1 + d) ≤ 2 * d + 1)
      (tPrefEmb d ℓ hℓ) (trPrefEmb br d ℓ hℓ) (eSA d) _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))
      (packAS d S) (packAS_sortAnc d S |>.trans hsa) x1 _
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_dR]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_flagBit]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tmpD]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_primAnc]

def fwdScanStep (arith : LcgSym54ArithV2) (d ℓ : ℕ) (hℓ : ℓ < d)
    (pos : Fin (arity (ℓ + 1))) : LayeredCircuit (totAS d) :=
  let pos' := liftPos hℓ pos
  let c1 := (arith.copyRegCircuit d).mapWires (combineEmb (tREmb d pos') (outREmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
  let c2 := (arith.copyRegCircuit d).mapWires (combineEmb (tCEmb d pos') (outCEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
  let c3 := (arith.ctrlAddInPlaceMSBCircuit d).mapWires
    (combineEmb (combineEmb (combineEmb (tTagEmb d pos') (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
      (outREmb d pos') (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
      (ePA d) (emb_disjoint_combineEmb (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
        (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
  let c4 := (arith.setConstMSBCircuit 1 1).mapWires (tTagEmb d pos')
  let c5 := (arith.ctrlAddConstInPlaceMSBCircuit d 1).mapWires
    (combineEmb (combineEmb (tTagEmb d pos') (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (ePA d)
      (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
  let c6 := (arith.setConstMSBCircuit 1 1).mapWires (tTagEmb d pos')
  LayeredCircuit.seqList [c1, c2, c3, c4, c5, c6]

lemma fwdScanStep_size (arith : LcgSym54ArithV2) (d ℓ : ℕ) (hℓ : ℓ < d)
    (pos : Fin (arity (ℓ + 1))) :
    (fwdScanStep arith d ℓ hℓ pos).size ≤ 42 * d + 2 := by
  dsimp only [fwdScanStep]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LayeredCircuit.mapWires_size, arith.copyRegCircuit_size, arith.ctrlAddInPlaceMSBCircuit_size]
  have hs4 := arith.setConstMSBCircuit_size 1 1
  have hs5 := arith.ctrlAddConstInPlaceMSBCircuit_size d 1
  omega

lemma fwdScanStep_act (comb : LcgSym54Comb) (arith : LcgSym54ArithV2)
    (d ℓ : ℕ) (hℓ : ℓ < d) (pos : Fin (arity (ℓ + 1))) (S : AsSnap d)
    (hOut0 : S.Out (liftPos hℓ pos) = fun _ => false)
    (hpa : S.primAnc = fun _ => false)
    (tIdx tR tC dRin : ℕ)
    (htR : tR < 2 ^ d) (hdR : dRin < 2 ^ d)
    (hTpos : S.T (liftPos hℓ pos) = tRecOf d (arity ℓ) tIdx tR tC)
    (hDR : S.dR = natToBits d dRin) :
    let pos' := liftPos hℓ pos
    let rOut := if tIdx < arity ℓ then tR + dRin else tR
    let dRout := if tIdx < arity ℓ then dRin else dRin + 1
    act (fwdScanStep arith d ℓ hℓ pos).unitary (ket (packAS d S)) =
      ket (packAS d { S with
        Out := Function.update S.Out pos' (outRecPack d (natToBits d rOut) (natToBits d tC))
        dR := natToBits d dRout }) := by
  intro pos' rOut dRout
  have hTpos' : S.T pos' = tRecOf d (arity ℓ) tIdx tR tC := hTpos
  have hOutZ : S.Out pos' = outRecPack d (fun _ => false) (fun _ => false) := by
    rw [hOut0, outRecPack_zero]
  have h1bit : natToBits 1 1 0 = true := by
    have ht := comb.natToBits_comp_revPerm 1 1 0
    have hr : (0 : Fin 1).rev = 0 := Fin.ext (by omega)
    rw [hr] at ht; simpa using ht
  let S1 : AsSnap d := { S with Out := Function.update S.Out pos' (outRecPack d (natToBits d tR) (fun _ => false)) }
  let S2 : AsSnap d := { S with Out := Function.update S.Out pos' (outRecPack d (natToBits d tR) (natToBits d tC)) }
  let S3 : AsSnap d := { S with Out := Function.update S.Out pos' (outRecPack d (natToBits d rOut) (natToBits d tC)) }
  let kR0 := natToBits d (if tIdx < arity ℓ then tR else tR - (tIdx - arity ℓ))
  let S4 : AsSnap d := { S3 with T := Function.update S.T pos' (tRecPack d kR0 (fun _ => !(decide (tIdx < arity ℓ))) (natToBits d tIdx) (natToBits d tR) (natToBits d tC)) }
  let S5 : AsSnap d := { S4 with dR := natToBits d dRout }
  have hc1 : act ((arith.copyRegCircuit d).mapWires (combineEmb (tREmb d pos') (outREmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary (ket (packAS d S)) =
      ket (packAS d S1) := by
    rw [act_copyRegOn]
    rw [outREmb, updateOn_outField]
    simp only [packAS_field_out_apply, hOutZ, outRecPack_apply_fOutR, tREmb, packAS_field_t_apply,
      hTpos', tRecOf, tRecPack_apply_fTR, Bool.false_xor, update_fOutR]
    rfl
  have hc2 : act ((arith.copyRegCircuit d).mapWires (combineEmb (tCEmb d pos') (outCEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary (ket (packAS d S1)) =
      ket (packAS d S2) := by
    rw [act_copyRegOn]
    rw [outCEmb, updateOn_outField]
    simp only [packAS_field_out_apply, S1, Function.update_self, outRecPack_apply_fOutC,
      tCEmb, packAS_field_t_apply, hTpos', tRecOf, tRecPack_apply_fTC, Bool.false_xor, update_fOutC]
    congr 2; apply AsSnap.ext <;> try rfl
    dsimp only [S1, S2]; rw [Function.update_idem]
  have hc3 : act ((arith.ctrlAddInPlaceMSBCircuit d).mapWires
        (combineEmb (combineEmb (combineEmb (tTagEmb d pos') (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
          (outREmb d pos') (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
          (ePA d) (emb_disjoint_combineEmb (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
            (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))).unitary (ket (packAS d S2)) =
      ket (packAS d S3) := by
    rw [act_ctrlAddInPlaceOn arith (tTagEmb d pos') (eDR d) (outREmb d pos') (ePA d)
      (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))
      (packAS d S2) (by rw [packAS_primAnc, hpa])]
    rw [outREmb, updateOn_outField, tTagEmb, packAS_field_t_apply, packAS_dR, packAS_field_out]
    have hS2Out : S2.Out pos' = outRecPack d (natToBits d tR) (natToBits d tC) := by dsimp [S2]; rw [Function.update_self]
    have hS2T : S2.T pos' = tRecOf d (arity ℓ) tIdx tR tC := hTpos'
    have hS2DR_val : bitsToNat S2.dR = dRin := by
      have h : S2.dR = natToBits d dRin := hDR
      rw [h, comb.bitsToNat_natToBits hdR]
    rw [hS2T, tRecOf, tRecPack_apply_fTTag, hS2DR_val, hS2Out, outRecPack_comp_fOutR,
      comb.bitsToNat_natToBits htR]
    have hrOutBits : (if decide (tIdx < arity ℓ) then natToBits d (dRin + tR) else natToBits d tR) = natToBits d rOut := by
      dsimp only [rOut]; by_cases hlt : tIdx < arity ℓ
      · simp only [hlt, decide_true, ↓reduceIte, Nat.add_comm]
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [hrOutBits, update_fOutR]
    congr 2; apply AsSnap.ext <;> try rfl
    dsimp only [S2, S3]; rw [Function.update_idem]
  have hc4 : act ((arith.setConstMSBCircuit 1 1).mapWires (tTagEmb d pos')).unitary (ket (packAS d S3)) =
      ket (packAS d S4) := by
    rw [act_setConstOn]
    rw [tTagEmb, updateOn_tField]
    simp only [packAS_field_t_apply]
    have hS3T : S3.T pos' = tRecOf d (arity ℓ) tIdx tR tC := hTpos'
    rw [hS3T, tRecOf]
    simp only [tRecPack_apply_fTTag]
    have hx4 : (fun j : Fin 1 => xor (decide (tIdx < arity ℓ)) (natToBits 1 1 j)) = fun _ => !(decide (tIdx < arity ℓ)) := by
      funext j; have hj : j = 0 := Fin.ext (by omega); subst hj; rw [h1bit, Bool.xor_true]
    rw [hx4, update_fTTag]
  have hc5 : act ((arith.ctrlAddConstInPlaceMSBCircuit d 1).mapWires
        (combineEmb (combineEmb (tTagEmb d pos') (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (ePA d)
          (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))).unitary (ket (packAS d S4)) =
      ket (packAS d S5) := by
    rw [act_ctrlAddConstOn arith (tTagEmb d pos') (eDR d) (ePA d)
      (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (packAS d S4) (by rw [packAS_primAnc]; exact hpa),
      updateOn_dR, tTagEmb, packAS_field_t_apply, packAS_dR]
    have hS4tag : S4.T pos' (fTTag d 0) = !(decide (tIdx < arity ℓ)) := by
      dsimp [S4]; rw [Function.update_self, tRecPack_apply_fTTag]
    have hS4dR : S4.dR = natToBits d dRin := hDR
    rw [hS4tag, hS4dR, comb.bitsToNat_natToBits hdR]
    have hmod1 : 1 % 2 ^ d = 1 := Nat.mod_eq_of_lt (by have h2 : 2 ≤ 2 ^ d := Nat.le_self_pow (by omega) 2; omega)
    have hdRoutBits : (if !(decide (tIdx < arity ℓ)) then natToBits d (1 % 2 ^ d + dRin) else natToBits d dRin) =
        natToBits d dRout := by
      dsimp only [dRout]; by_cases hlt : tIdx < arity ℓ
      · simp only [hlt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · simp only [hlt, decide_false, Bool.not_false, ↓reduceIte, hmod1, Nat.add_comm]
    rw [hdRoutBits]
  have hc6 : act ((arith.setConstMSBCircuit 1 1).mapWires (tTagEmb d pos')).unitary (ket (packAS d S5)) =
      ket (packAS d { S with
        Out := Function.update S.Out pos' (outRecPack d (natToBits d rOut) (natToBits d tC))
        dR := natToBits d dRout }) := by
    rw [act_setConstOn]
    rw [tTagEmb, updateOn_tField]
    simp only [packAS_field_t_apply]
    have hS5T : S5.T pos' = tRecPack d kR0 (fun _ => !(decide (tIdx < arity ℓ))) (natToBits d tIdx) (natToBits d tR) (natToBits d tC) := by
      dsimp [S5, S4]; rw [Function.update_self]
    rw [hS5T]
    simp only [tRecPack_apply_fTTag]
    have hx6 : (fun j : Fin 1 => xor (!(decide (tIdx < arity ℓ))) (natToBits 1 1 j)) = fun _ => decide (tIdx < arity ℓ) := by
      funext j; have hj : j = 0 := Fin.ext (by omega); subst hj; rw [h1bit, Bool.xor_true, Bool.not_not]
    rw [hx6, update_fTTag]
    congr 2; apply AsSnap.ext <;> try rfl
    funext q; dsimp only [S5, S4, S3]
    by_cases hq : q = pos'
    · subst hq; rw [Function.update_self, hTpos']; rfl
    · rw [Function.update_of_ne hq, Function.update_of_ne hq]
  dsimp only [fwdScanStep]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, LayeredCircuit.id_unitary, act_mul, act_one]
  rw [hc1, hc2, hc3, hc4, hc5, hc6]

def fwdScan (arith : LcgSym54ArithV2) (d ℓ : ℕ) (hℓ : ℓ < d) : LayeredCircuit (totAS d) :=
  LayeredCircuit.seq
    (LayeredCircuit.seqList ((List.finRange (arity (ℓ + 1))).map (fwdScanStep arith d ℓ hℓ)))
    ((arith.setConstMSBCircuit d (arity ℓ)).mapWires (eDR d))

lemma fwdScan_size (arith : LcgSym54ArithV2) (d ℓ : ℕ) (hℓ : ℓ < d) :
    (fwdScan arith d ℓ hℓ).size ≤ arity (ℓ + 1) * (42 * d + 2) + d := by
  dsimp only [fwdScan]
  rw [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size]
  have h1 := seqList_fin_size_le (fwdScanStep arith d ℓ hℓ) (42 * d + 2) (fwdScanStep_size arith d ℓ hℓ)
  have h2 := arith.setConstMSBCircuit_size d (arity ℓ)
  omega

lemma fwdScan_act (comb : LcgSym54Comb) (arith : LcgSym54ArithV2)
    (s : ℕ → ℕ) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (_hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d)
    (hs : ∀ c, c < b * (2 * arity ℓ) + 2 * arity ℓ → s c ≤ c)
    (S : AsSnap d)
    (hOut : S.Out = fun _ _ => false)
    (hdR : S.dR = fun _ => false)
    (hpa : S.primAnc = fun _ => false)
    (hT : ∀ pos : Fin (arity (ℓ + 1)),
      S.T (liftPos hℓ pos) =
        let L := greedyDiag s (b * (2 * arity ℓ)) (b * (2 * arity ℓ) + arity ℓ)
        let R := greedyDiag s (b * (2 * arity ℓ) + arity ℓ) (b * (2 * arity ℓ) + 2 * arity ℓ)
        let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
        let Ttilde1 := Ttilde0.mergeSort (fun a b => decide (mergePhi (arity ℓ) a ≤ mergePhi (arity ℓ) b))
        let t := Ttilde1[pos.1]'(by rw [ttilde1_length comb s (b * (2 * arity ℓ)) ℓ hs]; exact pos.isLt)
        tRecOf d (arity ℓ) t.1 t.2.1 t.2.2) :
    let lo := b * (2 * arity ℓ)
    let hi := lo + 2 * arity ℓ
    let g := greedyDiag s lo hi
    have hg_len : g.length = arity (ℓ + 1) := by
      have h := comb.greedyDiag_length s lo hi (by omega) (fun c _ hc2 => hs c hc2)
      dsimp only [g, hi, lo] at h ⊢
      rw [arity_succ_eq]; omega
    act (fwdScan arith d ℓ hℓ).unitary (ket (packAS d S)) =
      ket (packAS d { S with
        Out := fun q =>
          if hq : q.1 < arity (ℓ + 1) then
            let p := g[q.1]'(by omega)
            outRecPack d (natToBits d p.1) (natToBits d p.2)
          else fun _ => false }) := by
  intro lo hi g hg_len
  let L := greedyDiag s lo (lo + arity ℓ)
  let R := greedyDiag s (lo + arity ℓ) hi
  let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
  let Ttilde1 := Ttilde0.mergeSort (fun a b => decide (mergePhi (arity ℓ) a ≤ mergePhi (arity ℓ) b))
  have hT0_len : Ttilde0.length = arity (ℓ + 1) := ttilde0_length comb s lo ℓ hs
  have hT1_len : Ttilde1.length = arity (ℓ + 1) := ttilde1_length comb s lo ℓ hs
  have har := arity_succ_eq ℓ
  have hspec := comb.alonsoSchott_merge_spec s lo (lo + arity ℓ) hi (by omega) (by omega) (fun c hc => hs c hc)
  have hsubk : (lo + arity ℓ) - lo = arity ℓ := by omega
  simp only [hsubk] at hspec
  let dRfn : ℕ → ℕ := fun k => ((Ttilde1.take k).filter (fun u => decide (arity ℓ ≤ u.1))).length
  let outAt : ℕ → Qubits (wOut d) := fun q =>
    if hq : q < arity (ℓ + 1) then
      let t := Ttilde1[q]'(by omega)
      let dRq := dRfn q
      outRecPack d (natToBits d (if t.1 < arity ℓ then t.2.1 + dRq else t.2.1)) (natToBits d t.2.2)
    else fun _ => false
  let inv : ℕ → Qubits (totAS d) := fun k =>
    packAS d { S with
      Out := fun q => if q.1 < k then outAt q.1 else fun _ => false
      dR := natToBits d (dRfn k) }
  have hdR_zero : dRfn 0 = 0 := by simp [dRfn]
  have h0 : inv 0 = packAS d S := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    · simp [hOut]
    · simp [hdR, hdR_zero, natToBits_zero comb]
  have hstep : ∀ pos : Fin (arity (ℓ + 1)),
      act (fwdScanStep arith d ℓ hℓ pos).unitary (ket (inv pos.1)) = ket (inv (pos.1 + 1)) := by
    intro pos
    have hpos_T1 : pos.1 < Ttilde1.length := by omega
    let t := Ttilde1[pos.1]'hpos_T1
    have ht_mem : t ∈ Ttilde0 := (List.mergeSort_perm _ _).mem_iff.mp (List.getElem_mem hpos_T1)
    have hbounds := comb.Ttilde1_col_lt_iff s lo (lo + arity ℓ) hi (by omega) (by omega)
      (fun c hc => hs c hc) t ht_mem
    have hpow : arity d = 2 ^ d := arity_eq_two_pow d
    have htR_lt : t.2.1 < 2 ^ d := by omega
    have hdR_lt : dRfn pos.1 < 2 ^ d := by
      have h1 : dRfn pos.1 ≤ (Ttilde1.take pos.1).length := List.length_filter_le _ _
      have h2 : (Ttilde1.take pos.1).length ≤ pos.1 := List.length_take_le _ _
      have h3 := pos.isLt
      have h4 := arity_succ_le hℓ
      omega
    have hstep1 := fwdScanStep_act comb arith d ℓ hℓ pos
      { S with
        Out := fun q => if q.1 < pos.1 then outAt q.1 else fun _ => false
        dR := natToBits d (dRfn pos.1) }
      (by simp [liftPos]) hpa t.1 t.2.1 t.2.2 (dRfn pos.1) htR_lt hdR_lt
      (hT pos) rfl
    dsimp only [inv] at hstep1 ⊢
    rw [hstep1]
    have hdR_succ : dRfn (pos.1 + 1) = if t.1 < arity ℓ then dRfn pos.1 else dRfn pos.1 + 1 := by
      dsimp only [dRfn]
      rw [List.take_add_one, List.getElem?_eq_getElem hpos_T1, Option.toList_some, List.filter_append, List.length_append]
      by_cases hlt : t.1 < arity ℓ
      · have hdec : decide (arity ℓ ≤ (Ttilde1[pos.1]'hpos_T1).1) = false := decide_eq_false (show ¬ arity ℓ ≤ t.1 by omega)
        rw [if_pos hlt, List.filter_singleton, hdec]; rfl
      · have hdec : decide (arity ℓ ≤ (Ttilde1[pos.1]'hpos_T1).1) = true := decide_eq_true (show arity ℓ ≤ t.1 by omega)
        rw [if_neg hlt, List.filter_singleton, hdec]; rfl
    congr 2; apply AsSnap.ext <;> try rfl
    · funext q; dsimp only
      by_cases hq : q = liftPos hℓ pos
      · subst hq
        rw [Function.update_self,
          if_pos (show (liftPos hℓ pos).1 < pos.1 + 1 by dsimp only [liftPos]; exact Nat.lt_succ_self pos.1)]
        dsimp only [outAt]
        rw [dif_pos (show (liftPos hℓ pos).1 < arity (ℓ + 1) by dsimp only [liftPos]; exact pos.isLt)]; rfl
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ pos.1 := fun h => hq (Fin.ext h)
        by_cases hqp : q.1 < pos.1
        · have hqp1 : q.1 < pos.1 + 1 := by omega
          rw [if_pos hqp, if_pos hqp1]
        · have hnqp1 : ¬ q.1 < pos.1 + 1 := by omega
          rw [if_neg hqp, if_neg hnqp1]
    · rw [hdR_succ]
  have hseq := act_seqList_fin (fwdScanStep arith d ℓ hℓ) inv hstep
  rw [h0] at hseq
  dsimp only [fwdScan]
  rw [LayeredCircuit.seq_unitary, act_mul, hseq]
  have hdR_end : dRfn (arity (ℓ + 1)) = arity ℓ := by
    dsimp only [dRfn]
    rw [← hT1_len, List.take_length]
    have hperm_f : List.Perm (Ttilde1.filter (fun u => decide (arity ℓ ≤ u.1)))
        (Ttilde0.filter (fun u => decide (arity ℓ ≤ u.1))) :=
      (List.mergeSort_perm _ _).filter _
    rw [hperm_f.length_eq]
    have hmap : Ttilde0.map Prod.fst = List.range (arity (ℓ + 1)) := by
      refine List.ext_getElem (by simp [hT0_len]) fun i hi1 hi2 => ?_
      simp [Ttilde0]
    have hfilt : (Ttilde0.filter (fun u => decide (arity ℓ ≤ u.1))).map Prod.fst =
        (List.range (arity (ℓ + 1))).filter (fun idx => decide (arity ℓ ≤ idx)) := by
      rw [← hmap]; conv_rhs => rw [List.filter_map]
      rfl
    rw [← List.length_map Prod.fst, hfilt]
    have ha2 : arity (ℓ + 1) = arity ℓ + arity ℓ := by rw [arity_succ_eq, Nat.two_mul]
    rw [ha2, List.range_add, List.filter_append]
    have hL0 : ((List.range (arity ℓ)).filter (fun idx => decide (arity ℓ ≤ idx))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx; rw [List.mem_range] at hx; simp only [decide_eq_true_eq]; omega
    have hR0 : (((List.range (arity ℓ)).map (arity ℓ + ·)).filter (fun idx => decide (arity ℓ ≤ idx))) =
        (List.range (arity ℓ)).map (arity ℓ + ·) := by
      rw [List.filter_eq_self]
      intro x hx; rcases List.mem_map.mp hx with ⟨j, _, rfl⟩; simp
    rw [hL0, hR0, List.nil_append, List.length_map, List.length_range]
  rw [act_setConstOn, updateOn_dR]
  dsimp only [inv]
  have hx0 : (fun j => xor (packAS d { S with
      Out := fun q => if q.1 < arity (ℓ + 1) then outAt q.1 else fun _ => false
      dR := natToBits d (dRfn (arity (ℓ + 1))) } (eDR d j)) (natToBits d (arity ℓ) j)) = fun _ => false := by
    funext j; simp only [packAS_dR_apply]; rw [hdR_end, Bool.xor_self]
  rw [hx0]
  have hout_eq : (fun q : Fin (arity d) => if q.1 < arity (ℓ + 1) then outAt q.1 else fun _ => false) =
      (fun q : Fin (arity d) =>
        if hq : q.1 < arity (ℓ + 1) then
          let p := g[q.1]'(by omega)
          outRecPack d (natToBits d p.1) (natToBits d p.2)
        else fun _ => false) := by
    funext q
    by_cases hq : q.1 < arity (ℓ + 1)
    · rw [if_pos hq, dif_pos hq]
      dsimp only [outAt]
      rw [dif_pos hq]
      have hq_T1 : q.1 < Ttilde1.length := by rw [hT1_len]; exact hq
      let t := Ttilde1[q.1]'hq_T1
      have hg1 : ((if t.1 < arity ℓ then t.2.1 + dRfn q.1 else t.2.1, t.2.2) : ℕ × ℕ) =
          g[q.1]'(by rw [hg_len]; exact hq) := by
        have hmap_eq := hspec.2.2
        have hidx_g : q.1 < g.length := by rw [hg_len]; exact hq
        have hget := congrArg (fun l : List (ℕ × ℕ) => l[q.1]?) hmap_eq
        rw [List.getElem?_eq_getElem hidx_g,
          List.getElem?_eq_getElem (by
            rw [List.length_map, List.length_finRange, (List.mergeSort_perm _ _).length_eq]
            change q.1 < Ttilde0.length
            rw [hT0_len]; exact hq)] at hget
        simp only [List.getElem_map, List.getElem_finRange, Option.some.injEq] at hget
        exact hget
      have hg1_fst : (if t.1 < arity ℓ then t.2.1 + dRfn q.1 else t.2.1) = (g[q.1]'(by rw [hg_len]; exact hq)).1 :=
        congrArg Prod.fst hg1
      have hg1_snd : t.2.2 = (g[q.1]'(by rw [hg_len]; exact hq)).2 := by
        have h := congrArg Prod.snd hg1
        dsimp only at h
        exact h
      change outRecPack d (natToBits d (if t.1 < arity ℓ then t.2.1 + dRfn q.1 else t.2.1)) (natToBits d t.2.2) = _
      rw [hg1_fst, hg1_snd]
    · rw [if_neg hq, dif_neg hq]
  rw [hout_eq]
  congr 2; apply AsSnap.ext <;> try rfl
  exact hdR.symm

/-! ### Part 7: `revScan`, `Sort 2`, `clearRC`, `swapOutRC`, and `asMergeBlock` -/

def revScanStep (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (pos : Fin (arity (ℓ + 1))) : LayeredCircuit (totAS d) :=
  let lo := b * (2 * arity ℓ)
  let pos' := liftPos hℓ pos
  let c1 := (arith.ltConstMSBCircuit d (lo + arity ℓ)).mapWires
    (combineEmb (combineEmb (outCEmb d pos') (eFlag d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (eTmp d)
      (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
  let c2 := (arith.copyRegCircuit d).mapWires (combineEmb (outCEmb d pos') (bCEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
  let c3 := (arith.copyRegCircuit d).mapWires (combineEmb (outREmb d pos') (bREmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
  let c4 := (arith.ctrlSubInPlaceMSBCircuit d).mapWires
    (combineEmb (combineEmb (combineEmb (eFlag d) (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
      (bREmb d pos') (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
      (ePA d) (emb_disjoint_combineEmb (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
        (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
  let c5 := (arith.ctrlConstXorMSBCircuit d pos.1).mapWires (combineEmb (eFlag d) (bIdxEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
  let c6 := (arith.ctrlSubInPlaceMSBCircuit d).mapWires
    (combineEmb (combineEmb (combineEmb (eFlag d) (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
      (bIdxEmb d pos') (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
      (ePA d) (emb_disjoint_combineEmb (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
        (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
  let c7 := (arith.setConstMSBCircuit 1 1).mapWires (eFlag d)
  let c8 := (arith.ctrlConstXorMSBCircuit d (arity ℓ)).mapWires (combineEmb (eFlag d) (bIdxEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
  let c9 := (arith.ctrlAddInPlaceMSBCircuit d).mapWires
    (combineEmb (combineEmb (combineEmb (eFlag d) (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
      (bIdxEmb d pos') (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
      (ePA d) (emb_disjoint_combineEmb (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
        (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
  let c10 := (arith.ctrlAddConstInPlaceMSBCircuit d 1).mapWires
    (combineEmb (combineEmb (eFlag d) (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (ePA d)
      (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
  let c11 := (arith.setConstMSBCircuit 1 1).mapWires (eFlag d)
  LayeredCircuit.seqList [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c1]

lemma revScanStep_size (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (pos : Fin (arity (ℓ + 1))) :
    (revScanStep arith d ℓ b hℓ pos).size ≤ 132 * d + 4 := by
  dsimp only [revScanStep]
  simp only [LayeredCircuit.seqList_size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LayeredCircuit.mapWires_size, arith.copyRegCircuit_size, arith.ctrlSubInPlaceMSBCircuit_size,
    arith.ctrlAddInPlaceMSBCircuit_size]
  have hs1 := arith.ltConstMSBCircuit_size d (b * (2 * arity ℓ) + arity ℓ)
  have hs5 := arith.ctrlConstXorMSBCircuit_size d pos.1
  have hs7 := arith.setConstMSBCircuit_size 1 1
  have hs8 := arith.ctrlConstXorMSBCircuit_size d (arity ℓ)
  have hs10 := arith.ctrlAddConstInPlaceMSBCircuit_size d 1
  omega

lemma revScanStep_act (comb : LcgSym54Comb) (arith : LcgSym54ArithV2)
    (d ℓ b : ℕ) (hℓ : ℓ < d) (pos : Fin (arity (ℓ + 1))) (S : AsSnap d)
    (hBpos : S.B (liftPos hℓ pos) = fun _ => false)
    (hflag : S.flagBit = fun _ => false)
    (htmp : S.tmpD = fun _ => false)
    (hpa : S.primAnc = fun _ => false)
    (tIdx tR tC rOut dRin : ℕ)
    (hrOut_lt : rOut < 2 ^ d) (htC_lt : tC < 2 ^ d) (hdR_lt : dRin < 2 ^ d)
    (hpos_lt : pos.1 < 2 ^ d)
    (hOutpos : S.Out (liftPos hℓ pos) = outRecPack d (natToBits d rOut) (natToBits d tC))
    (hDR : S.dR = natToBits d dRin)
    (hBranchL : tIdx < arity ℓ → rOut = tR + dRin ∧ tIdx = pos.1 - dRin ∧ dRin ≤ pos.1)
    (hBranchR : arity ℓ ≤ tIdx → rOut = tR ∧ tIdx = arity ℓ + dRin)
    (hColIff : tIdx < arity ℓ ↔ tC < b * (2 * arity ℓ) + arity ℓ) :
    let pos' := liftPos hℓ pos
    let dRout := if tIdx < arity ℓ then dRin else dRin + 1
    act (revScanStep arith d ℓ b hℓ pos).unitary (ket (packAS d S)) =
      ket (packAS d { S with
        B := Function.update S.B pos' (bRecPack d (natToBits d tIdx) (natToBits d tR) (natToBits d tC))
        dR := natToBits d dRout }) := by
  intro pos' dRout
  have hOutpos' : S.Out pos' = outRecPack d (natToBits d rOut) (natToBits d tC) := hOutpos
  have hBZ : S.B pos' = bRecPack d (fun _ => false) (fun _ => false) (fun _ => false) := by
    rw [hBpos, bRecPack_zero]
  have h1bit : natToBits 1 1 0 = true := by
    have ht := comb.natToBits_comp_revPerm 1 1 0
    have hr : (0 : Fin 1).rev = 0 := Fin.ext (by omega)
    rw [hr] at ht; simpa using ht
  let lo := b * (2 * arity ℓ)
  let bFlag : Qubits 1 := fun _ => decide (tIdx < arity ℓ)
  have hltDec : decide (tC < lo + arity ℓ) = decide (tIdx < arity ℓ) := by
    dsimp only [lo]
    by_cases h : tIdx < arity ℓ
    · have hc := hColIff.mp h; rw [decide_eq_true h, decide_eq_true hc]
    · have hc : ¬ tC < b * (2 * arity ℓ) + arity ℓ := fun hc => h (hColIff.mpr hc)
      rw [decide_eq_false h, decide_eq_false hc]
  dsimp only [revScanStep]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, LayeredCircuit.id_unitary, act_mul, act_one]
  let S1 : AsSnap d := { S with flagBit := bFlag }
  let S2 : AsSnap d := { S1 with B := Function.update S.B pos' (bRecPack d (fun _ => false) (fun _ => false) (natToBits d tC)) }
  let S3 : AsSnap d := { S1 with B := Function.update S.B pos' (bRecPack d (fun _ => false) (natToBits d rOut) (natToBits d tC)) }
  let S4 : AsSnap d := { S1 with B := Function.update S.B pos' (bRecPack d (fun _ => false) (natToBits d tR) (natToBits d tC)) }
  let idx5 : Qubits d := if tIdx < arity ℓ then natToBits d pos.1 else fun _ => false
  let S5 : AsSnap d := { S1 with B := Function.update S.B pos' (bRecPack d idx5 (natToBits d tR) (natToBits d tC)) }
  let idx6 : Qubits d := if tIdx < arity ℓ then natToBits d tIdx else fun _ => false
  let S6 : AsSnap d := { S1 with B := Function.update S.B pos' (bRecPack d idx6 (natToBits d tR) (natToBits d tC)) }
  let S7 : AsSnap d := { S6 with flagBit := fun _ => !(decide (tIdx < arity ℓ)) }
  let idx8 : Qubits d := if tIdx < arity ℓ then natToBits d tIdx else natToBits d (arity ℓ)
  let S8 : AsSnap d := { S7 with B := Function.update S.B pos' (bRecPack d idx8 (natToBits d tR) (natToBits d tC)) }
  let S9 : AsSnap d := { S7 with B := Function.update S.B pos' (bRecPack d (natToBits d tIdx) (natToBits d tR) (natToBits d tC)) }
  let S10 : AsSnap d := { S9 with dR := natToBits d dRout }
  let S11 : AsSnap d := { S10 with flagBit := bFlag }
  have hc1 : act ((arith.ltConstMSBCircuit d (b * (2 * arity ℓ) + arity ℓ)).mapWires
        (combineEmb (combineEmb (outCEmb d pos') (eFlag d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (eTmp d)
          (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))).unitary (ket (packAS d S)) =
      ket (packAS d S1) := by
    rw [act_ltConstOn arith (outCEmb d pos') (eFlag d) (eTmp d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))
      (packAS d S) (by rw [packAS_tmpD, htmp])]
    rw [updateOn_flagBit, packAS_flagBit_apply, hflag]
    have hS_outC : bitsToNat (packAS d S ∘ outCEmb d pos') = tC := by
      rw [outCEmb, packAS_field_out, hOutpos', outRecPack_comp_fOutC, comb.bitsToNat_natToBits htC_lt]
    rw [hS_outC]
    have hx1 : (fun _ : Fin 1 => xor false (decide (tC < b * (2 * arity ℓ) + arity ℓ))) = bFlag := by
      funext _; rw [Bool.false_xor, hltDec]
    rw [hx1]
  have hc2 : act ((arith.copyRegCircuit d).mapWires (combineEmb (outCEmb d pos') (bCEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary
        (ket (packAS d S1)) = ket (packAS d S2) := by
    rw [act_copyRegOn]
    rw [bCEmb, updateOn_bField]
    simp only [packAS_field_b_apply, S1, hBZ, bRecPack_apply_fBC, outCEmb, packAS_field_out_apply,
      hOutpos', outRecPack_apply_fOutC, Bool.false_xor, update_fBC]
    rfl
  have hc3 : act ((arith.copyRegCircuit d).mapWires (combineEmb (outREmb d pos') (bREmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary
        (ket (packAS d S2)) = ket (packAS d S3) := by
    rw [act_copyRegOn]
    rw [bREmb, updateOn_bField]
    simp only [packAS_field_b_apply, S2, S1, Function.update_self, bRecPack_apply_fBR, outREmb, packAS_field_out_apply,
      hOutpos', outRecPack_apply_fOutR, Bool.false_xor, update_fBR]
    congr 2; apply AsSnap.ext <;> try rfl
    dsimp only [S2, S3]; rw [Function.update_idem]
  have hc4 : act ((arith.ctrlSubInPlaceMSBCircuit d).mapWires
        (combineEmb (combineEmb (combineEmb (eFlag d) (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
          (bREmb d pos') (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
          (ePA d) (emb_disjoint_combineEmb (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
            (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))).unitary
        (ket (packAS d S3)) = ket (packAS d S4) := by
    rw [act_ctrlSubInPlaceOn arith (eFlag d) (eDR d) (bREmb d pos') (ePA d)
      (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))
      (packAS d S3) (by rw [packAS_primAnc]; exact hpa)]
    rw [bREmb, updateOn_bField, packAS_flagBit_apply, packAS_dR, packAS_field_b]
    have hS3flag : S3.flagBit 0 = decide (tIdx < arity ℓ) := rfl
    have hS3B : S3.B pos' = bRecPack d (fun _ => false) (natToBits d rOut) (natToBits d tC) := by
      dsimp only [S3]; rw [Function.update_self]
    have hS3dR_val : bitsToNat S3.dR = dRin := by
      have h : S3.dR = natToBits d dRin := hDR
      rw [h, comb.bitsToNat_natToBits hdR_lt]
    rw [hS3flag, hS3dR_val, hS3B, bRecPack_comp_fBR, comb.bitsToNat_natToBits hrOut_lt]
    have hBrBits : (if decide (tIdx < arity ℓ) then natToBits d (2 ^ d + rOut - dRin) else natToBits d rOut) =
        natToBits d tR := by
      by_cases hlt : tIdx < arity ℓ
      · rcases hBranchL hlt with ⟨hr, _, _⟩
        have heq : 2 ^ d + rOut - dRin = 2 ^ d + tR := by omega
        rw [if_pos (decide_eq_true hlt), heq, natToBits_add_two_pow comb]
      · rcases hBranchR (Nat.le_of_not_lt hlt) with ⟨hr, _⟩
        rw [if_neg (by simpa using hlt), hr]
    rw [hBrBits, update_fBR]
    congr 2; apply AsSnap.ext <;> try rfl
    dsimp only [S3, S4]; rw [Function.update_idem]
  have hc5 : act ((arith.ctrlConstXorMSBCircuit d pos.1).mapWires (combineEmb (eFlag d) (bIdxEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary
        (ket (packAS d S4)) = ket (packAS d S5) := by
    rw [act_ctrlConstXorOn]
    rw [bIdxEmb, updateOn_bField, packAS_flagBit_apply]
    simp only [packAS_field_b, packAS_field_b_apply, S4, Function.update_self,
      bRecPack_comp_fBIdx, bRecPack_apply_fBIdx]
    have hS4flag : S4.flagBit 0 = decide (tIdx < arity ℓ) := rfl
    rw [hS4flag]
    have hidx5' : (if decide (tIdx < arity ℓ) then fun j => xor false (natToBits d pos.1 j) else fun _ => false) = idx5 := by
      dsimp only [idx5]; by_cases hlt : tIdx < arity ℓ
      · rw [if_pos (decide_eq_true hlt), if_pos hlt]; funext _; exact Bool.false_xor _
      · rw [if_neg (by simpa using hlt), if_neg hlt]
    rw [hidx5', update_fBIdx]
    congr 2; apply AsSnap.ext <;> try rfl
    dsimp only [S4, S5]; rw [Function.update_idem]
  have hc6 : act ((arith.ctrlSubInPlaceMSBCircuit d).mapWires
        (combineEmb (combineEmb (combineEmb (eFlag d) (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
          (bIdxEmb d pos') (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
          (ePA d) (emb_disjoint_combineEmb (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
            (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))).unitary
        (ket (packAS d S5)) = ket (packAS d S6) := by
    rw [act_ctrlSubInPlaceOn arith (eFlag d) (eDR d) (bIdxEmb d pos') (ePA d)
      (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))
      (packAS d S5) (by rw [packAS_primAnc]; exact hpa)]
    rw [bIdxEmb, updateOn_bField, packAS_flagBit_apply, packAS_dR, packAS_field_b]
    have hS5flag : S5.flagBit 0 = decide (tIdx < arity ℓ) := rfl
    have hS5B : S5.B pos' = bRecPack d idx5 (natToBits d tR) (natToBits d tC) := by
      dsimp only [S5]; rw [Function.update_self]
    have hS5dR_val : bitsToNat S5.dR = dRin := by
      have h : S5.dR = natToBits d dRin := hDR
      rw [h, comb.bitsToNat_natToBits hdR_lt]
    rw [hS5flag, hS5dR_val, hS5B, bRecPack_comp_fBIdx]
    have hidx6 : (if decide (tIdx < arity ℓ) then natToBits d (2 ^ d + bitsToNat idx5 - dRin) else idx5) =
        idx6 := by
      dsimp only [idx5, idx6]
      by_cases hlt : tIdx < arity ℓ
      · rcases hBranchL hlt with ⟨_, ht1, hdle⟩
        rw [if_pos (decide_eq_true hlt), if_pos hlt, if_pos hlt, comb.bitsToNat_natToBits hpos_lt]
        have heq : 2 ^ d + pos.1 - dRin = 2 ^ d + tIdx := by omega
        rw [heq, natToBits_add_two_pow comb]
      · rw [if_neg (by simpa using hlt), if_neg hlt, if_neg hlt]
    rw [hidx6, update_fBIdx]
    congr 2; apply AsSnap.ext <;> try rfl
    dsimp only [S5, S6]; rw [Function.update_idem]
  have hc7 : act ((arith.setConstMSBCircuit 1 1).mapWires (eFlag d)).unitary (ket (packAS d S6)) =
      ket (packAS d S7) := by
    rw [act_setConstOn, updateOn_flagBit]
    have hx7 : (fun j : Fin 1 => xor (packAS d S6 (eFlag d j)) (natToBits 1 1 j)) = fun _ => !(decide (tIdx < arity ℓ)) := by
      funext j; have hj : j = 0 := Fin.ext (by omega); subst hj
      simp only [packAS_flagBit_apply]; dsimp only [S6, S1, bFlag]; rw [h1bit, Bool.xor_true]
    rw [hx7]
  have hc8 : act ((arith.ctrlConstXorMSBCircuit d (arity ℓ)).mapWires (combineEmb (eFlag d) (bIdxEmb d pos') (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary
        (ket (packAS d S7)) = ket (packAS d S8) := by
    rw [act_ctrlConstXorOn]
    rw [bIdxEmb, updateOn_bField, packAS_flagBit_apply]
    have hS7flag : S7.flagBit 0 = !(decide (tIdx < arity ℓ)) := rfl
    have hS7B : S7.B pos' = bRecPack d idx6 (natToBits d tR) (natToBits d tC) := by
      dsimp only [S7, S6]; rw [Function.update_self]
    simp only [packAS_field_b, packAS_field_b_apply, hS7flag, hS7B,
      bRecPack_comp_fBIdx, bRecPack_apply_fBIdx]
    have hidx8 : (if !(decide (tIdx < arity ℓ)) then fun j => xor (idx6 j) (natToBits d (arity ℓ) j) else idx6) = idx8 := by
      dsimp only [idx6, idx8]
      by_cases hlt : tIdx < arity ℓ
      · rw [if_neg (by rw [decide_eq_true hlt]; decide), if_pos hlt, if_pos hlt]
      · rw [if_pos (by rw [decide_eq_false hlt]; rfl), if_neg hlt, if_neg hlt]
        funext _; exact Bool.false_xor _
    rw [hidx8, update_fBIdx]
    congr 2; apply AsSnap.ext <;> try rfl
    dsimp only [S7, S6, S8]; rw [Function.update_idem]
  have hc9 : act ((arith.ctrlAddInPlaceMSBCircuit d).mapWires
        (combineEmb (combineEmb (combineEmb (eFlag d) (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
          (bIdxEmb d pos') (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
          (ePA d) (emb_disjoint_combineEmb (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
            (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))).unitary
        (ket (packAS d S8)) = ket (packAS d S9) := by
    rw [act_ctrlAddInPlaceOn arith (eFlag d) (eDR d) (bIdxEmb d pos') (ePA d)
      (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))
      (packAS d S8) (by rw [packAS_primAnc]; exact hpa)]
    rw [bIdxEmb, updateOn_bField, packAS_flagBit_apply, packAS_dR, packAS_field_b]
    have hS8flag : S8.flagBit 0 = !(decide (tIdx < arity ℓ)) := rfl
    have hS8B : S8.B pos' = bRecPack d idx8 (natToBits d tR) (natToBits d tC) := by
      dsimp only [S8]; rw [Function.update_self]
    have hS8dR_val : bitsToNat S8.dR = dRin := by
      have h : S8.dR = natToBits d dRin := hDR
      rw [h, comb.bitsToNat_natToBits hdR_lt]
    rw [hS8flag, hS8dR_val, hS8B, bRecPack_comp_fBIdx]
    have ha_lt : arity ℓ < 2 ^ d := by
      have hpow : arity ℓ < arity d := by simp only [arity_eq_two_pow]; exact Nat.pow_lt_pow_right (by norm_num) hℓ
      simpa [arity_eq_two_pow] using hpow
    have hidx9 : (if !(decide (tIdx < arity ℓ)) then
        natToBits d (dRin + bitsToNat idx8) else idx8) = natToBits d tIdx := by
      dsimp only [idx8]
      by_cases hlt : tIdx < arity ℓ
      · rw [if_neg (by rw [decide_eq_true hlt]; decide), if_pos hlt]
      · rcases hBranchR (Nat.le_of_not_lt hlt) with ⟨_, ht1⟩
        rw [if_pos (by rw [decide_eq_false hlt]; rfl), if_neg hlt,
          comb.bitsToNat_natToBits ha_lt, ht1, Nat.add_comm]
    rw [hidx9, update_fBIdx]
    congr 2; apply AsSnap.ext <;> try rfl
    dsimp only [S8, S7, S6, S9]; rw [Function.update_idem]
  have hc10 : act ((arith.ctrlAddConstInPlaceMSBCircuit d 1).mapWires
        (combineEmb (combineEmb (eFlag d) (eDR d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (ePA d)
          (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))).unitary
        (ket (packAS d S9)) = ket (packAS d S10) := by
    rw [act_ctrlAddConstOn arith (eFlag d) (eDR d) (ePA d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))
      (packAS d S9) (by rw [packAS_primAnc]; exact hpa), updateOn_dR, packAS_flagBit_apply, packAS_dR]
    have hS9flag : S9.flagBit 0 = !(decide (tIdx < arity ℓ)) := rfl
    have hS9dR : S9.dR = natToBits d dRin := hDR
    rw [hS9flag, hS9dR, comb.bitsToNat_natToBits hdR_lt]
    have hmod1 : 1 % 2 ^ d = 1 := Nat.mod_eq_of_lt (by have h2 : 2 ≤ 2 ^ d := Nat.le_self_pow (by omega) 2; omega)
    have hdRoutBits : (if !(decide (tIdx < arity ℓ)) then natToBits d (1 % 2 ^ d + dRin) else natToBits d dRin) =
        natToBits d dRout := by
      dsimp only [dRout]; by_cases hlt : tIdx < arity ℓ
      · rw [if_neg (by rw [decide_eq_true hlt]; decide), if_pos hlt]
      · rw [if_pos (by rw [decide_eq_false hlt]; rfl), if_neg hlt, hmod1, Nat.add_comm]
    rw [hdRoutBits]
  have hc11 : act ((arith.setConstMSBCircuit 1 1).mapWires (eFlag d)).unitary (ket (packAS d S10)) =
      ket (packAS d S11) := by
    rw [act_setConstOn, updateOn_flagBit]
    have hx11 : (fun j : Fin 1 => xor (packAS d S10 (eFlag d j)) (natToBits 1 1 j)) = bFlag := by
      funext j; have hj : j = 0 := Fin.ext (by omega); subst hj
      simp only [packAS_flagBit_apply]; dsimp only [S10, S9, S7, bFlag]; rw [h1bit, Bool.xor_true, Bool.not_not]
    rw [hx11]
  have hc12 : act ((arith.ltConstMSBCircuit d (b * (2 * arity ℓ) + arity ℓ)).mapWires
        (combineEmb (combineEmb (outCEmb d pos') (eFlag d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))) (eTmp d)
          (emb_disjoint_combineEmb (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))).unitary (ket (packAS d S11)) =
      ket (packAS d { S with
        B := Function.update S.B pos' (bRecPack d (natToBits d tIdx) (natToBits d tR) (natToBits d tC))
        dR := natToBits d dRout }) := by
    rw [act_ltConstOn arith (outCEmb d pos') (eFlag d) (eTmp d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))
      (packAS d S11) (by rw [packAS_tmpD]; exact htmp),
      updateOn_flagBit, packAS_flagBit_apply]
    have hS11flag : S11.flagBit 0 = decide (tIdx < arity ℓ) := rfl
    have hS11_outC : bitsToNat (packAS d S11 ∘ outCEmb d pos') = tC := by
      rw [outCEmb, packAS_field_out,
        show S11.Out pos' = outRecPack d (natToBits d rOut) (natToBits d tC) from hOutpos',
        outRecPack_comp_fOutC, comb.bitsToNat_natToBits htC_lt]
    rw [hS11flag, hS11_outC]
    have hx12 : (fun _ : Fin 1 => xor (decide (tIdx < arity ℓ)) (decide (tC < b * (2 * arity ℓ) + arity ℓ))) = fun _ => false := by
      funext _; rw [show decide (tC < b * (2 * arity ℓ) + arity ℓ) = decide (tIdx < arity ℓ) from hltDec, Bool.xor_self]
    rw [hx12]
    congr 2; apply AsSnap.ext <;> try rfl
    exact hflag.symm
  rw [hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12]

def revScan (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d) : LayeredCircuit (totAS d) :=
  LayeredCircuit.seq
    (LayeredCircuit.seqList ((List.finRange (arity (ℓ + 1))).map (revScanStep arith d ℓ b hℓ)))
    ((arith.setConstMSBCircuit d (arity ℓ)).mapWires (eDR d))

lemma revScan_size (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d) :
    (revScan arith d ℓ b hℓ).size ≤ arity (ℓ + 1) * (132 * d + 4) + d := by
  dsimp only [revScan]
  rw [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size]
  have h1 := seqList_fin_size_le (revScanStep arith d ℓ b hℓ) (132 * d + 4) (revScanStep_size arith d ℓ b hℓ)
  have h2 := arith.setConstMSBCircuit_size d (arity ℓ)
  omega

lemma revScan_act (comb : LcgSym54Comb) (arith : LcgSym54ArithV2)
    (s : ℕ → ℕ) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (_hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d)
    (hs : ∀ c, c < b * (2 * arity ℓ) + 2 * arity ℓ → s c ≤ c)
    (S : AsSnap d)
    (hB : S.B = fun _ _ => false)
    (hdR : S.dR = fun _ => false)
    (hflag : S.flagBit = fun _ => false)
    (htmp : S.tmpD = fun _ => false)
    (hpa : S.primAnc = fun _ => false)
    (hOut : ∀ pos : Fin (arity (ℓ + 1)),
      S.Out (liftPos hℓ pos) =
        let p := (greedyDiag s (b * (2 * arity ℓ)) (b * (2 * arity ℓ) + 2 * arity ℓ))[pos.1]'(by
          have h := comb.greedyDiag_length s (b * (2 * arity ℓ)) (b * (2 * arity ℓ) + 2 * arity ℓ)
            (by omega) (fun c _ hc2 => hs c hc2)
          have har := arity_succ_eq ℓ; have := pos.isLt; omega)
        outRecPack d (natToBits d p.1) (natToBits d p.2)) :
    let lo := b * (2 * arity ℓ)
    let hi := lo + 2 * arity ℓ
    let L := greedyDiag s lo (lo + arity ℓ)
    let R := greedyDiag s (lo + arity ℓ) hi
    let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
    let Ttilde1 := Ttilde0.mergeSort (fun a b => decide (mergePhi (arity ℓ) a ≤ mergePhi (arity ℓ) b))
    act (revScan arith d ℓ b hℓ).unitary (ket (packAS d S)) =
      ket (packAS d { S with
        B := fun q =>
          if hq : q.1 < arity (ℓ + 1) then
            let t := Ttilde1[q.1]'(by rw [ttilde1_length comb s lo ℓ hs]; exact hq)
            bRecPack d (natToBits d t.1) (natToBits d t.2.1) (natToBits d t.2.2)
          else fun _ => false }) := by
  intro lo hi L R Ttilde0 Ttilde1
  have hT0_len : Ttilde0.length = arity (ℓ + 1) := ttilde0_length comb s lo ℓ hs
  have hT1_len : Ttilde1.length = arity (ℓ + 1) := ttilde1_length comb s lo ℓ hs
  have har := arity_succ_eq ℓ
  have hspec := comb.alonsoSchott_merge_spec s lo (lo + arity ℓ) hi (by omega) (by omega) (fun c hc => hs c hc)
  have hsubk : (lo + arity ℓ) - lo = arity ℓ := by omega
  simp only [hsubk] at hspec
  let g := greedyDiag s lo hi
  have hg_len : g.length = arity (ℓ + 1) := by
    have h := comb.greedyDiag_length s lo hi (by omega) (fun c _ hc2 => hs c hc2)
    dsimp only [g, hi, lo] at h ⊢
    omega
  let dRfn : ℕ → ℕ := fun k => ((Ttilde1.take k).filter (fun u => decide (arity ℓ ≤ u.1))).length
  let bAt : ℕ → Qubits (wB d) := fun q =>
    if hq : q < arity (ℓ + 1) then
      let t := Ttilde1[q]'(by omega)
      bRecPack d (natToBits d t.1) (natToBits d t.2.1) (natToBits d t.2.2)
    else fun _ => false
  let inv : ℕ → Qubits (totAS d) := fun k =>
    packAS d { S with
      B := fun q => if q.1 < k then bAt q.1 else fun _ => false
      dR := natToBits d (dRfn k) }
  have hdR_zero : dRfn 0 = 0 := by simp [dRfn]
  have h0 : inv 0 = packAS d S := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    · simp [hB]
    · simp [hdR, hdR_zero, natToBits_zero comb]
  have hstep : ∀ pos : Fin (arity (ℓ + 1)),
      act (revScanStep arith d ℓ b hℓ pos).unitary (ket (inv pos.1)) = ket (inv (pos.1 + 1)) := by
    intro pos
    have hpos_T1 : pos.1 < Ttilde1.length := by omega
    let t := Ttilde1[pos.1]'hpos_T1
    let rOut := (g[pos.1]'(by omega)).1
    have ht_mem : t ∈ Ttilde0 := (List.mergeSort_perm _ _).mem_iff.mp (List.getElem_mem hpos_T1)
    have hbounds := comb.Ttilde1_col_lt_iff s lo (lo + arity ℓ) hi (by omega) (by omega)
      (fun c hc => hs c hc) t ht_mem
    have hg_get : ((if t.1 < arity ℓ then t.2.1 + dRfn pos.1 else t.2.1, t.2.2) : ℕ × ℕ) =
        g[pos.1]'(by omega) := by
      have hmap_eq := hspec.2.2
      have hidx_g : pos.1 < g.length := by omega
      have hget := congrArg (fun l : List (ℕ × ℕ) => l[pos.1]?) hmap_eq
      rw [List.getElem?_eq_getElem hidx_g,
        List.getElem?_eq_getElem (by
          rw [List.length_map, List.length_finRange, (List.mergeSort_perm _ _).length_eq]
          change pos.1 < Ttilde0.length
          omega)] at hget
      simp only [List.getElem_map, List.getElem_finRange, Option.some.injEq] at hget
      exact hget
    have hrOut_eq : rOut = if t.1 < arity ℓ then t.2.1 + dRfn pos.1 else t.2.1 := by
      dsimp only [rOut]; rw [← hg_get]
    have hpow : arity d = 2 ^ d := arity_eq_two_pow d
    have hrOut_lt : rOut < 2 ^ d := by
      have hr := comb.greedyDiag_row_lt s lo hi (by omega) (fun c _ hc2 => hs c hc2)
        _ (List.getElem_mem (show pos.1 < g.length by omega))
      omega
    have htC_lt : t.2.2 < 2 ^ d := by omega
    have hdR_lt : dRfn pos.1 < 2 ^ d := by
      have h1 : dRfn pos.1 ≤ (Ttilde1.take pos.1).length := List.length_filter_le _ _
      have h2 : (Ttilde1.take pos.1).length ≤ pos.1 := List.length_take_le _ _
      have h3 := pos.isLt
      have h4 := arity_succ_le hℓ
      omega
    have hpos_lt : pos.1 < 2 ^ d := by
      have h3 := pos.isLt
      have h4 := arity_succ_le hℓ
      omega
    have hpos_spec := hspec.2.1 pos.1 hpos_T1
    have hstep1 := revScanStep_act comb arith d ℓ b hℓ pos
      { S with
        B := fun q => if q.1 < pos.1 then bAt q.1 else fun _ => false
        dR := natToBits d (dRfn pos.1) }
      (by dsimp only [liftPos]; rw [if_neg (Nat.lt_irrefl _)]) hflag htmp hpa t.1 t.2.1 t.2.2 rOut (dRfn pos.1)
      hrOut_lt htC_lt hdR_lt hpos_lt
      (by
        rw [hOut pos]
        change outRecPack d (natToBits d (g[pos.1]'(by omega)).1) (natToBits d (g[pos.1]'(by omega)).2) = _
        rw [← hg_get]; dsimp only; rw [← hrOut_eq])
      rfl
      (fun hlt => by
        rcases hpos_spec.1 hlt with ⟨_, ht1, _⟩
        have hdle : dRfn pos.1 ≤ pos.1 :=
          le_trans (List.length_filter_le _ _) (List.length_take_le _ _)
        exact ⟨by rw [hrOut_eq, if_pos hlt], ht1, hdle⟩)
      (fun hge => by
        have hnot : ¬ t.1 < arity ℓ := by omega
        exact ⟨by rw [hrOut_eq, if_neg hnot], hpos_spec.2 hge⟩)
      (by have hb := hbounds.2.2.2.2.1; dsimp only [lo] at hb; rw [hsubk] at hb; exact hb)
    dsimp only [inv] at hstep1 ⊢
    rw [hstep1]
    have hdR_succ : dRfn (pos.1 + 1) = if t.1 < arity ℓ then dRfn pos.1 else dRfn pos.1 + 1 := by
      dsimp only [dRfn]
      rw [List.take_add_one, List.getElem?_eq_getElem hpos_T1, Option.toList_some, List.filter_append, List.length_append]
      by_cases hlt : t.1 < arity ℓ
      · have hdec : decide (arity ℓ ≤ (Ttilde1[pos.1]'hpos_T1).1) = false := decide_eq_false (show ¬ arity ℓ ≤ t.1 by omega)
        rw [if_pos hlt, List.filter_singleton, hdec]; rfl
      · have hdec : decide (arity ℓ ≤ (Ttilde1[pos.1]'hpos_T1).1) = true := decide_eq_true (show arity ℓ ≤ t.1 by omega)
        rw [if_neg hlt, List.filter_singleton, hdec]; rfl
    congr 2; apply AsSnap.ext <;> try rfl
    · funext q; dsimp only
      by_cases hq : q = liftPos hℓ pos
      · subst hq
        rw [Function.update_self,
          if_pos (show (liftPos hℓ pos).1 < pos.1 + 1 by dsimp only [liftPos]; exact Nat.lt_succ_self pos.1)]
        dsimp only [bAt]; rw [dif_pos (show (liftPos hℓ pos).1 < arity (ℓ + 1) by dsimp only [liftPos]; exact pos.isLt)]; rfl
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ pos.1 := fun h => hq (Fin.ext h)
        by_cases hqp : q.1 < pos.1
        · have hqp1 : q.1 < pos.1 + 1 := by omega
          rw [if_pos hqp, if_pos hqp1]
        · have hnqp1 : ¬ q.1 < pos.1 + 1 := by omega
          rw [if_neg hqp, if_neg hnqp1]
    · rw [hdR_succ]
  have hseq := act_seqList_fin (revScanStep arith d ℓ b hℓ) inv hstep
  rw [h0] at hseq
  dsimp only [revScan]
  rw [LayeredCircuit.seq_unitary, act_mul, hseq]
  have hdR_end : dRfn (arity (ℓ + 1)) = arity ℓ := by
    dsimp only [dRfn]
    rw [← hT1_len, List.take_length]
    have hperm_f : List.Perm (Ttilde1.filter (fun u => decide (arity ℓ ≤ u.1)))
        (Ttilde0.filter (fun u => decide (arity ℓ ≤ u.1))) :=
      (List.mergeSort_perm _ _).filter _
    rw [hperm_f.length_eq]
    have hmap : Ttilde0.map Prod.fst = List.range (arity (ℓ + 1)) := by
      refine List.ext_getElem (by simp [hT0_len]) fun i hi1 hi2 => ?_
      simp [Ttilde0]
    have hfilt : (Ttilde0.filter (fun u => decide (arity ℓ ≤ u.1))).map Prod.fst =
        (List.range (arity (ℓ + 1))).filter (fun idx => decide (arity ℓ ≤ idx)) := by
      rw [← hmap]; conv_rhs => rw [List.filter_map]
      rfl
    rw [← List.length_map Prod.fst, hfilt]
    have ha2 : arity (ℓ + 1) = arity ℓ + arity ℓ := by rw [arity_succ_eq, Nat.two_mul]
    rw [ha2, List.range_add, List.filter_append]
    have hL0 : ((List.range (arity ℓ)).filter (fun idx => decide (arity ℓ ≤ idx))) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx; rw [List.mem_range] at hx; simp only [decide_eq_true_eq]; omega
    have hR0 : (((List.range (arity ℓ)).map (arity ℓ + ·)).filter (fun idx => decide (arity ℓ ≤ idx))) =
        (List.range (arity ℓ)).map (arity ℓ + ·) := by
      rw [List.filter_eq_self]
      intro x hx; rcases List.mem_map.mp hx with ⟨j, _, rfl⟩; simp
    rw [hL0, hR0, List.nil_append, List.length_map, List.length_range]
  rw [act_setConstOn, updateOn_dR]
  dsimp only [inv]
  have hx0 : (fun j => xor (packAS d { S with
      B := fun q => if q.1 < arity (ℓ + 1) then bAt q.1 else fun _ => false
      dR := natToBits d (dRfn (arity (ℓ + 1))) } (eDR d j)) (natToBits d (arity ℓ) j)) = fun _ => false := by
    funext j; simp only [packAS_dR_apply]; rw [hdR_end, Bool.xor_self]
  rw [hx0]
  congr 2; apply AsSnap.ext <;> try rfl
  · funext q; dsimp only
    by_cases hq : q.1 < arity (ℓ + 1)
    · rw [if_pos hq]
    · rw [if_neg hq, dif_neg hq]
  · exact hdR.symm

def sort2Emb (br : BitonicRouting54) (d ℓ : ℕ) (hℓ : ℓ < d) :
    Fin ((arity (ℓ + 1) * (d + (d + d)) + sortTraceSize (ℓ + 1)) + d) ↪ Fin (totAS d) :=
  packDTA54Emb (bPrefEmb d ℓ hℓ) (trPrefEmb br d ℓ hℓ) (saSort2Emb d)
    (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))

def sort2Circ (br : BitonicRouting54) (d ℓ : ℕ) (hℓ : ℓ < d) : LayeredCircuit (totAS d) :=
  (br.bitonicSortKeyCircuit (ℓ + 1) d (d + d) true).mapWires (sort2Emb br d ℓ hℓ)

lemma sort2Circ_size (br : BitonicRouting54) (d ℓ : ℕ) (hℓ : ℓ < d) :
    ((sort2Circ br d ℓ hℓ).size : ℝ) ≤
      br.C_sort * (arity (ℓ + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 * ((3 * d + 1 : ℕ) : ℝ) := by
  dsimp only [sort2Circ]
  rw [LayeredCircuit.mapWires_size]
  have hs := br.bitonicSortKeyCircuit_size (ℓ + 1) d (d + d) true
  have hc := le_of_lt br.hC_sort_pos
  have h1 : ((ℓ + 1 : ℕ) + 1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by norm_cast; omega
  have h2 : (2 ^ (ℓ + 1) : ℝ) = (arity (ℓ + 1) : ℝ) := by rw [arity_eq_two_pow]; push_cast; rfl
  have h3 : ((d + (d + d) + 1 : ℕ) : ℝ) = ((3 * d + 1 : ℕ) : ℝ) := by push_cast; ring
  have hsq : (((ℓ + 1 : ℕ) + 1 : ℝ)) ^ 2 ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by gcongr
  calc
    ((br.bitonicSortKeyCircuit (ℓ + 1) d (d + d) true).size : ℝ)
      ≤ br.C_sort * (2 ^ (ℓ + 1) : ℝ) * ((ℓ + 1 : ℕ) + 1 : ℝ) ^ 2 *
          ((d + (d + d) + 1 : ℕ) : ℝ) := by
        simpa [Nat.cast_add, Nat.cast_one] using hs
    _ ≤ br.C_sort * (arity (ℓ + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2 * ((3 * d + 1 : ℕ) : ℝ) := by
        rw [h2, h3]; gcongr

lemma sort2Circ_act (comb : LcgSym54Comb) (br : BitonicRouting54)
    (s : ℕ → ℕ) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (_hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d)
    (hs : ∀ c, c < b * (2 * arity ℓ) + 2 * arity ℓ → s c ≤ c)
    (S : AsSnap d)
    (htr : S.tr1 = fun _ => false) (hsa : S.sortAnc = fun _ => false)
    (hB : ∀ pos : Fin (arity (ℓ + 1)),
      S.B (liftPos hℓ pos) =
        let L := greedyDiag s (b * (2 * arity ℓ)) (b * (2 * arity ℓ) + arity ℓ)
        let R := greedyDiag s (b * (2 * arity ℓ) + arity ℓ) (b * (2 * arity ℓ) + 2 * arity ℓ)
        let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
        let Ttilde1 := Ttilde0.mergeSort (fun a b => decide (mergePhi (arity ℓ) a ≤ mergePhi (arity ℓ) b))
        let t := Ttilde1[pos.1]'(by rw [ttilde1_length comb s (b * (2 * arity ℓ)) ℓ hs]; exact pos.isLt)
        bRecPack d (natToBits d t.1) (natToBits d t.2.1) (natToBits d t.2.2)) :
    let lo := b * (2 * arity ℓ)
    let L := greedyDiag s lo (lo + arity ℓ)
    let R := greedyDiag s (lo + arity ℓ) (lo + 2 * arity ℓ)
    let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
    let x0 : Fin (arity (ℓ + 1)) → Qubits (wB d) := fun pos => S.B (liftPos hℓ pos)
    act (sort2Circ br d ℓ hℓ).unitary (ket (packAS d S)) =
      ket (packAS d { S with
        B := fun q =>
          if hq : q.1 < arity (ℓ + 1) then
            let t := Ttilde0[q.1]'(by rw [ttilde0_length comb s lo ℓ hs]; exact hq)
            bRecPack d (natToBits d t.1) (natToBits d t.2.1) (natToBits d t.2.2)
          else S.B q
        tr1 := padTr (sortTraceSize (ℓ + 1)) (sortTraceSize d)
          (sortTraceSize_mono br (by omega : ℓ + 1 ≤ d))
          (sortTrace (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0) }) := by
  intro lo L R Ttilde0 x0
  let Ttilde1 := Ttilde0.mergeSort (fun a b => decide (mergePhi (arity ℓ) a ≤ mergePhi (arity ℓ) b))
  have hT0_len : Ttilde0.length = arity (ℓ + 1) := ttilde0_length comb s lo ℓ hs
  have hT1_len : Ttilde1.length = arity (ℓ + 1) := ttilde1_length comb s lo ℓ hs
  have hx0_comp : packAS d S ∘ sort2Emb br d ℓ hℓ =
      packDTA54 (arity (ℓ + 1)) (wB d) (sortTraceSize (ℓ + 1)) d x0 (fun _ => false) := by
    refine comp_packDTA54Emb _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    · change (packAS d S ∘ eB d) ∘ _ = _
      exact comp_prefixRegEmb (bPrefixRange_le d) (arity_succ_le hℓ) _ _ (packAS_B d S)
    · change (packAS d S ∘ eTr d) ∘ _ = _
      rw [packAS_tr1, htr]; rfl
    · change (packAS d S ∘ eSA d) ∘ _ = _
      rw [packAS_sortAnc, hsa]; rfl
  have hcirc := act_mapWires_ket_singleton (br.bitonicSortKeyCircuit (ℓ + 1) d (d + d) true)
    (sort2Emb br d ℓ hℓ) (packAS d S) _ (by rw [hx0_comp]; exact br.act_bitonicSortKeyCircuit_ket _ _ _ _ x0)
  dsimp only [sort2Circ]
  rw [hcirc]
  set x1 := sort (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0
  have hx1_eq : ∀ pos : Fin (arity (ℓ + 1)),
      x1 pos = let t := Ttilde0[pos.1]'(by omega); bRecPack d (natToBits d t.1) (natToBits d t.2.1) (natToBits d t.2.2) := by
    let fB : ℕ × ℕ × ℕ → Qubits (wB d) := fun t => bRecPack d (natToBits d t.1) (natToBits d t.2.1) (natToBits d t.2.2)
    have hL0_eq : List.ofFn x0 = Ttilde1.map fB := by
      refine List.ext_getElem (by simp [hT1_len]) fun i hi1 hi2 => ?_
      have hilt : i < arity (ℓ + 1) := by simpa using hi1
      simp only [List.getElem_ofFn, List.getElem_map]
      exact hB ⟨i, hilt⟩
    have hperm : List.Perm (List.ofFn x1) (Ttilde0.map fB) := by
      have hp1 := br.sort_perm (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0
      have hp2 : List.Perm Ttilde1 Ttilde0 := List.mergeSort_perm _ _
      rw [hL0_eq] at hp1
      exact hp1.trans (hp2.map fB)
    have hpw1 : (List.ofFn x1).Pairwise (fun a b => bitsToNat (recKey54 a) ≤ bitsToNat (recKey54 b)) := by
      have hm := br.monotone_sort (fun r => bitsToNat (recKey54 r)) (ℓ + 1) x0
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.getElem_ofFn]
      exact hm (Nat.le_of_lt hij)
    have hT0_fst : ∀ (i : ℕ) (hi : i < Ttilde0.length), (Ttilde0[i]'hi).1 = i := fun i hi => by
      simp [Ttilde0]
    have hT0_lt : ∀ t ∈ Ttilde0, t.1 < 2 ^ d := fun t ht => by
      rcases List.getElem_of_mem ht with ⟨i, hi, rfl⟩
      rw [hT0_fst i hi]
      have h1 : arity (ℓ + 1) ≤ arity d := arity_succ_le hℓ
      have h2 : arity d = 2 ^ d := arity_eq_two_pow d
      omega
    have hpw2 : (Ttilde0.map fB).Pairwise (fun a b => bitsToNat (recKey54 a) ≤ bitsToNat (recKey54 b)) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.getElem_map, fB, recKey54_bRecPack]
      have hi0 : i < Ttilde0.length := by simpa using hi
      have hj0 : j < Ttilde0.length := by simpa using hj
      have hfi := hT0_lt _ (List.getElem_mem hi0)
      have hfj := hT0_lt _ (List.getElem_mem hj0)
      rw [comb.bitsToNat_natToBits hfi, comb.bitsToNat_natToBits hfj, hT0_fst i hi0, hT0_fst j hj0]
      exact Nat.le_of_lt hij
    have hinj : ∀ a ∈ Ttilde0.map fB, ∀ c ∈ Ttilde0.map fB,
        bitsToNat (recKey54 a) = bitsToNat (recKey54 c) → a = c := by
      rintro _ ha _ hc heq
      rcases List.mem_map.mp ha with ⟨t₁, ht₁, rfl⟩
      rcases List.mem_map.mp hc with ⟨t₂, ht₂, rfl⟩
      simp only [fB, recKey54_bRecPack] at heq
      rw [comb.bitsToNat_natToBits (hT0_lt t₁ ht₁), comb.bitsToNat_natToBits (hT0_lt t₂ ht₂)] at heq
      rcases List.getElem_of_mem ht₁ with ⟨i₁, hi₁, rfl⟩
      rcases List.getElem_of_mem ht₂ with ⟨i₂, hi₂, rfl⟩
      rw [hT0_fst i₁ hi₁, hT0_fst i₂ hi₂] at heq
      subst heq
      rfl
    have heq_list := comb.perm_eq_of_sorted_of_inj (fun r => bitsToNat (recKey54 r))
      (List.ofFn x1) (Ttilde0.map fB) hperm hpw1 hpw2 hinj
    intro pos
    have hget := congrArg (fun l : List (Qubits (wB d)) => l[pos.1]?) heq_list
    simp only [List.getElem?_ofFn, pos.isLt, ↓reduceDIte,
      List.getElem?_eq_getElem (show pos.1 < (Ttilde0.map fB).length by rw [List.length_map, hT0_len]; exact pos.isLt),
      Option.some.injEq] at hget
    rw [hget, List.getElem_map]
  congr 1
  dsimp only [sort2Emb]
  refine packAS_eq_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_main]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_R]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_C]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_T]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_Out]
  · change updateOn (packDTA54Emb (prefixRegEmb (bPrefixRange_le d) (arity_succ_le hℓ)) (trPrefEmb br d ℓ hℓ) (saSort2Emb d)
        (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
        (packAS d S) (packDTA54 (arity (ℓ + 1)) (wB d) (sortTraceSize (ℓ + 1)) d x1
          (sortTrace (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0)) ∘
        regEmb (oB d) (arity d) (wB d) (bPrefixRange_le d) = _
    rw [updateOn_packDTA54_prefixReg (bPrefixRange_le d) (arity_succ_le hℓ) (trPrefEmb br d ℓ hℓ)
      (saSort2Emb d) _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (packAS d S) S.B (packAS_B d S)]
    congr 1; funext q; dsimp only
    by_cases hq : q.1 < arity (ℓ + 1)
    · rw [dif_pos hq, dif_pos hq, hx1_eq ⟨q.1, hq⟩]
    · rw [dif_neg hq, dif_neg hq]
  · change updateOn (packDTA54Emb (bPrefEmb d ℓ hℓ)
        ((Fin.castLEEmb (sortTraceSize_mono br (by omega : ℓ + 1 ≤ d))).trans (eTr d))
        (saSort2Emb d) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
        (packAS d S) (packDTA54 (arity (ℓ + 1)) (wB d) (sortTraceSize (ℓ + 1)) d x1
          (sortTrace (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0)) ∘ eTr d = _
    exact updateOn_packDTA54_prefixSlice (sortTraceSize_mono br (by omega : ℓ + 1 ≤ d))
      (bPrefEmb d ℓ hℓ) (eTr d) (saSort2Emb d) _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))
      (packAS d S) (packAS_tr1 d S |>.trans htr) x1 _
  · change updateOn (packDTA54Emb (bPrefEmb d ℓ hℓ) (trPrefEmb br d ℓ hℓ)
        ((Fin.castLEEmb (by omega : d ≤ 2 * d + 1)).trans (eSA d))
        (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))
        (packAS d S) (packDTA54 (arity (ℓ + 1)) (wB d) (sortTraceSize (ℓ + 1)) d x1
          (sortTrace (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true x0)) ∘ eSA d = S.sortAnc
    rw [hsa]
    exact updateOn_packDTA54_prefixAncZero (by omega : d ≤ 2 * d + 1)
      (bPrefEmb d ℓ hℓ) (trPrefEmb br d ℓ hℓ) (eSA d) _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))
      (packAS d S) (packAS_sortAnc d S |>.trans hsa) x1 _
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_dR]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_flagBit]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_tmpD]
  · rw [updateOn_packDTA54_disjoint _ _ _ _ _ _ _ (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)), packAS_primAnc]

def clearRCStep (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) (pos : Fin (arity (ℓ + 1))) :
    LayeredCircuit (totAS d) :=
  let lo := b * (2 * arity ℓ)
  let p : Fin (arity d) := ⟨lo + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩
  let pos' := liftPos hℓ pos
  LayeredCircuit.seq
    ((arith.copyRegCircuit d).mapWires (combineEmb (bREmb d pos') (rSlot d p) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
    ((arith.copyRegCircuit d).mapWires (combineEmb (bCEmb d pos') (cSlot d p) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))

lemma clearRCStep_size (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) (pos : Fin (arity (ℓ + 1))) :
    (clearRCStep arith d ℓ b hℓ hb pos).size ≤ 2 * d := by
  dsimp only [clearRCStep]
  rw [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size, LayeredCircuit.mapWires_size,
    arith.copyRegCircuit_size]
  omega

def clearRC (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) : LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList ((List.finRange (arity (ℓ + 1))).map (clearRCStep arith d ℓ b hℓ hb))

lemma clearRC_size (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) :
    (clearRC arith d ℓ b hℓ hb).size ≤ arity (ℓ + 1) * (2 * d) :=
  seqList_fin_size_le _ _ (clearRCStep_size arith d ℓ b hℓ hb)

lemma clearRC_act (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) (S : AsSnap d)
    (rOf cOf : Fin (arity (ℓ + 1)) → ℕ)
    (hB : ∀ pos : Fin (arity (ℓ + 1)), ∃ idxB,
      S.B (liftPos hℓ pos) = bRecPack d idxB (natToBits d (rOf pos)) (natToBits d (cOf pos)))
    (hR : ∀ pos : Fin (arity (ℓ + 1)),
      S.R ⟨b * (2 * arity ℓ) + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩ = natToBits d (rOf pos))
    (hC : ∀ pos : Fin (arity (ℓ + 1)),
      S.C ⟨b * (2 * arity ℓ) + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩ = natToBits d (cOf pos)) :
    let lo := b * (2 * arity ℓ)
    act (clearRC arith d ℓ b hℓ hb).unitary (ket (packAS d S)) =
      ket (packAS d { S with
        R := fun p => if lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then fun _ => false else S.R p
        C := fun p => if lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then fun _ => false else S.C p }) := by
  intro lo
  have har : arity (ℓ + 1) = 2 * arity ℓ := arity_succ_eq ℓ
  let inv : ℕ → Qubits (totAS d) := fun k =>
    packAS d { S with
      R := fun p => if lo ≤ p.1 ∧ p.1 < lo + k then fun _ => false else S.R p
      C := fun p => if lo ≤ p.1 ∧ p.1 < lo + k then fun _ => false else S.C p }
  have h0 : inv 0 = packAS d S := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    all_goals { funext p; dsimp only; split_ifs with h <;> first | exfalso; omega | rfl }
  have hstep : ∀ pos : Fin (arity (ℓ + 1)),
      act (clearRCStep arith d ℓ b hℓ hb pos).unitary (ket (inv pos.1)) = ket (inv (pos.1 + 1)) := by
    intro pos
    let p : Fin (arity d) := ⟨lo + pos.1, by have := pos.isLt; omega⟩
    let pos' := liftPos hℓ pos
    rcases hB pos with ⟨idxB, hBpos⟩
    dsimp only [clearRCStep]
    rw [LayeredCircuit.seq_unitary, act_mul]
    rw [act_copyRegOn]
    dsimp only [inv]
    rw [updateOn_rSlot]
    simp only [packAS_slot_apply_R, bREmb, packAS_field_b_apply, hBpos, bRecPack_apply_fBR]
    have hRp : (if lo ≤ p.1 ∧ p.1 < lo + pos.1 then fun _ => false else S.R p) = natToBits d (rOf pos) := by
      have hn : ¬ (lo ≤ p.1 ∧ p.1 < lo + pos.1) := by dsimp [p]; omega
      rw [if_neg hn]; exact hR pos
    rw [hRp]; simp only [Bool.xor_self]
    rw [act_copyRegOn, updateOn_cSlot]
    simp only [packAS_slot_apply_C, bCEmb, packAS_field_b_apply, hBpos, bRecPack_apply_fBC]
    have hCp : (if lo ≤ p.1 ∧ p.1 < lo + pos.1 then fun _ => false else S.C p) = natToBits d (cOf pos) := by
      have hn : ¬ (lo ≤ p.1 ∧ p.1 < lo + pos.1) := by dsimp [p]; omega
      rw [if_neg hn]; exact hC pos
    rw [hCp]; simp only [Bool.xor_self]
    congr 2; apply AsSnap.ext <;> try rfl
    · funext q; dsimp only
      by_cases hq : q = p
      · subst hq; have h1 : lo ≤ p.1 ∧ p.1 < lo + (pos.1 + 1) := by dsimp [p]; omega
        rw [Function.update_self, if_pos h1]
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ lo + pos.1 := fun h => hq (Fin.ext h)
        by_cases h1 : lo ≤ q.1 ∧ q.1 < lo + pos.1
        · have h2 : lo ≤ q.1 ∧ q.1 < lo + (pos.1 + 1) := by omega
          rw [if_pos h1, if_pos h2]
        · have h2 : ¬ (lo ≤ q.1 ∧ q.1 < lo + (pos.1 + 1)) := by omega
          rw [if_neg h1, if_neg h2]
    · funext q; dsimp only
      by_cases hq : q = p
      · subst hq; have h1 : lo ≤ p.1 ∧ p.1 < lo + (pos.1 + 1) := by dsimp [p]; omega
        rw [Function.update_self, if_pos h1]
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ lo + pos.1 := fun h => hq (Fin.ext h)
        by_cases h1 : lo ≤ q.1 ∧ q.1 < lo + pos.1
        · have h2 : lo ≤ q.1 ∧ q.1 < lo + (pos.1 + 1) := by omega
          rw [if_pos h1, if_pos h2]
        · have h2 : ¬ (lo ≤ q.1 ∧ q.1 < lo + (pos.1 + 1)) := by omega
          rw [if_neg h1, if_neg h2]
  have hseq := act_seqList_fin (clearRCStep arith d ℓ b hℓ hb) inv hstep
  rwa [h0] at hseq

def swapOutRCStep (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) (pos : Fin (arity (ℓ + 1))) :
    LayeredCircuit (totAS d) :=
  let lo := b * (2 * arity ℓ)
  let p : Fin (arity d) := ⟨lo + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩
  let pos' := liftPos hℓ pos
  LayeredCircuit.seq
    ((arith.swapRegCircuit d).mapWires (combineEmb (outREmb d pos') (rSlot d p) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))
    ((arith.swapRegCircuit d).mapWires (combineEmb (outCEmb d pos') (cSlot d p) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))

lemma swapOutRCStep_size (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) (pos : Fin (arity (ℓ + 1))) :
    (swapOutRCStep arith d ℓ b hℓ hb pos).size ≤ 6 * d := by
  dsimp only [swapOutRCStep]
  rw [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size, LayeredCircuit.mapWires_size,
    arith.swapRegCircuit_size]
  omega

def swapOutRC (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) : LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList ((List.finRange (arity (ℓ + 1))).map (swapOutRCStep arith d ℓ b hℓ hb))

lemma swapOutRC_size (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) :
    (swapOutRC arith d ℓ b hℓ hb).size ≤ arity (ℓ + 1) * (6 * d) :=
  seqList_fin_size_le _ _ (swapOutRCStep_size arith d ℓ b hℓ hb)

lemma swapOutRC_act (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) (S : AsSnap d)
    (rNew cNew : Fin (arity (ℓ + 1)) → Qubits d)
    (hOut : S.Out = fun q => if hq : q.1 < arity (ℓ + 1) then
      outRecPack d (rNew ⟨q.1, hq⟩) (cNew ⟨q.1, hq⟩) else fun _ => false)
    (hR0 : ∀ pos : Fin (arity (ℓ + 1)),
      S.R ⟨b * (2 * arity ℓ) + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩ = fun _ => false)
    (hC0 : ∀ pos : Fin (arity (ℓ + 1)),
      S.C ⟨b * (2 * arity ℓ) + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩ = fun _ => false) :
    let lo := b * (2 * arity ℓ)
    act (swapOutRC arith d ℓ b hℓ hb).unitary (ket (packAS d S)) =
      ket (packAS d { S with
        R := fun p => if hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then rNew ⟨p.1 - lo, by omega⟩ else S.R p
        C := fun p => if hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then cNew ⟨p.1 - lo, by omega⟩ else S.C p
        Out := fun _ _ => false }) := by
  intro lo
  have har : arity (ℓ + 1) = 2 * arity ℓ := arity_succ_eq ℓ
  let inv : ℕ → Qubits (totAS d) := fun k =>
    packAS d { S with
      R := fun p => if hp : lo ≤ p.1 ∧ p.1 < lo + k ∧ p.1 < lo + arity (ℓ + 1) then
        rNew ⟨p.1 - lo, by omega⟩ else S.R p
      C := fun p => if hp : lo ≤ p.1 ∧ p.1 < lo + k ∧ p.1 < lo + arity (ℓ + 1) then
        cNew ⟨p.1 - lo, by omega⟩ else S.C p
      Out := fun q => if hq : k ≤ q.1 ∧ q.1 < arity (ℓ + 1) then
        outRecPack d (rNew ⟨q.1, hq.2⟩) (cNew ⟨q.1, hq.2⟩) else fun _ => false }
  have h0 : inv 0 = packAS d S := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    · funext p; dsimp only; split_ifs with h <;> first | exfalso; omega | rfl
    · funext p; dsimp only; split_ifs with h <;> first | exfalso; omega | rfl
    · funext q; dsimp only; rw [hOut]; dsimp only; by_cases hq : q.1 < arity (ℓ + 1)
      · rw [dif_pos ⟨Nat.zero_le _, hq⟩, dif_pos hq]
      · rw [dif_neg (by omega), dif_neg hq]
  have hn : inv (arity (ℓ + 1)) = packAS d { S with
      R := fun p => if hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then rNew ⟨p.1 - lo, by omega⟩ else S.R p
      C := fun p => if hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then cNew ⟨p.1 - lo, by omega⟩ else S.C p
      Out := fun _ _ => false } := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    · funext p; dsimp only; by_cases hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1)
      · rw [dif_pos ⟨hp.1, hp.2, hp.2⟩, dif_pos hp]
      · rw [dif_neg (by omega), dif_neg hp]
    · funext p; dsimp only; by_cases hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1)
      · rw [dif_pos ⟨hp.1, hp.2, hp.2⟩, dif_pos hp]
      · rw [dif_neg (by omega), dif_neg hp]
    · funext q; dsimp only; split_ifs with h <;> first | exfalso; omega | rfl
  rw [← h0, ← hn]
  refine act_seqList_fin (swapOutRCStep arith d ℓ b hℓ hb) inv fun pos => ?_
  let p : Fin (arity d) := ⟨lo + pos.1, by have := pos.isLt; omega⟩
  let pos' := liftPos hℓ pos
  let S0 : AsSnap d := { S with
    R := fun q => if hp : lo ≤ q.1 ∧ q.1 < lo + pos.1 ∧ q.1 < lo + arity (ℓ + 1) then
      rNew ⟨q.1 - lo, by omega⟩ else S.R q
    C := fun q => if hp : lo ≤ q.1 ∧ q.1 < lo + pos.1 ∧ q.1 < lo + arity (ℓ + 1) then
      cNew ⟨q.1 - lo, by omega⟩ else S.C q
    Out := fun q => if hq : pos.1 ≤ q.1 ∧ q.1 < arity (ℓ + 1) then
      outRecPack d (rNew ⟨q.1, hq.2⟩) (cNew ⟨q.1, hq.2⟩) else fun _ => false }
  let S1 : AsSnap d := { S0 with
    Out := Function.update S0.Out pos' (outRecPack d (fun _ => false) (cNew pos))
    R := Function.update S0.R p (rNew pos) }
  have hOut1 : S0.Out pos' = outRecPack d (rNew pos) (cNew pos) := by
    dsimp only [S0, pos', liftPos]; rw [dif_pos ⟨le_rfl, pos.isLt⟩]
  have hRp0 : S0.R p = fun _ => false := by
    dsimp only [S0]; rw [dif_neg (by dsimp [p]; omega)]; exact hR0 pos
  have hCp0 : S0.C p = fun _ => false := by
    dsimp only [S0]; rw [dif_neg (by dsimp [p]; omega)]; exact hC0 pos
  have hsw1 : act ((arith.swapRegCircuit d).mapWires (combineEmb (outREmb d pos') (rSlot d p) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary
        (ket (packAS d S0)) = ket (packAS d S1) := by
    rw [act_swapRegOn, outREmb, packAS_field_out, packAS_slot_comp_R, updateOn_outField,
      hOut1, hRp0, update_fOutR, outRecPack_comp_fOutR, updateOn_rSlot]
  have hsw2 : act ((arith.swapRegCircuit d).mapWires (combineEmb (outCEmb d pos') (cSlot d p) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary
        (ket (packAS d S1)) = ket (inv (pos.1 + 1)) := by
    rw [act_swapRegOn, outCEmb, packAS_field_out, packAS_slot_comp_C, updateOn_outField]
    have hS1Out : S1.Out pos' = outRecPack d (fun _ => false) (cNew pos) := by
      dsimp only [S1]; rw [Function.update_self]
    have hS1Cp : S1.C p = fun _ => false := hCp0
    rw [hS1Out, hS1Cp, update_fOutC, outRecPack_comp_fOutC, outRecPack_zero, updateOn_cSlot]
    dsimp only [inv]; congr 2; apply AsSnap.ext <;> try rfl
    · funext q; dsimp only [S1, S0]
      by_cases hq : q = p
      · subst hq; rw [Function.update_self, dif_pos (by dsimp [p]; refine ⟨by omega, by omega, by omega⟩)]
        congr 1; apply Fin.ext; dsimp [p]; omega
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ lo + pos.1 := fun h => hq (Fin.ext h)
        by_cases h1 : lo ≤ q.1 ∧ q.1 < lo + pos.1 ∧ q.1 < lo + arity (ℓ + 1)
        · have h2 : lo ≤ q.1 ∧ q.1 < lo + (pos.1 + 1) ∧ q.1 < lo + arity (ℓ + 1) := by omega
          rw [dif_pos h1, dif_pos h2]
        · have h2 : ¬ (lo ≤ q.1 ∧ q.1 < lo + (pos.1 + 1) ∧ q.1 < lo + arity (ℓ + 1)) := by omega
          rw [dif_neg h1, dif_neg h2]
    · funext q; dsimp only [S1, S0]
      by_cases hq : q = p
      · subst hq; rw [Function.update_self, dif_pos (by dsimp [p]; refine ⟨by omega, by omega, by omega⟩)]
        congr 1; apply Fin.ext; dsimp [p]; omega
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ lo + pos.1 := fun h => hq (Fin.ext h)
        by_cases h1 : lo ≤ q.1 ∧ q.1 < lo + pos.1 ∧ q.1 < lo + arity (ℓ + 1)
        · have h2 : lo ≤ q.1 ∧ q.1 < lo + (pos.1 + 1) ∧ q.1 < lo + arity (ℓ + 1) := by omega
          rw [dif_pos h1, dif_pos h2]
        · have h2 : ¬ (lo ≤ q.1 ∧ q.1 < lo + (pos.1 + 1) ∧ q.1 < lo + arity (ℓ + 1)) := by omega
          rw [dif_neg h1, dif_neg h2]
    · dsimp only [S1, S0]; rw [Function.update_idem]
      funext q
      by_cases hq : q = pos'
      · subst hq; rw [Function.update_self, dif_neg (by dsimp [pos', liftPos]; omega)]
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ pos.1 := fun h => hq (Fin.ext h)
        by_cases h1 : pos.1 ≤ q.1 ∧ q.1 < arity (ℓ + 1)
        · have h2 : pos.1 + 1 ≤ q.1 ∧ q.1 < arity (ℓ + 1) := by omega
          rw [dif_pos h1, dif_pos h2]
        · have h2 : ¬ (pos.1 + 1 ≤ q.1 ∧ q.1 < arity (ℓ + 1)) := by omega
          rw [dif_neg h1, dif_neg h2]
  dsimp only [swapOutRCStep]
  rw [LayeredCircuit.seq_unitary, act_mul]
  change act _ (act _ (ket (packAS d S0))) = _
  rw [hsw1, hsw2]

def asMergeBlock (br : BitonicRouting54) (arith : LcgSym54ArithV2) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) : LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList
    [ prepTtilde0 arith d ℓ b hℓ hb
    , sort1Circ br d ℓ hℓ
    , fwdScan arith d ℓ hℓ
    , (sort1Circ br d ℓ hℓ).adj
    , (prepTtilde0 arith d ℓ b hℓ hb).adj
    , revScan arith d ℓ b hℓ
    , sort2Circ br d ℓ hℓ
    , clearRC arith d ℓ b hℓ hb
    , (sort2Circ br d ℓ hℓ).adj
    , (revScan arith d ℓ b hℓ).adj
    , swapOutRC arith d ℓ b hℓ hb ]

lemma asMergeBlock_size (br : BitonicRouting54) (arith : LcgSym54ArithV2) (d ℓ b : ℕ)
    (hℓ : ℓ < d) (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d) :
    ((asMergeBlock br arith d ℓ b hℓ hb).size : ℝ) ≤
      (360 * (d + 1 : ℕ) : ℝ) * (arity (ℓ + 1) : ℝ) +
        14 * br.C_sort * (arity (ℓ + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 3 := by
  dsimp only [asMergeBlock]
  rw [LayeredCircuit.seqList_size]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, LayeredCircuit.adj_size]
  have h1 := prepTtilde0_size arith d ℓ b hℓ hb
  have h2 := sort1Circ_size br d ℓ hℓ
  have h3 := fwdScan_size arith d ℓ hℓ
  have h4 := revScan_size arith d ℓ b hℓ
  have h5 := sort2Circ_size br d ℓ hℓ
  have h6 := clearRC_size arith d ℓ b hℓ hb
  have h7 := swapOutRC_size arith d ℓ b hℓ hb
  have hpos : 1 ≤ arity (ℓ + 1) := by rw [arity_eq_two_pow]; exact Nat.one_le_two_pow
  have hc : 0 ≤ br.C_sort := le_of_lt br.hC_sort_pos
  have harith : (prepTtilde0 arith d ℓ b hℓ hb).size + (fwdScan arith d ℓ hℓ).size +
      (prepTtilde0 arith d ℓ b hℓ hb).size + (revScan arith d ℓ b hℓ).size +
      (clearRC arith d ℓ b hℓ hb).size + (revScan arith d ℓ b hℓ).size +
      (swapOutRC arith d ℓ b hℓ hb).size ≤ 360 * (d + 1) * arity (ℓ + 1) := by
    have hd : d ≤ d * arity (ℓ + 1) := Nat.le_mul_of_pos_right d hpos
    nlinarith
  have harithR : ((prepTtilde0 arith d ℓ b hℓ hb).size : ℝ) + ((fwdScan arith d ℓ hℓ).size : ℝ) +
      ((prepTtilde0 arith d ℓ b hℓ hb).size : ℝ) + ((revScan arith d ℓ b hℓ).size : ℝ) +
      ((clearRC arith d ℓ b hℓ hb).size : ℝ) + ((revScan arith d ℓ b hℓ).size : ℝ) +
      ((swapOutRC arith d ℓ b hℓ hb).size : ℝ) ≤ (360 * (d + 1 : ℕ) : ℝ) * (arity (ℓ + 1) : ℝ) := by
    exact_mod_cast harith
  have hs14 : ((4 * d + 2 : ℕ) : ℝ) * 2 + ((3 * d + 1 : ℕ) : ℝ) * 2 ≤ 14 * ((d + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hbit : 2 * ((sort1Circ br d ℓ hℓ).size : ℝ) + 2 * ((sort2Circ br d ℓ hℓ).size : ℝ) ≤
      14 * br.C_sort * (arity (ℓ + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hs14 (by positivity : 0 ≤ br.C_sort * (arity (ℓ + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2)
    nlinarith
  push_cast at harithR hbit ⊢
  linarith

lemma asMergeBlock_act (comb : LcgSym54Comb) (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (s : ℕ → ℕ) (d ℓ b : ℕ) (hℓ : ℓ < d)
    (hb : b * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d)
    (hs : ∀ c, c < b * (2 * arity ℓ) + 2 * arity ℓ → s c ≤ c)
    (S : AsSnap d)
    (hT : S.T = fun _ _ => false) (hOut : S.Out = fun _ _ => false)
    (hB : S.B = fun _ _ => false) (htr : S.tr1 = fun _ => false)
    (hsa : S.sortAnc = fun _ => false) (hdR : S.dR = fun _ => false)
    (hflag : S.flagBit = fun _ => false) (htmp : S.tmpD = fun _ => false)
    (hpa : S.primAnc = fun _ => false)
    (hR : ∀ pos : Fin (arity (ℓ + 1)),
      S.R ⟨b * (2 * arity ℓ) + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩ =
        let L := greedyDiag s (b * (2 * arity ℓ)) (b * (2 * arity ℓ) + arity ℓ)
        let R := greedyDiag s (b * (2 * arity ℓ) + arity ℓ) (b * (2 * arity ℓ) + 2 * arity ℓ)
        natToBits d ((L ++ R)[pos.1]'(by rw [lr_length comb s (b * (2 * arity ℓ)) (arity ℓ) hs, ← arity_succ_eq ℓ]; exact pos.isLt)).1)
    (hC : ∀ pos : Fin (arity (ℓ + 1)),
      S.C ⟨b * (2 * arity ℓ) + pos.1, by have := pos.isLt; have := arity_succ_eq ℓ; omega⟩ =
        let L := greedyDiag s (b * (2 * arity ℓ)) (b * (2 * arity ℓ) + arity ℓ)
        let R := greedyDiag s (b * (2 * arity ℓ) + arity ℓ) (b * (2 * arity ℓ) + 2 * arity ℓ)
        natToBits d ((L ++ R)[pos.1]'(by rw [lr_length comb s (b * (2 * arity ℓ)) (arity ℓ) hs, ← arity_succ_eq ℓ]; exact pos.isLt)).2) :
    let lo := b * (2 * arity ℓ)
    let hi := lo + 2 * arity ℓ
    let g := greedyDiag s lo hi
    have hg_len : g.length = arity (ℓ + 1) := by
      have h := comb.greedyDiag_length s lo hi (by omega) (fun c _ hc2 => hs c hc2)
      dsimp only [g, hi, lo] at h ⊢
      rw [arity_succ_eq]; omega
    act (asMergeBlock br arith d ℓ b hℓ hb).unitary (ket (packAS d S)) =
      ket (packAS d { S with
        R := fun p => if hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then
          natToBits d (g[p.1 - lo]'(by omega)).1 else S.R p
        C := fun p => if hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then
          natToBits d (g[p.1 - lo]'(by omega)).2 else S.C p }) := by
  intro lo hi g hg_len
  let L := greedyDiag s lo (lo + arity ℓ)
  let R := greedyDiag s (lo + arity ℓ) hi
  let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
  let Ttilde1 := Ttilde0.mergeSort (fun a b => decide (mergePhi (arity ℓ) a ≤ mergePhi (arity ℓ) b))
  have har := arity_succ_eq ℓ
  have hLR_len : (L ++ R).length = arity (ℓ + 1) := by
    rw [lr_length comb s lo (arity ℓ) hs, har]
  have hT0_len : Ttilde0.length = arity (ℓ + 1) := ttilde0_length comb s lo ℓ hs
  have hT1_len : Ttilde1.length = arity (ℓ + 1) := ttilde1_length comb s lo ℓ hs
  let rOf : Fin (arity (ℓ + 1)) → ℕ := fun pos => ((L ++ R)[pos.1]'(by omega)).1
  let cOf : Fin (arity (ℓ + 1)) → ℕ := fun pos => ((L ++ R)[pos.1]'(by omega)).2
  have hT0_col := comb.Ttilde1_col_lt_iff s lo (lo + arity ℓ) hi (by omega) (by omega) (fun c hc => hs c hc)
  have hpow : arity d = 2 ^ d := arity_eq_two_pow d
  have hrLt : ∀ pos : Fin (arity (ℓ + 1)), rOf pos < 2 ^ d := fun pos => by
    have htmem : Ttilde0[pos.1]'(by omega) ∈ Ttilde0 := List.getElem_mem (by omega)
    have hp := (hT0_col _ htmem).2.2.1
    have hsub : Ttilde0[pos.1]'(by omega) = (pos.1, rOf pos, cOf pos) := by simp [Ttilde0, rOf, cOf]
    rw [hsub] at hp; dsimp only [hi, lo] at hp; omega
  have hcLt : ∀ pos : Fin (arity (ℓ + 1)), cOf pos < 2 ^ d := fun pos => by
    have htmem : Ttilde0[pos.1]'(by omega) ∈ Ttilde0 := List.getElem_mem (by omega)
    have hp := (hT0_col _ htmem).2.1
    have hsub : Ttilde0[pos.1]'(by omega) = (pos.1, rOf pos, cOf pos) := by simp [Ttilde0, rOf, cOf]
    rw [hsub] at hp; dsimp only [hi, lo] at hp; omega
  have hgeR : ∀ pos : Fin (arity (ℓ + 1)), arity ℓ ≤ pos.1 → pos.1 - arity ℓ ≤ rOf pos := fun pos hge => by
    have htmem : Ttilde0[pos.1]'(by omega) ∈ Ttilde0 := List.getElem_mem (by omega)
    have hsub : Ttilde0[pos.1]'(by omega) = (pos.1, rOf pos, cOf pos) := by simp [Ttilde0, rOf, cOf]
    have hp := (hT0_col _ htmem).2.2.2.2.2
    rw [hsub] at hp; simp only [show lo + arity ℓ - lo = arity ℓ by omega] at hp
    exact hp hge
  -- Snapshots across the 11 steps
  let T0fn : Fin (arity d) → Qubits (wT d) := fun q =>
    if hq : q.1 < arity (ℓ + 1) then
      let t := Ttilde0[q.1]'(by omega)
      tRecOf d (arity ℓ) t.1 t.2.1 t.2.2
    else fun _ => false
  let T1fn : Fin (arity d) → Qubits (wT d) := fun q =>
    if hq : q.1 < arity (ℓ + 1) then
      let t := Ttilde1[q.1]'(by omega)
      tRecOf d (arity ℓ) t.1 t.2.1 t.2.2
    else fun _ => false
  let tr1fn : Qubits (sortTraceSize d) := padTr (sortTraceSize (ℓ + 1)) (sortTraceSize d)
    (sortTraceSize_mono br (by omega : ℓ + 1 ≤ d))
    (sortTrace (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true (fun pos => T0fn (liftPos hℓ pos)))
  let Outfn : Fin (arity d) → Qubits (wOut d) := fun q =>
    if hq : q.1 < arity (ℓ + 1) then
      let p := g[q.1]'(by omega)
      outRecPack d (natToBits d p.1) (natToBits d p.2)
    else fun _ => false
  let B1fn : Fin (arity d) → Qubits (wB d) := fun q =>
    if hq : q.1 < arity (ℓ + 1) then
      let t := Ttilde1[q.1]'(by omega)
      bRecPack d (natToBits d t.1) (natToBits d t.2.1) (natToBits d t.2.2)
    else fun _ => false
  let B0fn : Fin (arity d) → Qubits (wB d) := fun q =>
    if hq : q.1 < arity (ℓ + 1) then
      let t := Ttilde0[q.1]'(by omega)
      bRecPack d (natToBits d t.1) (natToBits d t.2.1) (natToBits d t.2.2)
    else fun _ => false
  let tr2fn : Qubits (sortTraceSize d) := padTr (sortTraceSize (ℓ + 1)) (sortTraceSize d)
    (sortTraceSize_mono br (by omega : ℓ + 1 ≤ d))
    (sortTrace (fun r => bitsToNat (recKey54 r)) (ℓ + 1) true (fun pos => B1fn (liftPos hℓ pos)))
  let S_1 : AsSnap d := { S with T := T0fn }
  let S_2 : AsSnap d := { S with T := T1fn, tr1 := tr1fn }
  let S_3 : AsSnap d := { S with T := T1fn, Out := Outfn, tr1 := tr1fn }
  let S_4 : AsSnap d := { S with T := T0fn, Out := Outfn }
  let S_5 : AsSnap d := { S with Out := Outfn }
  let S_6 : AsSnap d := { S with Out := Outfn, B := B1fn }
  let S_7 : AsSnap d := { S with Out := Outfn, B := B0fn, tr1 := tr2fn }
  let Rclr : Fin (arity d) → Qubits d := fun p => if lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then fun _ => false else S.R p
  let Cclr : Fin (arity d) → Qubits d := fun p => if lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then fun _ => false else S.C p
  let S_8 : AsSnap d := { S with R := Rclr, C := Cclr, Out := Outfn, B := B0fn, tr1 := tr2fn }
  let S_9 : AsSnap d := { S with R := Rclr, C := Cclr, Out := Outfn, B := B1fn }
  let S_10 : AsSnap d := { S with R := Rclr, C := Cclr, Out := Outfn }
  have hT0_eq : ∀ q : Fin (arity d), T0fn q = if hq : q.1 < arity (ℓ + 1) then
      tRecOf d (arity ℓ) q.1 (rOf ⟨q.1, hq⟩) (cOf ⟨q.1, hq⟩) else fun _ => false := fun q => by
    by_cases hq : q.1 < arity (ℓ + 1)
    · simp only [T0fn, dif_pos hq, Ttilde0, List.getElem_map, List.getElem_zipIdx, zero_add]; rfl
    · dsimp only [T0fn]; rw [dif_neg hq, dif_neg hq]
  have hS1_T : ∀ pos : Fin (arity (ℓ + 1)), S_1.T (liftPos hℓ pos) =
      tRecOf d (arity ℓ) (Ttilde0[pos.1]' (by omega)).1 (Ttilde0[pos.1]'(by omega)).2.1 (Ttilde0[pos.1]'(by omega)).2.2 := by
    intro pos; dsimp only [S_1, T0fn, liftPos]; rw [dif_pos pos.isLt]
  have hS2_T : ∀ pos : Fin (arity (ℓ + 1)), S_2.T (liftPos hℓ pos) =
      tRecOf d (arity ℓ) (Ttilde1[pos.1]' (by omega)).1 (Ttilde1[pos.1]'(by omega)).2.1 (Ttilde1[pos.1]'(by omega)).2.2 := by
    intro pos; dsimp only [S_2, T1fn, liftPos]; rw [dif_pos pos.isLt]
  have hS4_T : ∀ pos : Fin (arity (ℓ + 1)), S_4.T (liftPos hℓ pos) =
      tRecOf d (arity ℓ) (Ttilde0[pos.1]' (by omega)).1 (Ttilde0[pos.1]'(by omega)).2.1 (Ttilde0[pos.1]'(by omega)).2.2 := by
    intro pos; dsimp only [S_4, T0fn, liftPos]; rw [dif_pos pos.isLt]
  have st1 : act (prepTtilde0 arith d ℓ b hℓ hb).unitary (ket (packAS d S)) = ket (packAS d S_1) := by
    have hp := prepTtilde0_act comb arith d ℓ b hℓ hb S hT htmp hpa rOf cOf hrLt hcLt hgeR hR hC
    rw [hp]; congr 2; apply AsSnap.ext <;> try rfl
    funext q; exact (hT0_eq q).symm
  have st2 : act (sort1Circ br d ℓ hℓ).unitary (ket (packAS d S_1)) = ket (packAS d S_2) := by
    have hs1 := sort1Circ_act comb br s d ℓ b hℓ hb hs S_1 htr hsa hS1_T
    rw [hs1]; congr 2; apply AsSnap.ext <;> try rfl
    funext q; dsimp only [S_2, S_1, T0fn, T1fn]
    by_cases hq : q.1 < arity (ℓ + 1)
    · rw [dif_pos hq, dif_pos hq]
    · rw [dif_neg hq, dif_neg hq, dif_neg hq]
  have st3 : act (fwdScan arith d ℓ hℓ).unitary (ket (packAS d S_2)) = ket (packAS d S_3) :=
    fwdScan_act comb arith s d ℓ b hℓ hb hs S_2 hOut hdR hpa hS2_T
  have st4 : act (sort1Circ br d ℓ hℓ).adj.unitary (ket (packAS d S_3)) = ket (packAS d S_4) := by
    apply act_adj_ket
    have hs1 := sort1Circ_act comb br s d ℓ b hℓ hb hs S_4 htr hsa hS4_T
    rw [hs1]; congr 2; apply AsSnap.ext <;> try rfl
    funext q; dsimp only [S_4, S_3, T0fn, T1fn]
    by_cases hq : q.1 < arity (ℓ + 1)
    · rw [dif_pos hq, dif_pos hq]
    · rw [dif_neg hq, dif_neg hq, dif_neg hq]
  have st5 : act (prepTtilde0 arith d ℓ b hℓ hb).adj.unitary (ket (packAS d S_4)) = ket (packAS d S_5) := by
    apply act_adj_ket
    have hp := prepTtilde0_act comb arith d ℓ b hℓ hb S_5 hT htmp hpa rOf cOf hrLt hcLt hgeR hR hC
    rw [hp]; congr 2; apply AsSnap.ext <;> try rfl
    funext q; exact (hT0_eq q).symm
  have st6 : act (revScan arith d ℓ b hℓ).unitary (ket (packAS d S_5)) = ket (packAS d S_6) :=
    revScan_act comb arith s d ℓ b hℓ hb hs S_5 hB hdR hflag htmp hpa
      (fun pos => by dsimp only [S_5, Outfn, liftPos]; rw [dif_pos pos.isLt])
  have st7 : act (sort2Circ br d ℓ hℓ).unitary (ket (packAS d S_6)) = ket (packAS d S_7) := by
    have hs2 := sort2Circ_act comb br s d ℓ b hℓ hb hs S_6 htr hsa
      (fun pos => by dsimp only [S_6, B1fn, liftPos]; rw [dif_pos pos.isLt])
    rw [hs2]; congr 2; apply AsSnap.ext <;> try rfl
    funext q; dsimp only [S_7, S_6, B1fn, B0fn]
    by_cases hq : q.1 < arity (ℓ + 1)
    · rw [dif_pos hq, dif_pos hq]
    · rw [dif_neg hq, dif_neg hq, dif_neg hq]
  have st8 : act (clearRC arith d ℓ b hℓ hb).unitary (ket (packAS d S_7)) = ket (packAS d S_8) :=
    clearRC_act arith d ℓ b hℓ hb S_7 rOf cOf
      (fun pos => ⟨natToBits d pos.1, by
        dsimp only [S_7, B0fn, liftPos]; rw [dif_pos pos.isLt]
        simp [Ttilde0, rOf, cOf]⟩) hR hC
  have st9 : act (sort2Circ br d ℓ hℓ).adj.unitary (ket (packAS d S_8)) = ket (packAS d S_9) := by
    apply act_adj_ket
    have hs2 := sort2Circ_act comb br s d ℓ b hℓ hb hs S_9 htr hsa
      (fun pos => by dsimp only [S_9, B1fn, liftPos]; rw [dif_pos pos.isLt])
    rw [hs2]; congr 2; apply AsSnap.ext <;> try rfl
    funext q; dsimp only [S_9, S_8, B1fn, B0fn]
    by_cases hq : q.1 < arity (ℓ + 1)
    · rw [dif_pos hq, dif_pos hq]
    · rw [dif_neg hq, dif_neg hq, dif_neg hq]
  have st10 : act (revScan arith d ℓ b hℓ).adj.unitary (ket (packAS d S_9)) = ket (packAS d S_10) :=
    act_adj_ket _ (revScan_act comb arith s d ℓ b hℓ hb hs S_10 hB hdR hflag htmp hpa
      (fun pos => by dsimp only [S_10, Outfn, liftPos]; rw [dif_pos pos.isLt]))
  have st11 : act (swapOutRC arith d ℓ b hℓ hb).unitary (ket (packAS d S_10)) =
      ket (packAS d { S with
        R := fun p => if hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then
          natToBits d (g[p.1 - lo]'(by omega)).1 else S.R p
        C := fun p => if hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1) then
          natToBits d (g[p.1 - lo]'(by omega)).2 else S.C p }) := by
    have hsw := swapOutRC_act arith d ℓ b hℓ hb S_10
      (fun pos => natToBits d (g[pos.1]'(by omega)).1)
      (fun pos => natToBits d (g[pos.1]'(by omega)).2)
      rfl
      (fun pos => by dsimp [S_10, Rclr]; rw [if_pos (by omega)])
      (fun pos => by dsimp [S_10, Cclr]; rw [if_pos (by omega)])
    rw [hsw]; congr 2; apply AsSnap.ext <;> try rfl
    · funext p; dsimp only [S_10, Rclr]
      by_cases hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1)
      · rw [dif_pos hp, dif_pos hp]
      · rw [dif_neg hp, dif_neg hp, if_neg hp]
    · funext p; dsimp only [S_10, Cclr]
      by_cases hp : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ + 1)
      · rw [dif_pos hp, dif_pos hp]
      · rw [dif_neg hp, dif_neg hp, if_neg hp]
    · exact hOut.symm
  dsimp only [asMergeBlock]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, LayeredCircuit.id_unitary, act_mul, act_one]
  rw [st1, st2, st3, st4, st5, st6, st7, st8, st9, st10, st11]

/-! ### Part 8: Multi-Level Alonso–Schott Merge, Core Circuit, and Uniform `S_N` Prep -/

lemma getElem_bang_eq {α : Type*} [Inhabited α] (L : List α) (i : ℕ) (hi : i < L.length) :
    L[i]! = L[i]'hi := by
  simp [hi]

lemma seqList_size_le_real {m : ℕ} (lcs : List (LayeredCircuit m)) (B : ℝ)
    (hB : ∀ lc ∈ lcs, (lc.size : ℝ) ≤ B) :
    ((LayeredCircuit.seqList lcs).size : ℝ) ≤ (lcs.length : ℝ) * B := by
  rw [LayeredCircuit.seqList_size]
  induction lcs with
  | nil => simp
  | cons lc rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h1 := hB lc List.mem_cons_self
    have h2 := ih fun lc' hlc' => hB lc' (List.mem_cons_of_mem _ hlc')
    linarith

lemma seqList_fin_size_le_real {m n : ℕ} (f : Fin n → LayeredCircuit m) (B : ℝ)
    (hB : ∀ k : Fin n, ((f k).size : ℝ) ≤ B) :
    ((LayeredCircuit.seqList ((List.finRange n).map f)).size : ℝ) ≤ (n : ℝ) * B := by
  have h := seqList_size_le_real ((List.finRange n).map f) B (fun lc hlc => by
    rcases List.mem_map.mp hlc with ⟨k, _, rfl⟩
    exact hB k)
  simpa using h

lemma arity_pos (k : ℕ) : 0 < arity k := by
  rw [arity_eq_two_pow]; exact Nat.two_pow_pos k

lemma arity_one_le (k : ℕ) : 1 ≤ arity k := arity_pos k

lemma arity_zero : arity 0 = 1 := by
  rw [arity_eq_two_pow, pow_zero]

lemma arity_mul_sub {d m : ℕ} (hm : m ≤ d) : arity (d - m) * arity m = arity d := by
  simp only [arity_eq_two_pow, ← pow_add, Nat.sub_add_cancel hm]

lemma arity_mul_rem (d ℓ : ℕ) (hℓ : ℓ < d) :
    arity (d - 1 - ℓ) * arity (ℓ + 1) = arity d := by
  simp only [arity_eq_two_pow, ← pow_add, show d - 1 - ℓ + (ℓ + 1) = d by omega]

lemma blockBound {d ℓ : ℕ} (hℓ : ℓ < d) (b : Fin (arity (d - 1 - ℓ))) :
    b.1 * (2 * arity ℓ) + 2 * arity ℓ ≤ arity d := by
  rw [← arity_succ_eq, ← Nat.succ_mul, ← arity_mul_rem d ℓ hℓ]
  exact Nat.mul_le_mul_right _ b.isLt

lemma blk_hi_le {d m : ℕ} (hm : m ≤ d) (p : Fin (arity d)) :
    (p.1 / arity m) * arity m + arity m ≤ arity d := by
  have hmul : arity d = arity (d - m) * arity m := (arity_mul_sub hm).symm
  have hdiv : p.1 / arity m < arity (d - m) := by
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm, ← hmul]; exact p.isLt
  have hle : (p.1 / arity m + 1) * arity m ≤ arity (d - m) * arity m :=
    Nat.mul_le_mul_right _ hdiv
  rw [Nat.succ_mul] at hle
  exact le_trans hle (le_of_eq hmul.symm)

def ZeroAncAS {d : ℕ} (S : AsSnap d) : Prop :=
  S.T = (fun _ _ => false) ∧
  S.Out = (fun _ _ => false) ∧
  S.B = (fun _ _ => false) ∧
  S.tr1 = (fun _ => false) ∧
  S.sortAnc = (fun _ => false) ∧
  S.dR = (fun _ => false) ∧
  S.flagBit = (fun _ => false) ∧
  S.tmpD = (fun _ => false) ∧
  S.primAnc = (fun _ => false)

lemma zeroAnc_zeroSnap (d : ℕ) (main0 : Fin (arity d) → Qubits d) : ZeroAncAS (zeroSnap d main0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def levelTargetSnap (s : ℕ → ℕ) (d m : ℕ) (S : AsSnap d) : AsSnap d :=
  { S with
    R := fun p =>
      let blk := p.1 / arity m
      let off := p.1 % arity m
      let lo := blk * arity m
      natToBits d ((greedyDiag s lo (lo + arity m))[off]!).1
    C := fun p =>
      let blk := p.1 / arity m
      let off := p.1 % arity m
      let lo := blk * arity m
      natToBits d ((greedyDiag s lo (lo + arity m))[off]!).2 }

def levelBlockSnap (s : ℕ → ℕ) (d m k : ℕ) (S : AsSnap d) : AsSnap d :=
  { S with
    R := fun p => if p.1 < k * arity m then (levelTargetSnap s d m S).R p else S.R p
    C := fun p => if p.1 < k * arity m then (levelTargetSnap s d m S).C p else S.C p }

def asMergeLevel (br : BitonicRouting54) (arith : LcgSym54ArithV2) (d : ℕ) (ℓ : Fin d) :
    LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList
    ((List.finRange (arity (d - 1 - ℓ.1))).map fun b =>
      asMergeBlock br arith d ℓ.1 b.1 ℓ.isLt (blockBound ℓ.isLt b))

lemma asMergeLevel_size (br : BitonicRouting54) (arith : LcgSym54ArithV2) (d : ℕ) (ℓ : Fin d) :
    ((asMergeLevel br arith d ℓ).size : ℝ) ≤
      (360 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 3 := by
  dsimp only [asMergeLevel]
  have hstep : ∀ b : Fin (arity (d - 1 - ℓ.1)),
      ((asMergeBlock br arith d ℓ.1 b.1 ℓ.isLt (blockBound ℓ.isLt b)).size : ℝ) ≤
        ((360 * (d + 1 : ℕ) : ℝ) + 14 * br.C_sort * ((d + 1 : ℕ) : ℝ) ^ 3) * (arity (ℓ.1 + 1) : ℝ) := by
    intro b
    have hs := asMergeBlock_size br arith d ℓ.1 b.1 ℓ.isLt (blockBound ℓ.isLt b)
    linarith [hs]
  have htot := seqList_fin_size_le_real _ _ hstep
  have hmul : (arity (d - 1 - ℓ.1) : ℝ) * (arity (ℓ.1 + 1) : ℝ) = (arity d : ℝ) := by
    exact_mod_cast arity_mul_rem d ℓ.1 ℓ.isLt
  have hrem : (arity (d - 1 - ℓ.1) : ℝ) *
      (((360 * (d + 1 : ℕ) : ℝ) + 14 * br.C_sort * ((d + 1 : ℕ) : ℝ) ^ 3) * (arity (ℓ.1 + 1) : ℝ)) =
      ((360 * (d + 1 : ℕ) : ℝ) + 14 * br.C_sort * ((d + 1 : ℕ) : ℝ) ^ 3) * (arity d : ℝ) := by
    rw [← mul_assoc, mul_comm (arity (d - 1 - ℓ.1) : ℝ), mul_assoc, hmul]
  rw [hrem] at htot
  have hd1 : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hcub : ((d + 1 : ℕ) : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 3 := by
    have hp := pow_le_pow_right₀ hd1 (show 1 ≤ 3 by omega)
    simpa using hp
  have har : (0 : ℝ) ≤ (arity d : ℝ) := Nat.cast_nonneg _
  calc
    ((LayeredCircuit.seqList (List.map (fun b => asMergeBlock br arith d ℓ.1 b.1 ℓ.isLt (blockBound ℓ.isLt b))
        (List.finRange (arity (d - 1 - ℓ.1))))).size : ℝ)
      ≤ ((360 * (d + 1 : ℕ) : ℝ) + 14 * br.C_sort * ((d + 1 : ℕ) : ℝ) ^ 3) * (arity d : ℝ) := htot
    _ ≤ (360 * ((d + 1 : ℕ) : ℝ) ^ 3 + 14 * br.C_sort * ((d + 1 : ℕ) : ℝ) ^ 3) * (arity d : ℝ) := by
        gcongr
    _ = (360 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 3 := by ring

lemma asMergeLevel_act (comb : LcgSym54Comb) (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (s : ℕ → ℕ) (d : ℕ) (ℓ : Fin d) (hs : ∀ c, c < arity d → s c ≤ c)
    (S0 : AsSnap d) (hz : ZeroAncAS S0) :
    act (asMergeLevel br arith d ℓ).unitary (ket (packAS d (levelTargetSnap s d ℓ.1 S0))) =
      ket (packAS d (levelTargetSnap s d (ℓ.1 + 1) S0)) := by
  let S := levelTargetSnap s d ℓ.1 S0
  let inv : ℕ → Qubits (totAS d) := fun k => packAS d (levelBlockSnap s d (ℓ.1 + 1) k S)
  have h0 : inv 0 = packAS d S := by
    dsimp only [inv, levelBlockSnap]
    congr 1; apply AsSnap.ext <;> try rfl
    · funext p; simp
    · funext p; simp
  have hn : inv (arity (d - 1 - ℓ.1)) = packAS d (levelTargetSnap s d (ℓ.1 + 1) S0) := by
    dsimp only [inv, levelBlockSnap, levelTargetSnap]
    congr 1; apply AsSnap.ext <;> try rfl
    · funext p; dsimp only
      have hlt : p.1 < arity (d - 1 - ℓ.1) * arity (ℓ.1 + 1) := by
        rw [arity_mul_rem d ℓ.1 ℓ.isLt]; exact p.isLt
      rw [if_pos hlt]
    · funext p; dsimp only
      have hlt : p.1 < arity (d - 1 - ℓ.1) * arity (ℓ.1 + 1) := by
        rw [arity_mul_rem d ℓ.1 ℓ.isLt]; exact p.isLt
      rw [if_pos hlt]
  have hstep : ∀ b : Fin (arity (d - 1 - ℓ.1)),
      act (asMergeBlock br arith d ℓ.1 b.1 ℓ.isLt (blockBound ℓ.isLt b)).unitary (ket (inv b.1)) =
        ket (inv (b.1 + 1)) := by
    intro b
    let hb := blockBound ℓ.isLt b
    let lo := b.1 * (2 * arity ℓ.1)
    let hi := lo + 2 * arity ℓ.1
    let g := greedyDiag s lo hi
    let L := greedyDiag s lo (lo + arity ℓ.1)
    let R := greedyDiag s (lo + arity ℓ.1) hi
    let S_b := levelBlockSnap s d (ℓ.1 + 1) b.1 S
    have har1 : arity (ℓ.1 + 1) = 2 * arity ℓ.1 := arity_succ_eq ℓ.1
    have hlo_eq : b.1 * arity (ℓ.1 + 1) = lo := by dsimp only [lo]; rw [har1]
    have hs_blk : ∀ c, c < hi → s c ≤ c := fun c hc => hs c (lt_of_lt_of_le hc hb)
    have hL_len : L.length = arity ℓ.1 := by
      have h := comb.greedyDiag_length s lo (lo + arity ℓ.1) (by omega)
        (fun c _ hc2 => hs_blk c (by dsimp only [hi]; omega))
      dsimp only [L]; omega
    have hR_len : R.length = arity ℓ.1 := by
      have h := comb.greedyDiag_length s (lo + arity ℓ.1) hi (by omega)
        (fun c _ hc2 => hs_blk c hc2)
      dsimp only [R, hi] at h ⊢; omega
    have hpos_div_mod : ∀ pos : Fin (arity (ℓ.1 + 1)),
        let idx := lo + pos.1
        (∀ hlt : pos.1 < arity ℓ.1,
          idx / arity ℓ.1 = 2 * b.1 ∧ idx % arity ℓ.1 = pos.1 ∧
          (L ++ R)[pos.1]'(by rw [lr_length comb s lo (arity ℓ.1) hs_blk, ← arity_succ_eq]; exact pos.isLt) =
            L[pos.1]'(by rw [hL_len]; exact hlt)) ∧
        (∀ _hge : arity ℓ.1 ≤ pos.1,
          idx / arity ℓ.1 = 2 * b.1 + 1 ∧ idx % arity ℓ.1 = pos.1 - arity ℓ.1 ∧
          (L ++ R)[pos.1]'(by rw [lr_length comb s lo (arity ℓ.1) hs_blk, ← arity_succ_eq]; exact pos.isLt) =
            R[pos.1 - arity ℓ.1]'(by
              rw [hR_len]
              have hpos_lt : pos.1 < 2 * arity ℓ.1 := lt_of_lt_of_eq pos.isLt har1
              omega)) := by
      intro pos idx
      have hpos_lt : pos.1 < 2 * arity ℓ.1 := by rw [← har1]; exact pos.isLt
      constructor
      · intro hlt
        have heq : idx = pos.1 + arity ℓ.1 * (2 * b.1) := by dsimp only [idx, lo]; ring
        have hdiv : idx / arity ℓ.1 = 2 * b.1 := by
          rw [heq, Nat.add_mul_div_left _ _ (arity_pos ℓ.1), Nat.div_eq_of_lt hlt, Nat.zero_add]
        have hmod : idx % arity ℓ.1 = pos.1 := by
          rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
        refine ⟨hdiv, hmod, ?_⟩
        exact List.getElem_append_left (by rw [hL_len]; exact hlt)
      · intro hge
        have hr_lt : pos.1 - arity ℓ.1 < arity ℓ.1 := by omega
        have heq : idx = (pos.1 - arity ℓ.1) + arity ℓ.1 * (2 * b.1 + 1) := by
          have hmul : arity ℓ.1 * (2 * b.1 + 1) = b.1 * (2 * arity ℓ.1) + arity ℓ.1 := by ring
          dsimp only [idx, lo]; omega
        have hdiv : idx / arity ℓ.1 = 2 * b.1 + 1 := by
          rw [heq, Nat.add_mul_div_left _ _ (arity_pos ℓ.1), Nat.div_eq_of_lt hr_lt, Nat.zero_add]
        have hmod : idx % arity ℓ.1 = pos.1 - arity ℓ.1 := by
          rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr_lt]
        refine ⟨hdiv, hmod, ?_⟩
        have hle_L : L.length ≤ pos.1 := by rw [hL_len]; exact hge
        rw [List.getElem_append_right hle_L]
        congr 1; omega
    have hR_arg : ∀ pos : Fin (arity (ℓ.1 + 1)),
        S_b.R ⟨lo + pos.1, by have hpos_lt : pos.1 < 2 * arity ℓ.1 := lt_of_lt_of_eq pos.isLt har1; dsimp only [lo]; omega⟩ =
          natToBits d ((L ++ R)[pos.1]'(by rw [lr_length comb s lo (arity ℓ.1) hs_blk, ← arity_succ_eq]; exact pos.isLt)).1 := by
      intro pos
      have hpos_lt : pos.1 < 2 * arity ℓ.1 := lt_of_lt_of_eq pos.isLt har1
      have hge_b : ¬ lo + pos.1 < b.1 * arity (ℓ.1 + 1) := by omega
      dsimp only [S_b, levelBlockSnap]
      rw [if_neg hge_b]
      dsimp only [S, levelTargetSnap]
      by_cases hlt : pos.1 < arity ℓ.1
      · rcases (hpos_div_mod pos).1 hlt with ⟨hdiv, hmod, happ⟩
        rw [hdiv, hmod]
        have hlo : 2 * b.1 * arity ℓ.1 = lo := by dsimp only [lo]; ring
        rw [hlo, happ, getElem_bang_eq L pos.1 (by rw [hL_len]; exact hlt)]
      · rcases (hpos_div_mod pos).2 (Nat.le_of_not_lt hlt) with ⟨hdiv, hmod, happ⟩
        rw [hdiv, hmod]
        have hlo : (2 * b.1 + 1) * arity ℓ.1 = lo + arity ℓ.1 := by dsimp only [lo]; ring
        have hhi : lo + arity ℓ.1 + arity ℓ.1 = hi := by dsimp only [hi]; omega
        rw [hlo, hhi, happ, getElem_bang_eq R (pos.1 - arity ℓ.1) (by rw [hR_len]; omega)]
    have hC_arg : ∀ pos : Fin (arity (ℓ.1 + 1)),
        S_b.C ⟨lo + pos.1, by have hpos_lt : pos.1 < 2 * arity ℓ.1 := lt_of_lt_of_eq pos.isLt har1; dsimp only [lo]; omega⟩ =
          natToBits d ((L ++ R)[pos.1]'(by rw [lr_length comb s lo (arity ℓ.1) hs_blk, ← arity_succ_eq]; exact pos.isLt)).2 := by
      intro pos
      have hpos_lt : pos.1 < 2 * arity ℓ.1 := lt_of_lt_of_eq pos.isLt har1
      have hge_b : ¬ lo + pos.1 < b.1 * arity (ℓ.1 + 1) := by omega
      dsimp only [S_b, levelBlockSnap]
      rw [if_neg hge_b]
      dsimp only [S, levelTargetSnap]
      by_cases hlt : pos.1 < arity ℓ.1
      · rcases (hpos_div_mod pos).1 hlt with ⟨hdiv, hmod, happ⟩
        rw [hdiv, hmod]
        have hlo : 2 * b.1 * arity ℓ.1 = lo := by dsimp only [lo]; ring
        rw [hlo, happ, getElem_bang_eq L pos.1 (by rw [hL_len]; exact hlt)]
      · rcases (hpos_div_mod pos).2 (Nat.le_of_not_lt hlt) with ⟨hdiv, hmod, happ⟩
        rw [hdiv, hmod]
        have hlo : (2 * b.1 + 1) * arity ℓ.1 = lo + arity ℓ.1 := by dsimp only [lo]; ring
        have hhi : lo + arity ℓ.1 + arity ℓ.1 = hi := by dsimp only [hi]; omega
        rw [hlo, hhi, happ, getElem_bang_eq R (pos.1 - arity ℓ.1) (by rw [hR_len]; omega)]
    have hact := asMergeBlock_act comb br arith s d ℓ.1 b.1 ℓ.isLt hb hs_blk S_b
      hz.1 hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2.1 hz.2.2.2.2.2.1 hz.2.2.2.2.2.2.1 hz.2.2.2.2.2.2.2.1 hz.2.2.2.2.2.2.2.2
      hR_arg hC_arg
    have hhi_eq : (b.1 + 1) * arity (ℓ.1 + 1) = lo + arity (ℓ.1 + 1) := by rw [Nat.succ_mul, hlo_eq]
    dsimp only [inv] at hact ⊢
    rw [hact]
    congr 2; apply AsSnap.ext <;> try rfl
    · funext p; dsimp only [S_b, levelBlockSnap, levelTargetSnap]
      by_cases hlt1 : p.1 < b.1 * arity (ℓ.1 + 1)
      · have hnot : ¬ (lo ≤ p.1 ∧ p.1 < lo + arity (ℓ.1 + 1)) := by omega
        have hlt2 : p.1 < (b.1 + 1) * arity (ℓ.1 + 1) := by omega
        rw [dif_neg hnot, if_pos hlt1, if_pos hlt2]
      · by_cases hlt2 : p.1 < (b.1 + 1) * arity (ℓ.1 + 1)
        · have hyes : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ.1 + 1) := by omega
          have hrem_lt : p.1 - lo < arity (ℓ.1 + 1) := by omega
          have heq : p.1 = (p.1 - lo) + arity (ℓ.1 + 1) * b.1 := by rw [Nat.mul_comm]; omega
          have hdiv : p.1 / arity (ℓ.1 + 1) = b.1 := by
            rw [heq, Nat.add_mul_div_left _ _ (arity_pos (ℓ.1 + 1)), Nat.div_eq_of_lt hrem_lt, Nat.zero_add]
          have hmod : p.1 % arity (ℓ.1 + 1) = p.1 - lo := by
            conv_lhs => rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]
          have hhi' : lo + arity (ℓ.1 + 1) = hi := by dsimp only [hi]; omega
          have hg_len : (greedyDiag s lo hi).length = arity (ℓ.1 + 1) := by
            have h := comb.greedyDiag_length s lo hi (by omega) (fun c _ hc2 => hs_blk c hc2)
            dsimp only [hi] at h ⊢; omega
          rw [dif_pos hyes, if_pos hlt2, hdiv, hmod, hlo_eq, hhi',
            getElem_bang_eq (greedyDiag s lo hi) (p.1 - lo) (by omega)]
        · have hnot : ¬ (lo ≤ p.1 ∧ p.1 < lo + arity (ℓ.1 + 1)) := by omega
          rw [dif_neg hnot, if_neg hlt1, if_neg hlt2]
    · funext p; dsimp only [S_b, levelBlockSnap, levelTargetSnap]
      by_cases hlt1 : p.1 < b.1 * arity (ℓ.1 + 1)
      · have hnot : ¬ (lo ≤ p.1 ∧ p.1 < lo + arity (ℓ.1 + 1)) := by omega
        have hlt2 : p.1 < (b.1 + 1) * arity (ℓ.1 + 1) := by omega
        rw [dif_neg hnot, if_pos hlt1, if_pos hlt2]
      · by_cases hlt2 : p.1 < (b.1 + 1) * arity (ℓ.1 + 1)
        · have hyes : lo ≤ p.1 ∧ p.1 < lo + arity (ℓ.1 + 1) := by omega
          have hrem_lt : p.1 - lo < arity (ℓ.1 + 1) := by omega
          have heq : p.1 = (p.1 - lo) + arity (ℓ.1 + 1) * b.1 := by rw [Nat.mul_comm]; omega
          have hdiv : p.1 / arity (ℓ.1 + 1) = b.1 := by
            rw [heq, Nat.add_mul_div_left _ _ (arity_pos (ℓ.1 + 1)), Nat.div_eq_of_lt hrem_lt, Nat.zero_add]
          have hmod : p.1 % arity (ℓ.1 + 1) = p.1 - lo := by
            conv_lhs => rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]
          have hhi' : lo + arity (ℓ.1 + 1) = hi := by dsimp only [hi]; omega
          have hg_len : (greedyDiag s lo hi).length = arity (ℓ.1 + 1) := by
            have h := comb.greedyDiag_length s lo hi (by omega) (fun c _ hc2 => hs_blk c hc2)
            dsimp only [hi] at h ⊢; omega
          rw [dif_pos hyes, if_pos hlt2, hdiv, hmod, hlo_eq, hhi',
            getElem_bang_eq (greedyDiag s lo hi) (p.1 - lo) (by omega)]
        · have hnot : ¬ (lo ≤ p.1 ∧ p.1 < lo + arity (ℓ.1 + 1)) := by omega
          rw [dif_neg hnot, if_neg hlt1, if_neg hlt2]
  have hseq := act_seqList_fin _ inv hstep
  rw [h0, hn] at hseq
  exact hseq

def asMergeAll (br : BitonicRouting54) (arith : LcgSym54ArithV2) (d : ℕ) :
    LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList ((List.finRange d).map (asMergeLevel br arith d))

lemma asMergeAll_size (br : BitonicRouting54) (arith : LcgSym54ArithV2) (d : ℕ) :
    ((asMergeAll br arith d).size : ℝ) ≤
      (360 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 := by
  dsimp only [asMergeAll]
  have htot := seqList_fin_size_le_real (asMergeLevel br arith d)
    ((360 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 3)
    (asMergeLevel_size br arith d)
  have hd : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hnonneg : 0 ≤ (360 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 3 := by
    have := br.hC_sort_pos; positivity
  calc
    ((LayeredCircuit.seqList (List.map (asMergeLevel br arith d) (List.finRange d))).size : ℝ)
      ≤ (d : ℝ) * ((360 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 3) := htot
    _ ≤ ((d + 1 : ℕ) : ℝ) * ((360 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 3) := by gcongr
    _ = (360 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 := by ring

lemma asMergeAll_act (comb : LcgSym54Comb) (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (s : ℕ → ℕ) (d : ℕ) (hs : ∀ c, c < arity d → s c ≤ c)
    (S0 : AsSnap d) (hz : ZeroAncAS S0) :
    act (asMergeAll br arith d).unitary
        (ket (packAS d { S0 with
          R := fun p => natToBits d (s p.1)
          C := fun p => natToBits d p.1 })) =
      ket (packAS d { S0 with
        R := fun p => natToBits d ((greedyDiag s 0 (arity d))[p.1]!).1
        C := fun p => natToBits d ((greedyDiag s 0 (arity d))[p.1]!).2 }) := by
  let inv : ℕ → Qubits (totAS d) := fun k => packAS d (levelTargetSnap s d (min k d) S0)
  have h0 : inv 0 = packAS d { S0 with R := fun p => natToBits d (s p.1), C := fun p => natToBits d p.1 } := by
    dsimp only [inv, levelTargetSnap]
    simp only [Nat.zero_min]
    congr 1; apply AsSnap.ext <;> try rfl
    · funext p; dsimp only; simp only [arity_zero, Nat.div_one, Nat.mod_one, mul_one]
      rw [comb.greedyDiag_leaf s p.1 (hs p.1 p.isLt)]; rfl
    · funext p; dsimp only; simp only [arity_zero, Nat.div_one, Nat.mod_one, mul_one]
      rw [comb.greedyDiag_leaf s p.1 (hs p.1 p.isLt)]; rfl
  have hn : inv d = packAS d { S0 with
      R := fun p => natToBits d ((greedyDiag s 0 (arity d))[p.1]!).1
      C := fun p => natToBits d ((greedyDiag s 0 (arity d))[p.1]!).2 } := by
    dsimp only [inv, levelTargetSnap]
    simp only [min_self]
    congr 1; apply AsSnap.ext <;> try rfl
    · funext p; dsimp only
      rw [Nat.div_eq_of_lt p.isLt, Nat.mod_eq_of_lt p.isLt, Nat.zero_mul, Nat.zero_add]
    · funext p; dsimp only
      rw [Nat.div_eq_of_lt p.isLt, Nat.mod_eq_of_lt p.isLt, Nat.zero_mul, Nat.zero_add]
  have hstep : ∀ ℓ : Fin d, act (asMergeLevel br arith d ℓ).unitary (ket (inv ℓ.1)) = ket (inv (ℓ.1 + 1)) := by
    intro ℓ
    have hm1 : min ℓ.1 d = ℓ.1 := Nat.min_eq_left (Nat.le_of_lt ℓ.isLt)
    have hm2 : min (ℓ.1 + 1) d = ℓ.1 + 1 := Nat.min_eq_left ℓ.isLt
    dsimp only [inv]
    rw [hm1, hm2]
    exact asMergeLevel_act comb br arith s d ℓ hs S0 hz
  have hseq := act_seqList_fin (asMergeLevel br arith d) inv hstep
  dsimp only [asMergeAll]
  rwa [h0, hn] at hseq

def padMainLESStep (arith : LcgSym54ArithV2) (N d : ℕ) (p : Fin (arity d)) : LayeredCircuit (totAS d) :=
  if _ : p.1 < N then LayeredCircuit.id (totAS d)
  else (arith.setConstMSBCircuit d p.1).mapWires (mainSlot d p)

def padMainLES (arith : LcgSym54ArithV2) (N d : ℕ) : LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList ((List.finRange (arity d)).map (padMainLESStep arith N d))

lemma padMainLES_size (arith : LcgSym54ArithV2) (N d : ℕ) :
    (padMainLES arith N d).size ≤ arity d * d := by
  refine seqList_fin_size_le _ d fun p => ?_
  dsimp only [padMainLESStep]
  split_ifs
  · simp [LayeredCircuit.id_size]
  · rw [LayeredCircuit.mapWires_size]; exact arith.setConstMSBCircuit_size d p.1

lemma padMainLES_act (arith : LcgSym54ArithV2) (N d : ℕ) (s : Fin N → ℕ) :
    act (padMainLES arith N d).unitary (ket (packAS d (zeroSnap d (padZeroLESBits N d s)))) =
      ket (packAS d (zeroSnap d (fun p => natToBits d (padLES54 N s p.1)))) := by
  let inv : ℕ → Qubits (totAS d) := fun k =>
    packAS d (zeroSnap d (fun p =>
      if p.1 < k then natToBits d (padLES54 N s p.1) else padZeroLESBits N d s p))
  have h0 : inv 0 = packAS d (zeroSnap d (padZeroLESBits N d s)) := rfl
  have hn : inv (arity d) = packAS d (zeroSnap d (fun p => natToBits d (padLES54 N s p.1))) := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    funext p; dsimp only [zeroSnap]; rw [if_pos p.isLt]
  have hstep : ∀ p : Fin (arity d),
      act (padMainLESStep arith N d p).unitary (ket (inv p.1)) = ket (inv (p.1 + 1)) := by
    intro p
    dsimp only [padMainLESStep]
    by_cases hp : p.1 < N
    · rw [dif_pos hp, LayeredCircuit.id_unitary, act_one]
      congr 1; dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
      funext q; dsimp only [zeroSnap]
      by_cases hq : q.1 = p.1
      · have hqN : q.1 < N := by omega
        rw [if_neg (by omega), if_pos (by omega)]
        dsimp only [padZeroLESBits, padLES54]
        rw [dif_pos hqN, dif_pos hqN]
      · by_cases hqp : q.1 < p.1
        · rw [if_pos hqp, if_pos (by omega)]
        · rw [if_neg hqp, if_neg (by omega)]
    · rw [dif_neg hp, act_setConstOn]
      dsimp only [inv]; rw [updateOn_mainSlot]
      congr 2; apply AsSnap.ext <;> try rfl
      funext q; dsimp only [zeroSnap]
      by_cases hq : q = p
      · rw [hq, Function.update_self]
        simp only [packAS_slot_apply_main]
        rw [if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self p.1)]
        dsimp only [padZeroLESBits, padLES54]
        rw [dif_neg hp, dif_neg hp]
        funext _; exact Bool.false_xor _
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ p.1 := fun h => hq (Fin.ext h)
        by_cases hqp : q.1 < p.1
        · rw [if_pos hqp, if_pos (by omega)]
        · rw [if_neg hqp, if_neg (by omega)]
  have hseq := act_seqList_fin (padMainLESStep arith N d) inv hstep
  dsimp only [padMainLES]
  rwa [h0, hn] at hseq

def swapMainR (arith : LcgSym54ArithV2) (d : ℕ) : LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList ((List.finRange (arity d)).map fun p =>
    (arith.swapRegCircuit d).mapWires (combineEmb (mainSlot d p) (rSlot d p) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))

lemma swapMainR_size (arith : LcgSym54ArithV2) (d : ℕ) :
    (swapMainR arith d).size ≤ arity d * (3 * d) := by
  refine seqList_fin_size_le _ (3 * d) fun p => ?_
  rw [LayeredCircuit.mapWires_size, arith.swapRegCircuit_size]

lemma swapMainR_act (arith : LcgSym54ArithV2) (d : ℕ) (S : AsSnap d) :
    act (swapMainR arith d).unitary (ket (packAS d S)) =
      ket (packAS d { S with main := S.R, R := S.main }) := by
  let inv : ℕ → Qubits (totAS d) := fun k =>
    packAS d { S with
      main := fun q => if q.1 < k then S.R q else S.main q
      R := fun q => if q.1 < k then S.main q else S.R q }
  have h0 : inv 0 = packAS d S := rfl
  have hn : inv (arity d) = packAS d { S with main := S.R, R := S.main } := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    · funext q; dsimp only; rw [if_pos q.isLt]
    · funext q; dsimp only; rw [if_pos q.isLt]
  have hstep : ∀ p : Fin (arity d),
      act ((arith.swapRegCircuit d).mapWires (combineEmb (mainSlot d p) (rSlot d p) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary
        (ket (inv p.1)) = ket (inv (p.1 + 1)) := by
    intro p
    dsimp only [inv]
    rw [act_swapRegOn]
    rw [packAS_slot_comp_R, packAS_slot_comp_main, updateOn_mainSlot, updateOn_rSlot]
    dsimp only
    congr 2; apply AsSnap.ext <;> try rfl
    · funext q; dsimp only
      by_cases hq : q = p
      · rw [hq, Function.update_self, if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self p.1)]
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ p.1 := fun h => hq (Fin.ext h)
        by_cases hqp : q.1 < p.1
        · rw [if_pos hqp, if_pos (by omega)]
        · rw [if_neg hqp, if_neg (by omega)]
    · funext q; dsimp only
      by_cases hq : q = p
      · rw [hq, Function.update_self, if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self p.1)]
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ p.1 := fun h => hq (Fin.ext h)
        by_cases hqp : q.1 < p.1
        · rw [if_pos hqp, if_pos (by omega)]
        · rw [if_neg hqp, if_neg (by omega)]
  have hseq := act_seqList_fin _ inv hstep
  dsimp only [swapMainR]
  rwa [h0, hn] at hseq

def initC (arith : LcgSym54ArithV2) (d : ℕ) : LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList ((List.finRange (arity d)).map fun p =>
    (arith.setConstMSBCircuit d p.1).mapWires (cSlot d p))

lemma initC_size (arith : LcgSym54ArithV2) (d : ℕ) :
    (initC arith d).size ≤ arity d * d := by
  refine seqList_fin_size_le _ d fun p => ?_
  rw [LayeredCircuit.mapWires_size]; exact arith.setConstMSBCircuit_size d p.1

lemma initC_act (arith : LcgSym54ArithV2) (d : ℕ) (S : AsSnap d) (hC : S.C = fun _ _ => false) :
    act (initC arith d).unitary (ket (packAS d S)) =
      ket (packAS d { S with C := fun p => natToBits d p.1 }) := by
  let inv : ℕ → Qubits (totAS d) := fun k =>
    packAS d { S with C := fun q => if q.1 < k then natToBits d q.1 else fun _ => false }
  have h0 : inv 0 = packAS d S := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    funext q; dsimp only; rw [if_neg (Nat.not_lt_zero _), hC]
  have hn : inv (arity d) = packAS d { S with C := fun p => natToBits d p.1 } := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    funext q; dsimp only; rw [if_pos q.isLt]
  have hstep : ∀ p : Fin (arity d),
      act ((arith.setConstMSBCircuit d p.1).mapWires (cSlot d p)).unitary (ket (inv p.1)) =
        ket (inv (p.1 + 1)) := by
    intro p
    dsimp only [inv]
    rw [act_setConstOn, updateOn_cSlot]
    simp only [packAS_slot_apply_C]
    rw [if_neg (Nat.lt_irrefl _)]
    congr 2; apply AsSnap.ext <;> try rfl
    funext q; dsimp only
    by_cases hq : q = p
    · rw [hq, Function.update_self, if_pos (Nat.lt_succ_self p.1)]
      funext _; exact Bool.false_xor _
    · rw [Function.update_of_ne hq]
      have hqne : q.1 ≠ p.1 := fun h => hq (Fin.ext h)
      by_cases hqp : q.1 < p.1
      · rw [if_pos hqp, if_pos (by omega)]
      · rw [if_neg hqp, if_neg (by omega)]
  have hseq := act_seqList_fin _ inv hstep
  dsimp only [initC]
  rwa [h0, hn] at hseq

def clearRIdx (arith : LcgSym54ArithV2) (d : ℕ) : LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList ((List.finRange (arity d)).map fun p =>
    (arith.setConstMSBCircuit d p.1).mapWires (rSlot d p))

lemma clearRIdx_size (arith : LcgSym54ArithV2) (d : ℕ) :
    (clearRIdx arith d).size ≤ arity d * d := by
  refine seqList_fin_size_le _ d fun p => ?_
  rw [LayeredCircuit.mapWires_size]; exact arith.setConstMSBCircuit_size d p.1

lemma clearRIdx_act (arith : LcgSym54ArithV2) (d : ℕ) (S : AsSnap d) (hR : S.R = fun p => natToBits d p.1) :
    act (clearRIdx arith d).unitary (ket (packAS d S)) =
      ket (packAS d { S with R := fun _ _ => false }) := by
  let inv : ℕ → Qubits (totAS d) := fun k =>
    packAS d { S with R := fun q => if q.1 < k then fun _ => false else natToBits d q.1 }
  have h0 : inv 0 = packAS d S := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    funext q; dsimp only; rw [if_neg (Nat.not_lt_zero _), hR]
  have hn : inv (arity d) = packAS d { S with R := fun _ _ => false } := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    funext q; dsimp only; rw [if_pos q.isLt]
  have hstep : ∀ p : Fin (arity d),
      act ((arith.setConstMSBCircuit d p.1).mapWires (rSlot d p)).unitary (ket (inv p.1)) =
        ket (inv (p.1 + 1)) := by
    intro p
    dsimp only [inv]
    rw [act_setConstOn, updateOn_rSlot]
    simp only [packAS_slot_apply_R]
    rw [if_neg (Nat.lt_irrefl _)]
    congr 2; apply AsSnap.ext <;> try rfl
    funext q; dsimp only
    by_cases hq : q = p
    · rw [hq, Function.update_self, if_pos (Nat.lt_succ_self p.1)]
      funext _; exact Bool.xor_self _
    · rw [Function.update_of_ne hq]
      have hqne : q.1 ≠ p.1 := fun h => hq (Fin.ext h)
      by_cases hqp : q.1 < p.1
      · rw [if_pos hqp, if_pos (by omega)]
      · rw [if_neg hqp, if_neg (by omega)]
  have hseq := act_seqList_fin _ inv hstep
  dsimp only [clearRIdx]
  rwa [h0, hn] at hseq

def swapCMain (arith : LcgSym54ArithV2) (d : ℕ) : LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList ((List.finRange (arity d)).map fun p =>
    (arith.swapRegCircuit d).mapWires (combineEmb (cSlot d p) (mainSlot d p) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega))))

lemma swapCMain_size (arith : LcgSym54ArithV2) (d : ℕ) :
    (swapCMain arith d).size ≤ arity d * (3 * d) := by
  refine seqList_fin_size_le _ (3 * d) fun p => ?_
  rw [LayeredCircuit.mapWires_size, arith.swapRegCircuit_size]

lemma swapCMain_act (arith : LcgSym54ArithV2) (d : ℕ) (S : AsSnap d) :
    act (swapCMain arith d).unitary (ket (packAS d S)) =
      ket (packAS d { S with main := S.C, C := S.main }) := by
  let inv : ℕ → Qubits (totAS d) := fun k =>
    packAS d { S with
      main := fun q => if q.1 < k then S.C q else S.main q
      C := fun q => if q.1 < k then S.main q else S.C q }
  have h0 : inv 0 = packAS d S := rfl
  have hn : inv (arity d) = packAS d { S with main := S.C, C := S.main } := by
    dsimp only [inv]; congr 1; apply AsSnap.ext <;> try rfl
    · funext q; dsimp only; rw [if_pos q.isLt]
    · funext q; dsimp only; rw [if_pos q.isLt]
  have hstep : ∀ p : Fin (arity d),
      act ((arith.swapRegCircuit d).mapWires (combineEmb (cSlot d p) (mainSlot d p) (by exact sep_of _ _ (by dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR]; omega)))).unitary
        (ket (inv p.1)) = ket (inv (p.1 + 1)) := by
    intro p
    dsimp only [inv]
    rw [act_swapRegOn]
    rw [packAS_slot_comp_main, packAS_slot_comp_C, updateOn_cSlot, updateOn_mainSlot]
    dsimp only
    congr 2; apply AsSnap.ext <;> try rfl
    · funext q; dsimp only
      by_cases hq : q = p
      · rw [hq, Function.update_self, if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self p.1)]
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ p.1 := fun h => hq (Fin.ext h)
        by_cases hqp : q.1 < p.1
        · rw [if_pos hqp, if_pos (by omega)]
        · rw [if_neg hqp, if_neg (by omega)]
    · funext q; dsimp only
      by_cases hq : q = p
      · rw [hq, Function.update_self, if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self p.1)]
      · rw [Function.update_of_ne hq]
        have hqne : q.1 ≠ p.1 := fun h => hq (Fin.ext h)
        by_cases hqp : q.1 < p.1
        · rw [if_pos hqp, if_pos (by omega)]
        · rw [if_neg hqp, if_neg (by omega)]
  have hseq := act_seqList_fin _ inv hstep
  dsimp only [swapCMain]
  rwa [h0, hn] at hseq

def alonsoSchottCore (br : BitonicRouting54) (arith : LcgSym54ArithV2) (N d : ℕ) :
    LayeredCircuit (totAS d) :=
  LayeredCircuit.seqList
    [ padMainLES arith N d
    , swapMainR arith d
    , initC arith d
    , asMergeAll br arith d
    , clearRIdx arith d
    , swapCMain arith d ]

lemma alonsoSchottCore_size (br : BitonicRouting54) (arith : LcgSym54ArithV2) (N d : ℕ) :
    ((alonsoSchottCore br arith N d).size : ℝ) ≤
      (370 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 := by
  dsimp only [alonsoSchottCore]
  rw [LayeredCircuit.seqList_size]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.cast_add]
  have h1 : ((padMainLES arith N d).size : ℝ) ≤ (arity d : ℝ) * (d : ℝ) := by exact_mod_cast padMainLES_size arith N d
  have h2 : ((swapMainR arith d).size : ℝ) ≤ (arity d : ℝ) * (3 * (d : ℝ)) := by exact_mod_cast swapMainR_size arith d
  have h3 : ((initC arith d).size : ℝ) ≤ (arity d : ℝ) * (d : ℝ) := by exact_mod_cast initC_size arith d
  have h4 := asMergeAll_size br arith d
  have h5 : ((clearRIdx arith d).size : ℝ) ≤ (arity d : ℝ) * (d : ℝ) := by exact_mod_cast clearRIdx_size arith d
  have h6 : ((swapCMain arith d).size : ℝ) ≤ (arity d : ℝ) * (3 * (d : ℝ)) := by exact_mod_cast swapCMain_size arith d
  have hd1 : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hd4 : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 4 := by
    have hd_le : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by norm_cast; omega
    have hpow : ((d + 1 : ℕ) : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 4 := by
      simpa using pow_le_pow_right₀ hd1 (show 1 ≤ 4 by omega)
    exact le_trans hd_le hpow
  have har : (0 : ℝ) ≤ (arity d : ℝ) := Nat.cast_nonneg _
  push_cast at h4 hd1 hd4 ⊢
  nlinarith

lemma alonsoSchottCore_act (comb : LcgSym54Comb) (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (N d : ℕ) (hNM : N ≤ arity d) (s : Fin N → ℕ) (hs : IsLES N s) :
    act (alonsoSchottCore br arith N d).unitary (ket (packAS d (zeroSnap d (padZeroLESBits N d s)))) =
      ket (packAS d (zeroSnap d (permRegBits N d hNM (comb.lesToPerm N s hs)⁻¹))) := by
  have hsPad : ∀ c, c < arity d → padLES54 N s c ≤ c := fun c _ => comb.padLES54_le N s hs c
  have hroot : ∀ p : Fin (arity d),
      (greedyDiag (padLES54 N s) 0 (arity d))[p.1]! =
        (p.1, (padPerm54 N (arity d) hNM (comb.lesToPerm N s hs)⁻¹ p).1) := fun p =>
    (comb.greedyDiag_pad_root N (arity d) hNM s hs p.1 p.isLt).2
  dsimp only [alonsoSchottCore]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, LayeredCircuit.id_unitary, act_mul, act_one]
  rw [padMainLES_act, swapMainR_act, initC_act _ _ _ rfl]
  have hst4 := asMergeAll_act comb br arith (padLES54 N s) d hsPad
    (zeroSnap d (fun _ _ => false)) (zeroAnc_zeroSnap d _)
  dsimp only [zeroSnap] at hst4 ⊢
  rw [hst4]
  have hr_eq : (fun p : Fin (arity d) => natToBits d ((greedyDiag (padLES54 N s) 0 (arity d))[p.1]!).1) =
      fun p : Fin (arity d) => natToBits d p.1 := by
    funext p; rw [hroot p]
  have hc_eq : (fun p : Fin (arity d) => natToBits d ((greedyDiag (padLES54 N s) 0 (arity d))[p.1]!).2) =
      permRegBits N d hNM (comb.lesToPerm N s hs)⁻¹ := by
    funext p; rw [hroot p]; rfl
  rw [hr_eq, hc_eq, clearRIdx_act _ _ _ rfl, swapCMain_act]

def castEmb (d : ℕ) : Fin (totAS d) ↪ Fin (arity d * d + ancAS d) :=
  (finCongr (totAS_eq d).symm).toEmbedding

def alonsoSchottCircuit (br : BitonicRouting54) (arith : LcgSym54ArithV2) (N d : ℕ) :
    LayeredCircuit (arity d * d + ancAS d) :=
  (alonsoSchottCore br arith N d).mapWires (castEmb d)

lemma alonsoSchottCircuit_size (br : BitonicRouting54) (arith : LcgSym54ArithV2) (N d : ℕ) :
    ((alonsoSchottCircuit br arith N d).size : ℝ) ≤
      (370 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 := by
  dsimp only [alonsoSchottCircuit]; rw [LayeredCircuit.mapWires_size]
  exact alonsoSchottCore_size br arith N d

lemma act_alonsoSchottCircuit_gen (comb : LcgSym54Comb) (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (N d : ℕ) (hNM : N ≤ arity d) (s : Fin N → ℕ) (hs : IsLES N s) :
    act (alonsoSchottCircuit br arith N d).unitary
        (ket (padZero (arity d * d) (ancAS d) (flatReg (arity d) d (padZeroLESBits N d s)))) =
      ket (padZero (arity d * d) (ancAS d) (flatReg (arity d) d (permRegBits N d hNM (comb.lesToPerm N s hs)⁻¹))) := by
  let z0 := padZero (arity d * d) (ancAS d) (flatReg (arity d) d (padZeroLESBits N d s))
  have hz0 : z0 ∘ castEmb d = packAS d (zeroSnap d (padZeroLESBits N d s)) := by
    funext i; exact (congrFun (packAS_zeroSnap_eq_padZero d (padZeroLESBits N d s)) i).symm
  have hact := act_mapWires_ket_singleton (alonsoSchottCore br arith N d) (castEmb d) z0 _
    (by rw [hz0]; exact alonsoSchottCore_act comb br arith N d hNM s hs)
  dsimp only [alonsoSchottCircuit]
  rw [hact]
  congr 1; funext u
  have hu : castEmb d (Fin.cast (totAS_eq d) u) = u := Fin.ext rfl
  conv_lhs => rw [← hu]
  rw [updateOn_apply_emb, packAS_zeroSnap_eq_padZero]
  rfl

lemma act_alonsoSchottCircuit_perm (comb : LcgSym54Comb) (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (N d : ℕ) (hNM : N ≤ arity d) (σ : Equiv.Perm (Fin N)) :
    act (alonsoSchottCircuit br arith N d).unitary
        (ket (padZero (arity d * d) (ancAS d) (flatReg (arity d) d (padZeroLESBits N d (permToLES N σ))))) =
      ket (padZero (arity d * d) (ancAS d) (flatReg (arity d) d (permRegBits N d hNM σ⁻¹))) := by
  have h := act_alonsoSchottCircuit_gen comb br arith N d hNM (permToLES N σ) (comb.permToLES_isLES N σ)
  have hperm : comb.lesToPerm N (permToLES N σ) (comb.permToLES_isLES N σ) = σ := by
    rw [comb.lesToPerm_eq]
    have hsub : (⟨permToLES N σ, comb.permToLES_isLES N σ⟩ : { s : Fin N → ℕ // IsLES N s }) =
        (comb.lesEquivPerm N).symm σ := Subtype.ext (comb.lesEquivPerm_symm_apply N σ).symm
    rw [hsub, Equiv.apply_symm_apply]
  rwa [hperm] at h

lemma act_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act A (c • ψ) = c • act A ψ := by
  ext i; simp [act, Matrix.mulVec_smul]

lemma act_add {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act A (ψ + φ) = act A ψ + act A φ := by
  ext i; simp [act, Matrix.mulVec_add]

lemma act_sum {ι α : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (s : Finset α)
    (f : α → EuclideanSpace ℂ ι) :
    act A (∑ x ∈ s, f x) = ∑ x ∈ s, act A (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext i; simp [act]
  | @insert a s ha ih => rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

def oneCtrlEmb (d : ℕ) : Fin 1 ↪ Fin (arity d * d + (ancAS d + 1)) :=
  sliceEmb (arity d * d + ancAS d) 1 (by omega)

def castEmbA (d : ℕ) : Fin (totAS d) ↪ Fin (arity d * d + (ancAS d + 1)) :=
  sliceEmb 0 (totAS d) (by have := totAS_eq d; omega)

def coreEmb (d : ℕ) : Fin (arity d * d + ancAS d) ↪ Fin (arity d * d + (ancAS d + 1)) :=
  sliceEmb 0 (arity d * d + ancAS d) (by omega)

lemma inRange_trans_castEmbA {d k lo hi : ℕ} (e : Fin k ↪ Fin (totAS d)) (h : InRange lo hi e) :
    InRange lo hi (e.trans (castEmbA d)) := fun i => by
  simp only [Function.Embedding.trans_apply, castEmbA, sliceEmb_apply, Nat.zero_add]
  exact h i

lemma inRange_oneCtrlEmb (d : ℕ) :
    InRange (totAS d) (totAS d + 1) (oneCtrlEmb d) := fun i => by
  have := totAS_eq d
  have hi := i.isLt
  simp only [oneCtrlEmb, sliceEmb_apply]
  omega

def unifMainEmb (d : ℕ) (p : Fin (arity d)) : Fin d ↪ Fin (arity d * d + (ancAS d + 1)) :=
  (mainSlot d p).trans (castEmbA d)

def unifRAncEmb (d : ℕ) : Fin d ↪ Fin (arity d * d + (ancAS d + 1)) :=
  have hle : d ≤ arity d * d := by
    have h1 := arity_one_le d
    nlinarith
  ((Fin.castLEEmb hle).trans (eR d)).trans (castEmbA d)

lemma inRange_unifRAncEmb (d : ℕ) : InRange (oR d) (oC d) (unifRAncEmb d) :=
  inRange_trans_castEmbA _ (inRange_trans _ _ (inRange_eR d))

lemma unif_disj_CM (d : ℕ) (p : Fin (arity d)) :
    ∀ i j, oneCtrlEmb d i ≠ unifMainEmb d p j :=
  disjoint_of_inRange (inRange_oneCtrlEmb d) (inRange_trans_castEmbA _ (inRange_mainSlot d p))
    (by right; dsimp [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC]; omega)

lemma unif_disj_CR (d : ℕ) :
    ∀ i j, oneCtrlEmb d i ≠ unifRAncEmb d j :=
  disjoint_of_inRange (inRange_oneCtrlEmb d) (inRange_unifRAncEmb d)
    (by right; dsimp [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT]; omega)

lemma unif_disj_MR (d : ℕ) (p : Fin (arity d)) :
    ∀ i j, unifMainEmb d p i ≠ unifRAncEmb d j :=
  disjoint_of_inRange (inRange_trans_castEmbA _ (inRange_mainSlot d p)) (inRange_unifRAncEmb d)
    (Or.inl le_rfl)

def unifStepEmb (N d : ℕ) (hNM : N ≤ arity d) (j : Fin N) :
    Fin ((1 + d) + d) ↪ Fin (arity d * d + (ancAS d + 1)) :=
  let j' := Fin.castLE hNM j
  combineEmb (combineEmb (oneCtrlEmb d) (unifMainEmb d j') (unif_disj_CM d j'))
    (unifRAncEmb d) (emb_disjoint_combineEmb (unif_disj_CM d j') (unif_disj_CR d) (unif_disj_MR d j'))

abbrev PartialLES (k : ℕ) := (j : Fin k) → Fin (j.1 + 1)

def padPartialLES (_N k : ℕ) (_hk : k ≤ _N) (d : ℕ) (f : PartialLES k) (p : Fin (arity d)) : Qubits d :=
  if hp : p.1 < k then natToBits d (f ⟨p.1, hp⟩).1 else fun _ => false

def consLES {k : ℕ} (f : PartialLES k) (r : Fin (k + 1)) : PartialLES (k + 1) :=
  fun j => if h : j.1 < k then f ⟨j.1, h⟩ else ⟨r.1, by have := j.isLt; have := r.isLt; omega⟩

def partialEquivProd (k : ℕ) : PartialLES k × Fin (k + 1) ≃ PartialLES (k + 1) where
  toFun p := consLES p.1 p.2
  invFun g := (fun j => g ⟨j.1, by omega⟩, ⟨(g ⟨k, Nat.lt_succ_self k⟩).1, (g ⟨k, Nat.lt_succ_self k⟩).isLt⟩)
  left_inv p := Prod.ext (funext fun j => by simp [consLES, j.isLt]) (Fin.ext (by simp [consLES]))
  right_inv g := funext fun j => Fin.ext (by
    by_cases hj : j.1 < k
    · simp [consLES, hj]
    · have hjk : j.1 = k := by have := j.isLt; omega
      have heq : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hjk
      subst heq
      simp only [consLES, lt_irrefl, ↓reduceDIte])

lemma comp_unifStepEmb {N d : ℕ} (hNM : N ≤ arity d) (k : Fin N)
    (arr : Fin (arity d) → Qubits d) (hk0 : arr (Fin.castLE hNM k) = fun _ => false) :
    updateOn (oneCtrlEmb d) (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d arr)) (fun _ => true) ∘
        unifStepEmb N d hNM k =
      padZero (1 + d) d (Fin.append (fun _ : Fin 1 => true) (fun _ : Fin d => false)) := by
  let j' := Fin.castLE hNM k
  funext u
  refine Fin.addCases (fun ij => ?_) (fun r => ?_) u
  · refine Fin.addCases (fun i => ?_) (fun b => ?_) ij
    · dsimp only [Function.comp_apply, unifStepEmb]
      rw [combineEmb_castAdd, combineEmb_castAdd, updateOn_apply_emb, padZero_castAdd, Fin.append_left]
    · dsimp only [Function.comp_apply, unifStepEmb]
      rw [combineEmb_castAdd, combineEmb_natAdd]
      have hnot : unifMainEmb d j' b ∉ Set.range (oneCtrlEmb d) := by
        rintro ⟨i, hi⟩; exact unif_disj_CM d j' i b hi
      rw [updateOn_apply_not_mem _ _ _ hnot]
      have hlt : (unifMainEmb d j' b).1 < arity d * d :=
        (inRange_trans_castEmbA _ (inRange_mainSlot d j') b).2
      rw [padZero_val_lt _ _ hlt, padZero_castAdd, Fin.append_right]
      have hval : (⟨(unifMainEmb d j' b).1, hlt⟩ : Fin (arity d * d)) = finProdFinEquiv (j', b) :=
        Fin.ext (by simp [unifMainEmb, castEmbA, mainSlot, eMain])
      rw [hval, flatReg, Equiv.symm_apply_apply, hk0]
  · dsimp only [Function.comp_apply, unifStepEmb]
    rw [combineEmb_natAdd]
    have hnot : unifRAncEmb d r ∉ Set.range (oneCtrlEmb d) := by
      rintro ⟨i, hi⟩; exact unif_disj_CR d i r hi
    rw [updateOn_apply_not_mem _ _ _ hnot]
    have hge : arity d * d ≤ (unifRAncEmb d r).1 := by
      have h := (inRange_unifRAncEmb d r).1
      dsimp only [oR] at h; exact h
    rw [padZero_val_ge _ _ hge, padZero_natAdd]

lemma updateOn_unifStepEmb_eq {N d : ℕ} (hNM : N ≤ arity d) (k : Fin N)
    (arr : Fin (arity d) → Qubits d) (val : Qubits d) :
    updateOn (unifStepEmb N d hNM k)
        (updateOn (oneCtrlEmb d) (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d arr)) (fun _ => true))
        (padZero (1 + d) d (Fin.append (fun _ : Fin 1 => true) val)) =
      updateOn (oneCtrlEmb d)
        (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (Function.update arr (Fin.castLE hNM k) val)))
        (fun _ => true) := by
  let j' := Fin.castLE hNM k
  funext u
  by_cases hC : u ∈ Set.range (oneCtrlEmb d)
  · rcases hC with ⟨i, rfl⟩
    have hmem : oneCtrlEmb d i = unifStepEmb N d hNM k (Fin.castAdd d (Fin.castAdd d i)) := by
      dsimp only [unifStepEmb]; simp
    conv_lhs => rw [hmem]
    rw [updateOn_apply_emb, padZero_castAdd, Fin.append_left, updateOn_apply_emb]
  · rw [updateOn_apply_not_mem (oneCtrlEmb d) _ _ hC]
    by_cases hM : u ∈ Set.range (unifMainEmb d j')
    · rcases hM with ⟨b, rfl⟩
      have hmem : unifMainEmb d j' b = unifStepEmb N d hNM k (Fin.castAdd d (Fin.natAdd 1 b)) := by
        dsimp only [unifStepEmb, j']; simp
      conv_lhs => rw [hmem]
      rw [updateOn_apply_emb, padZero_castAdd, Fin.append_right]
      have hlt : (unifMainEmb d j' b).1 < arity d * d :=
        (inRange_trans_castEmbA _ (inRange_mainSlot d j') b).2
      rw [padZero_val_lt _ _ hlt]
      have hval : (⟨(unifMainEmb d j' b).1, hlt⟩ : Fin (arity d * d)) = finProdFinEquiv (j', b) :=
        Fin.ext (by simp [unifMainEmb, castEmbA, mainSlot, eMain])
      dsimp only [j']
      rw [hval, flatReg, Equiv.symm_apply_apply, Function.update_self]
    · by_cases hR : u ∈ Set.range (unifRAncEmb d)
      · rcases hR with ⟨r, rfl⟩
        have hmem : unifRAncEmb d r = unifStepEmb N d hNM k (Fin.natAdd (1 + d) r) := by
          dsimp only [unifStepEmb]; simp
        conv_lhs => rw [hmem]
        rw [updateOn_apply_emb, padZero_natAdd]
        have hge : arity d * d ≤ (unifRAncEmb d r).1 := by
          have h := (inRange_unifRAncEmb d r).1
          dsimp only [oR] at h; exact h
        rw [padZero_val_ge _ _ hge]
      · have hnot : u ∉ Set.range (unifStepEmb N d hNM k) := by
          rintro ⟨x, hx⟩
          refine Fin.addCases (fun ij => ?_) (fun r => ?_) x hx
          · refine Fin.addCases (fun i => ?_) (fun b => ?_) ij
            · simp only [unifStepEmb, combineEmb_castAdd]; exact fun hi => hC ⟨i, hi⟩
            · simp only [unifStepEmb, combineEmb_castAdd, combineEmb_natAdd]; exact fun hb => hM ⟨b, hb⟩
          · simp only [unifStepEmb, combineEmb_natAdd]; exact fun hr => hR ⟨r, hr⟩
        rw [updateOn_apply_not_mem _ _ _ hnot, updateOn_apply_not_mem (oneCtrlEmb d) _ _ hC]
        by_cases hlt : u.1 < arity d * d
        · rw [padZero_val_lt _ _ hlt, padZero_val_lt _ _ hlt]
          simp only [flatReg]
          have hne : (finProdFinEquiv.symm ⟨u.1, hlt⟩).1 ≠ j' := by
            intro hfst
            apply hM
            refine ⟨(finProdFinEquiv.symm ⟨u.1, hlt⟩).2, Fin.ext ?_⟩
            have heq : finProdFinEquiv (j', (finProdFinEquiv.symm ⟨u.1, hlt⟩).2) = ⟨u.1, hlt⟩ := by
              rw [← hfst]; exact finProdFinEquiv.apply_symm_apply _
            have hv := congrArg Fin.val heq
            simp only [unifMainEmb, castEmbA, mainSlot, eMain, Function.Embedding.trans_apply,
              slotInReg_apply, regEmb_apply, sliceEmb_apply, Nat.zero_add]
            exact hv
          rw [Function.update_of_ne hne]
        · have hge : arity d * d ≤ u.1 := Nat.le_of_not_lt hlt
          rw [padZero_val_ge _ _ hge, padZero_val_ge _ _ hge]

def unifPermCircuit (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (N d : ℕ) (hNM : N ≤ arity d) : LayeredCircuit (arity d * d + (ancAS d + 1)) :=
  let prepLES := LayeredCircuit.seqList ((List.finRange N).map fun j =>
    (br.unifPrefixCircuit d (j.1 + 1) (Nat.succ_pos j.1)
      (by have := j.isLt; rw [← arity_eq_two_pow d]; omega)).mapWires (unifStepEmb N d hNM j))
  LayeredCircuit.seqList
    [ (arith.setConstMSBCircuit 1 1).mapWires (oneCtrlEmb d)
    , prepLES
    , (arith.setConstMSBCircuit 1 1).mapWires (oneCtrlEmb d)
    , (alonsoSchottCircuit br arith N d).mapWires (coreEmb d) ]

lemma unifPermCircuit_size (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (N d : ℕ) (_h1N : 1 ≤ N) (h1d : 1 ≤ d) (hNM : N ≤ arity d) :
    ((unifPermCircuit br arith N d hNM).size : ℝ) ≤
      (500 + 16 * br.C_sort + br.C_unif) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 := by
  dsimp only [unifPermCircuit]
  rw [LayeredCircuit.seqList_size]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.cast_add]
  rw [LayeredCircuit.mapWires_size, LayeredCircuit.mapWires_size]
  have hsc : ((arith.setConstMSBCircuit 1 1).size : ℝ) ≤ 1 := by exact_mod_cast arith.setConstMSBCircuit_size 1 1
  have hprep : ((LayeredCircuit.seqList ((List.finRange N).map fun j =>
      (br.unifPrefixCircuit d (j.1 + 1) (Nat.succ_pos j.1)
        (by have := j.isLt; rw [← arity_eq_two_pow d]; omega)).mapWires (unifStepEmb N d hNM j))).size : ℝ) ≤
      (N : ℝ) * (br.C_unif * ((d + 1 : ℕ) : ℝ) ^ 2) := by
    refine seqList_fin_size_le_real _ _ fun j => ?_
    rw [LayeredCircuit.mapWires_size]
    simpa [Nat.cast_add, Nat.cast_one] using
      br.unifPrefixCircuit_size d (j.1 + 1) (Nat.succ_pos j.1)
        (by have := j.isLt; rw [← arity_eq_two_pow d]; omega)
  have has := alonsoSchottCircuit_size br arith N d
  have har1 : (1 : ℝ) ≤ (arity d : ℝ) := by exact_mod_cast arity_one_le d
  have hN_le : (N : ℝ) ≤ (arity d : ℝ) := by exact_mod_cast hNM
  have hd1 : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hsq : ((d + 1 : ℕ) : ℝ) ^ 2 ≤ ((d + 1 : ℕ) : ℝ) ^ 4 :=
    pow_le_pow_right₀ hd1 (by omega)
  have hd4 : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 4 := one_le_pow₀ hd1
  have h1c : (1 : ℝ) ≤ (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 := by nlinarith
  have hc_unif : 0 < br.C_unif := br.hC_unif_pos
  have hc_sort : 0 < br.C_sort := br.hC_sort_pos
  have hprep2 : (N : ℝ) * (br.C_unif * ((d + 1 : ℕ) : ℝ) ^ 2) ≤
      br.C_unif * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 := by
    have h := mul_le_mul hN_le (mul_le_mul_of_nonneg_left hsq (le_of_lt hc_unif))
      (by positivity) (by positivity)
    linarith
  have hcs_nn : (0 : ℝ) ≤ 2 * br.C_sort * ((arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4) := by positivity
  have hbound : (2 : ℝ) + br.C_unif * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 +
      (370 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 ≤
      (500 + 16 * br.C_sort + br.C_unif) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 := by
    have hdiff : (500 + 16 * br.C_sort + br.C_unif) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 -
        ((2 : ℝ) + br.C_unif * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4 +
          (370 + 14 * br.C_sort) * (arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4) =
        130 * ((arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4) - 2 +
          2 * br.C_sort * ((arity d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 4) := by ring
    linarith [h1c, hcs_nn, hdiff]
  push_cast at hsc hprep hprep2 has hbound ⊢
  linarith [hsc, hprep, hprep2, has, hbound]

lemma act_unifPermCircuit (comb : LcgSym54Comb) (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (N d : ℕ) (hNM : N ≤ arity d) :
    act (unifPermCircuit br arith N d hNM).unitary (ket (fun _ => false)) =
      ((1 / Real.sqrt (Nat.factorial N : ℝ) : ℝ) : ℂ) •
        ∑ σ : Equiv.Perm (Fin N),
          ket (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (permRegBits N d hNM σ))) := by
  have h1bit : natToBits 1 1 0 = true := by
    have ht := comb.natToBits_comp_revPerm 1 1 0
    have hr : (0 : Fin 1).rev = 0 := Fin.ext (by omega)
    rw [hr] at ht; simpa using ht
  dsimp only [unifPermCircuit]
  simp only [LayeredCircuit.seqList, LayeredCircuit.seq_unitary, LayeredCircuit.id_unitary, act_mul, act_one]
  -- Step 1: set oneCtrl = true
  have hs1 : act ((arith.setConstMSBCircuit 1 1).mapWires (oneCtrlEmb d)).unitary (ket (fun _ => false)) =
      ket (updateOn (oneCtrlEmb d) (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (fun _ _ => false))) (fun _ => true)) := by
    rw [act_setConstOn]
    have hzero : (fun _ : Fin (arity d * d + (ancAS d + 1)) => false) =
        padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (fun _ _ => false)) := by
      funext u; rw [flatReg_zero]; by_cases h : u.1 < arity d * d
      · rw [padZero_val_lt _ _ h]
      · rw [padZero_val_ge _ _ (Nat.le_of_not_lt h)]
    have hval : (fun j : Fin 1 => xor false (natToBits 1 1 j)) = fun _ => true := by
      funext j; have hj : j = 0 := Fin.ext (by omega); subst hj; simp [h1bit]
    rw [hval, hzero]
  -- Step 2: loop generating uniform superposition over PartialLES k
  let invState : (k : ℕ) → k ≤ N → EuclideanSpace ℂ (Qubits (arity d * d + (ancAS d + 1))) := fun k hk =>
    ((1 / Real.sqrt (Nat.factorial k : ℝ) : ℝ) : ℂ) •
      ∑ f : PartialLES k,
        ket (updateOn (oneCtrlEmb d)
          (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (padPartialLES N k hk d f)))
          (fun _ => true))
  have hinv0 : invState 0 (Nat.zero_le N) =
      ket (updateOn (oneCtrlEmb d) (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (fun _ _ => false))) (fun _ => true)) := by
    dsimp only [invState]
    rw [Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, div_one, Complex.ofReal_one, one_smul]
    have hpad0 : ∀ f : PartialLES 0, padPartialLES N 0 (Nat.zero_le N) d f = fun _ _ => false :=
      fun _ => funext fun _ => by simp [padPartialLES]
    rw [Fintype.sum_unique, hpad0]
  let prepCirc := LayeredCircuit.seqList ((List.finRange N).map fun j =>
    (br.unifPrefixCircuit d (j.1 + 1) (Nat.succ_pos j.1)
      (by have := j.isLt; rw [← arity_eq_two_pow d]; omega)).mapWires (unifStepEmb N d hNM j))
  have hgen : ∀ (lcs : List (Fin N)), ∀ (k : ℕ) (hk : k ≤ N),
      lcs = (List.finRange N).drop k →
      act (LayeredCircuit.seqList (lcs.map fun j =>
          (br.unifPrefixCircuit d (j.1 + 1) (Nat.succ_pos j.1)
            (by have := j.isLt; rw [← arity_eq_two_pow d]; omega)).mapWires (unifStepEmb N d hNM j))).unitary
          (invState k hk) = invState N le_rfl := by
    intro lcs
    induction lcs with
    | nil =>
      intro k hk hdrop
      have hlen := congrArg List.length hdrop
      simp only [List.length_nil, List.length_drop, List.length_finRange] at hlen
      have hkn : k = N := by omega
      subst hkn; simp [LayeredCircuit.seqList, act_one]
    | cons j rest ih =>
      intro k hk hdrop
      have hlen := congrArg List.length hdrop
      simp only [List.length_cons, List.length_drop, List.length_finRange] at hlen
      have hklt : k < N := by omega
      have hj : j = ⟨k, hklt⟩ := by
        have h0 := congrArg List.head? hdrop
        rw [List.head?_drop, List.getElem?_eq_getElem (by rw [List.length_finRange]; exact hklt),
          List.getElem_finRange] at h0
        exact Option.some.inj h0
      have hdrop' : rest = (List.finRange N).drop (k + 1) := by
        have ht := congrArg List.tail hdrop
        simpa [List.tail_drop] using ht
      subst hj
      simp only [List.map_cons, LayeredCircuit.seqList, LayeredCircuit.seq_unitary, act_mul]
      have hstep : act ((br.unifPrefixCircuit d (k + 1) (Nat.succ_pos k)
            (by rw [← arity_eq_two_pow d]; omega)).mapWires (unifStepEmb N d hNM ⟨k, hklt⟩)).unitary
            (invState k hk) = invState (k + 1) hklt := by
        dsimp only [invState]
        rw [act_smul, act_sum]
        have hterm : ∀ f : PartialLES k,
            act ((br.unifPrefixCircuit d (k + 1) (Nat.succ_pos k)
              (by rw [← arity_eq_two_pow d]; omega)).mapWires (unifStepEmb N d hNM ⟨k, hklt⟩)).unitary
              (ket (updateOn (oneCtrlEmb d)
                (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (padPartialLES N k hk d f)))
                (fun _ => true))) =
              ((1 / Real.sqrt ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) •
                ∑ r : Fin (k + 1),
                  ket (updateOn (oneCtrlEmb d)
                    (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (padPartialLES N (k + 1) hklt d (consLES f r))))
                    (fun _ => true)) := by
          intro f
          let z := updateOn (oneCtrlEmb d)
            (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (padPartialLES N k hk d f)))
            (fun _ => true)
          have hz_comp := comp_unifStepEmb hNM ⟨k, hklt⟩ (padPartialLES N k hk d f)
            (by dsimp only [padPartialLES, Fin.castLE]; rw [dif_neg (Nat.lt_irrefl k)])
          have hsum := LcgSym54.act_mapWires_ket_sum
            (br.unifPrefixCircuit d (k + 1) (Nat.succ_pos k) (by rw [← arity_eq_two_pow d]; omega))
            (unifStepEmb N d hNM ⟨k, hklt⟩) z Finset.univ
            (fun _ => ((1 / Real.sqrt ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ))
            (fun r : Fin (k + 1) => padZero (1 + d) d (Fin.append (fun _ : Fin 1 => true) (natToBits d r.1)))
            (by rw [hz_comp, br.act_unifPrefixCircuit_true, Finset.smul_sum])
          rw [hsum, ← Finset.smul_sum]
          congr 1; refine Finset.sum_congr rfl fun r _ => ?_
          rw [updateOn_unifStepEmb_eq hNM ⟨k, hklt⟩]
          congr 4; funext p; dsimp only [padPartialLES, consLES]
          by_cases hpk : p.1 = k
          · have hlt1 : p.1 < k + 1 := by omega
            have hnk : ¬ p.1 < k := by omega
            have hp_eq : p = Fin.castLE hNM ⟨k, hklt⟩ := Fin.ext hpk
            rw [dif_pos hlt1, dif_neg hnk, Function.update_apply, if_pos hp_eq]
          · have hne : p ≠ Fin.castLE hNM ⟨k, hklt⟩ := fun h => hpk (congrArg Fin.val h)
            rw [Function.update_of_ne hne]
            dsimp only [padPartialLES]
            by_cases hlt : p.1 < k
            · have hlt1 : p.1 < k + 1 := by omega
              rw [dif_pos hlt, dif_pos hlt1, dif_pos hlt]
            · have hlt1 : ¬ p.1 < k + 1 := by omega
              rw [dif_neg hlt, dif_neg hlt1]
        simp_rw [hterm]
        rw [← Finset.smul_sum, smul_smul]
        have hsc : ((1 / Real.sqrt (Nat.factorial k : ℝ) : ℝ) : ℂ) *
            ((1 / Real.sqrt ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) =
            ((1 / Real.sqrt (Nat.factorial (k + 1) : ℝ) : ℝ) : ℂ) := by
          norm_cast
          rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_comm (Real.sqrt _), one_div_mul_one_div]
        rw [hsc]
        congr 1
        rw [show (∑ x : PartialLES k, ∑ r : Fin (k + 1),
            ket (updateOn (oneCtrlEmb d) (padZero (arity d * d) (ancAS d + 1)
              (flatReg (arity d) d (padPartialLES N (k + 1) hklt d (consLES x r)))) (fun _ => true))) =
          ∑ p : PartialLES k × Fin (k + 1),
            ket (updateOn (oneCtrlEmb d) (padZero (arity d * d) (ancAS d + 1)
              (flatReg (arity d) d (padPartialLES N (k + 1) hklt d (partialEquivProd k p)))) (fun _ => true)) from
          (Fintype.sum_prod_type (fun p : PartialLES k × Fin (k + 1) =>
            ket (updateOn (oneCtrlEmb d) (padZero (arity d * d) (ancAS d + 1)
              (flatReg (arity d) d (padPartialLES N (k + 1) hklt d (partialEquivProd k p)))) (fun _ => true)))).symm]
        exact Fintype.sum_equiv (partialEquivProd k) _ _ (fun _ => rfl)
      rw [hstep]
      exact ih (k + 1) hklt hdrop'
  have hs2 := hgen (List.finRange N) 0 (Nat.zero_le N) (by simp)
  rw [hinv0] at hs2
  -- Step 3: uncompute oneCtrl to false
  have hs3 : act ((arith.setConstMSBCircuit 1 1).mapWires (oneCtrlEmb d)).unitary (invState N le_rfl) =
      ((1 / Real.sqrt (Nat.factorial N : ℝ) : ℝ) : ℂ) •
        ∑ f : PartialLES N,
          ket (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (padPartialLES N N le_rfl d f))) := by
    dsimp only [invState]
    rw [act_smul, act_sum]
    congr 1; refine Finset.sum_congr rfl fun f _ => ?_
    rw [act_setConstOn]
    congr 1; funext u
    by_cases hC : u ∈ Set.range (oneCtrlEmb d)
    · rcases hC with ⟨i, rfl⟩
      have hi0 : i = 0 := Fin.ext (by omega); subst hi0
      rw [updateOn_apply_emb, updateOn_apply_emb, h1bit, Bool.xor_self]
      have hge : arity d * d ≤ (oneCtrlEmb d 0).1 := by
        have h := (inRange_oneCtrlEmb d 0).1; dsimp only [totAS, oPA, oTmp, oFlag, oDR, oSA, oTr, oB, oOut, oT, oC, oR] at h; omega
      rw [padZero_val_ge _ _ hge]
    · rw [updateOn_apply_not_mem (oneCtrlEmb d) _ _ hC, updateOn_apply_not_mem (oneCtrlEmb d) _ _ hC]
  -- Step 4: apply alonsoSchottCircuit via coreEmb across the superposition
  have hs4 : ∀ f : PartialLES N,
      act ((alonsoSchottCircuit br arith N d).mapWires (coreEmb d)).unitary
          (ket (padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (padPartialLES N N le_rfl d f)))) =
        ket (padZero (arity d * d) (ancAS d + 1)
          (flatReg (arity d) d (permRegBits N d hNM (comb.lesToPerm N ((lesEquivPi N).symm f).1 ((lesEquivPi N).symm f).2)⁻¹))) := by
    intro f
    let s := (lesEquivPi N).symm f
    have hpad_eq : padPartialLES N N le_rfl d f = padZeroLESBits N d s.1 := by
      funext p; by_cases hp : p.1 < N
      · simp [padPartialLES, padZeroLESBits, hp, s, lesEquivPi]
      · simp [padPartialLES, padZeroLESBits, hp]
    let z := padZero (arity d * d) (ancAS d + 1) (flatReg (arity d) d (padPartialLES N N le_rfl d f))
    have hz_core : z ∘ coreEmb d = padZero (arity d * d) (ancAS d) (flatReg (arity d) d (padZeroLESBits N d s.1)) := by
      funext u
      dsimp only [Function.comp_apply, z, coreEmb, sliceEmb_apply]
      rw [hpad_eq]
      by_cases h : u.1 < arity d * d
      · rw [padZero_val_lt _ _ (by simpa using h), padZero_val_lt _ _ h]
        congr 1; exact Fin.ext (Nat.zero_add u.1)
      · have hge := Nat.le_of_not_lt h
        rw [padZero_val_ge _ _ (by simpa using hge), padZero_val_ge _ _ hge]
    have hact := act_mapWires_ket_singleton (alonsoSchottCircuit br arith N d) (coreEmb d) z _
      (by rw [hz_core]; exact act_alonsoSchottCircuit_gen comb br arith N d hNM s.1 s.2)
    rw [hact]
    congr 1; funext u
    by_cases hu : u.1 < arity d * d + ancAS d
    · have hmem : u = coreEmb d ⟨u.1, hu⟩ := Fin.ext (Nat.zero_add u.1).symm
      conv_lhs => rw [hmem]
      rw [updateOn_apply_emb]
      by_cases h : u.1 < arity d * d
      · rw [padZero_val_lt _ _ (by simpa using h), padZero_val_lt _ _ h]
      · have hge := Nat.le_of_not_lt h
        rw [padZero_val_ge _ _ (by simpa using hge), padZero_val_ge _ _ hge]
    · have hge : arity d * d ≤ u.1 := by omega
      have hnot : u ∉ Set.range (coreEmb d) := by
        rintro ⟨i, hi⟩; have := i.isLt; have hv := congrArg Fin.val hi; simp only [coreEmb, sliceEmb_apply] at hv; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]
      dsimp only [z]
      rw [padZero_val_ge _ _ hge, padZero_val_ge _ _ hge]
  rw [hs1, hs2, hs3, act_smul, act_sum]
  simp_rw [hs4]
  congr 1
  let ePerm : PartialLES N ≃ Equiv.Perm (Fin N) :=
    ((lesEquivPi N).symm.trans (comb.lesEquivPerm N)).trans (Equiv.inv (Equiv.Perm (Fin N)))
  refine Fintype.sum_equiv ePerm _ _ fun f => ?_
  dsimp only [ePerm, Equiv.trans_apply]
  rw [Equiv.inv_apply, ← comb.lesToPerm_eq]

def buildAlonsoSchottSil54 (comb : LcgSym54Comb) (br : BitonicRouting54) (arith : LcgSym54ArithV2) :
    QuantumLTF.Membership.Supplement.AlonsoSchottSil54 where
  C_as := 500 + 16 * br.C_sort + br.C_unif
  C_as_pos := by linarith [br.hC_sort_pos, br.hC_unif_pos]
  alonsoSchottAnc _ d := ancAS d
  alonsoSchottCircuit N d _ _ _ := alonsoSchottCircuit br arith N d
  alonsoSchottCircuit_size N d h1N h1d hNM := by
    have h := alonsoSchottCircuit_size br arith N d
    have hcs : 0 ≤ br.C_sort := le_of_lt br.hC_sort_pos
    have hcu : 0 ≤ br.C_unif := le_of_lt br.hC_unif_pos
    have har : (0 : ℝ) ≤ (arity d : ℝ) := Nat.cast_nonneg _
    have hd4 : (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 4 := by positivity
    nlinarith [mul_nonneg har hd4]
  act_alonsoSchottCircuit N d _ _ hNM σ := act_alonsoSchottCircuit_perm comb br arith N d hNM σ
  unifPermAnc _ d := ancAS d + 1
  unifPermCircuit N d _ _ hNM := unifPermCircuit br arith N d hNM
  unifPermCircuit_size N d h1N h1d hNM := unifPermCircuit_size br arith N d h1N h1d hNM
  act_unifPermCircuit N d _ _ hNM := act_unifPermCircuit comb br arith N d hNM

end Aux_w54_as

theorem solution : Nonempty QuantumLTF.Membership.Supplement.AlonsoSchottSil54 := by
  rcases QuantumLTF.Membership.Supplement.bitonic_routing_54 with ⟨br⟩
  rcases QuantumLTF.Membership.Supplement.lcg_sym_comb_54 with ⟨comb⟩
  rcases QuantumLTF.Membership.Supplement.lcg_sym_arith_54 with ⟨arith⟩
  exact ⟨Aux_w54_as.buildAlonsoSchottSil54 comb br arith⟩



