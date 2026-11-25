-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.lcg_sym_arith_54
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T03:21:06.546824+00:00
-- url     : https://prove2.me/submissions/0ac99132-8635-4775-91de-dd0ad0e55353

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
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2

set_option autoImplicit false

namespace Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router

lemma act_subReg_perm {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
    (f : Qubits main → Qubits main) (hlc : lc.ImplementsOnClean (permMat f))
    (embMain : Fin main ↪ Fin m) (embAnc : Fin anc ↪ Fin m)
    (hdisj : ∀ i j, embMain i ≠ embAnc j) (z : Qubits m)
    (hclean : ∀ j : Fin anc, z (embAnc j) = false) :
    act (lc.mapWires (combineEmb embMain embAnc hdisj)).unitary (ket z) =
      ket (updateOn embMain z (f (z ∘ embMain))) := by
  have hact := act_mapWires_implementsOnClean lc (permMat f) hlc
    (combineEmb embMain embAnc hdisj) z (fun j => by simpa using hclean j)
  dsimp only at hact
  rw [hact, Finset.sum_eq_single (f (z ∘ ((Fin.castAddEmb anc).trans (combineEmb embMain embAnc hdisj))))]
  · simp [permMat, castAddEmb_trans_combineEmb]
  · intro y _ hy; simp [permMat, hy]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma permMat_id {ι : Type*} [DecidableEq ι] : permMat (id : ι → ι) = 1 := by
  ext y z
  simp [permMat, Matrix.one_apply]

lemma permMat_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → ι) :
    permMat f * permMat g = permMat (f ∘ g) := by
  ext y z
  simp only [Matrix.mul_apply, permMat, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (g z)]
  · simp
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma seqClean_perm {main anc₁ anc₂ : ℕ}
    (lc₁ : LayeredCircuit (main + anc₁)) (lc₂ : LayeredCircuit (main + anc₂))
    {f g : Qubits main → Qubits main}
    (h₁ : lc₁.ImplementsOnClean (permMat f)) (h₂ : lc₂.ImplementsOnClean (permMat g)) :
    (seqClean lc₁ lc₂).ImplementsOnClean (permMat (g ∘ f)) := by
  have h := seqClean_implements lc₁ lc₂ (permMat f) (permMat g) h₁ h₂
  rwa [permMat_mul] at h

lemma adj_implementsOnClean_perm {main anc : ℕ} (lc : LayeredCircuit (main + anc))
    {f g : Qubits main → Qubits main}
    (_hleft : ∀ x, g (f x) = x) (hright : ∀ x, f (g x) = x)
    (hlc : lc.ImplementsOnClean (permMat f)) :
    lc.adj.ImplementsOnClean (permMat g) := by
  apply implementsOnClean_of_act_perm
  intro x
  have hfg := act_ket_of_implementsOnClean_perm hlc (g x)
  rw [hright x] at hfg
  have hadj := congrArg (act lc.adj.unitary) hfg.symm
  conv_rhs at hadj =>
    rw [← act_mul, LayeredCircuit.adj_unitary,
      Matrix.mem_unitaryGroup_iff'.mp lc.unitary_mem_unitaryGroup, act_one]
  exact hadj

lemma implementsOnClean_id_perm {main anc : ℕ} :
    (LayeredCircuit.id (main + anc)).ImplementsOnClean (permMat id) := by
  apply implementsOnClean_of_act_perm
  intro x; simp [LayeredCircuit.id_unitary, act_one]

lemma act_mapWires_perm {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
    (f : Qubits main → Qubits main) (hlc : lc.ImplementsOnClean (permMat f))
    (emb : Fin (main + anc) ↪ Fin m) (z : Qubits m)
    (hclean : ∀ j : Fin anc, z (emb (Fin.natAdd main j)) = false) :
    let embMain : Fin main ↪ Fin m := (Fin.castAddEmb anc).trans emb
    act (lc.mapWires emb).unitary (ket z) = ket (updateOn embMain z (f (z ∘ embMain))) := by
  intro embMain
  have h := act_mapWires_implementsOnClean lc (permMat f) hlc emb z hclean
  dsimp only at h
  dsimp only [embMain]
  rw [h, Finset.sum_eq_single (f (z ∘ ((Fin.castAddEmb anc).trans emb)))]
  · simp [permMat]
  · intro y _ hy; simp [permMat, hy]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem


lemma bitsToNatLSB_rev {q : ℕ} (b : Qubits q) :
    bitsToNatLSB (fun j : Fin q => b j.rev) = bitsToNat b := by
  dsimp only [bitsToNatLSB, bitsToNat]
  refine Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin q)) _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Fin.val_rev]
  have hi := i.isLt
  have heq : i.1 = q - 1 - (q - (i.1 + 1)) := by omega
  rw [← heq]

lemma natToBits_eq_rev_natToBitsLSB (q k : ℕ) (hk : k < 2 ^ q) :
    (fun j : Fin q => natToBits q k j.rev) = natToBitsLSB q k := by
  have hbits : bitsToNat (natToBits q k) = k := by
    rw [← bitsEquivFin_apply]
    simp [natToBits, Nat.mod_eq_of_lt hk]
  have hrev : bitsToNatLSB (fun j : Fin q => natToBits q k j.rev) = k := by
    rw [bitsToNatLSB_rev, hbits]
  rw [← natToBitsLSB_bitsToNatLSB (fun j : Fin q => natToBits q k j.rev), hrev]

lemma natToBits_apply {q k : ℕ} (hk : k < 2 ^ q) (i : Fin q) :
    natToBits q k i = natToBitsLSB q k i.rev := by
  have h := congrFun (natToBits_eq_rev_natToBitsLSB q k hk) i.rev
  simpa [Fin.rev_rev] using h

lemma bitsToNatLSB_all_false (w : ℕ) : bitsToNatLSB (fun _ : Fin w => false) = 0 := by
  simp [bitsToNatLSB]

lemma bitsToNatLSB_add_two_pow_rev (w : ℕ) (x : Qubits w) :
    bitsToNatLSB (fun i => !x i) + bitsToNatLSB x = 2 ^ w - 1 := by
  induction w with
  | zero => simp [bitsToNatLSB]
  | succ w ih =>
    simp only [bitsToNatLSB, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero]
    have hih := ih (fun i => x i.succ)
    have h1 : (∑ i : Fin w, if !x i.succ then 2 ^ (i.1 + 1) else 0) =
        2 * ∑ i : Fin w, if !x i.succ then 2 ^ i.1 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [pow_succ']
    have h2 : (∑ i : Fin w, if x i.succ then 2 ^ (i.1 + 1) else 0) =
        2 * ∑ i : Fin w, if x i.succ then 2 ^ i.1 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [pow_succ']
    dsimp only [bitsToNatLSB] at hih
    rw [h1, h2]
    have hp : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    have hb : (if !x 0 then 1 else 0) + (if x 0 then 1 else 0) = 1 := by
      cases x 0 <;> rfl
    rw [pow_succ']
    omega

lemma bitsToNatLSB_complement_lt_iff (w : ℕ) (a b : Qubits w) :
    (2 ^ w ≤ bitsToNatLSB (fun i => !a i) + bitsToNatLSB b) ↔
      bitsToNatLSB a < bitsToNatLSB b := by
  have hc := bitsToNatLSB_add_two_pow_rev w a
  have ha := bitsToNatLSB_lt w a
  omega

/-! ### Part 2: Zero-Ancilla Register Primitives -/

/-- Swaps two distinct wires `a` and `b` using 3 CNOT gates. -/
def swapWiresGate {m : ℕ} (a b : Fin m) (hne : a ≠ b) : LayeredCircuit m :=
  (cnotGate a b hne).seq ((cnotGate b a hne.symm).seq (cnotGate a b hne))

@[simp] lemma swapWiresGate_size {m : ℕ} (a b : Fin m) (hne : a ≠ b) :
    (swapWiresGate a b hne).size = 3 := by
  simp [swapWiresGate]

@[simp] lemma swapWiresGate_depth {m : ℕ} (a b : Fin m) (hne : a ≠ b) :
    (swapWiresGate a b hne).depth = 3 := by
  simp [swapWiresGate]

lemma swapWiresGate_usesOnly {m : ℕ} (a b : Fin m) (hne : a ≠ b) :
    (swapWiresGate a b hne).UsesOnly {a, b} := by
  refine LayeredCircuit.seq_usesOnly (cnotGate_usesOnly a b hne)
    (LayeredCircuit.seq_usesOnly ?_ (cnotGate_usesOnly a b hne))
  exact (cnotGate_usesOnly b a hne.symm).mono (by intro w hw; simp at hw ⊢; tauto)

lemma act_swapWiresGate_ket {m : ℕ} (a b : Fin m) (hne : a ≠ b) (z : Qubits m) :
    act (swapWiresGate a b hne).unitary (ket z) =
      ket (fun w => if w = a then z b else if w = b then z a else z w) := by
  simp only [swapWiresGate, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket]
  congr 1; funext w
  by_cases hwa : w = a
  · subst hwa
    simp only [Function.update_self, Function.update_of_ne hne, Function.update_of_ne hne.symm, ↓reduceIte]
    generalize z w = vw; generalize z b = vb; cases vw <;> cases vb <;> rfl
  · by_cases hwb : w = b
    · subst hwb
      simp only [Function.update_self, Function.update_of_ne hne, Function.update_of_ne hwa,
        if_neg hwa, ↓reduceIte]
      generalize z a = va; generalize z w = vw; cases va <;> cases vw <;> rfl
    · simp [hwa, hwb]

private def copyPrefixCircuit (w : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit (w + w)
  | 0, _ => LayeredCircuit.id (w + w)
  | k + 1, hk =>
    let prev := copyPrefixCircuit w k (by omega)
    let c : Fin (w + w) := ⟨k, by omega⟩
    let t : Fin (w + w) := ⟨w + k, by omega⟩
    have hct : c ≠ t := Fin.ne_of_val_ne (by dsimp [c, t]; omega)
    prev.seq (cnotGate c t hct)

private lemma copyPrefixCircuit_size (w k : ℕ) (hk : k ≤ w) :
    (copyPrefixCircuit w k hk).size = k := by
  induction k with
  | zero => simp [copyPrefixCircuit]
  | succ k ih => simp [copyPrefixCircuit, ih (by omega)]

private lemma act_copyPrefixCircuit_ket (w k : ℕ) (hk : k ≤ w) (z : Qubits (w + w)) :
    act (copyPrefixCircuit w k hk).unitary (ket z) =
      ket (fun u => if h : w ≤ u.1 ∧ u.1 < w + k then
        xor (z u) (z ⟨u.1 - w, by omega⟩) else z u) := by
  induction k with
  | zero =>
    simp only [copyPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u; rw [dif_neg (by omega)]
  | succ k ih =>
    dsimp only [copyPrefixCircuit]
    rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega), act_cnotGate_ket]
    congr 1; funext u
    let c : Fin (w + w) := ⟨k, by omega⟩
    let t : Fin (w + w) := ⟨w + k, by omega⟩
    by_cases hut : u = t
    · subst hut
      have ht_new : w ≤ t.1 ∧ t.1 < w + (k + 1) := by dsimp [t]; omega
      rw [Function.update_self, dif_pos ht_new]
      have hnc : ¬ (w ≤ c.1 ∧ c.1 < w + k) := by dsimp [c]; omega
      have hnt : ¬ (w ≤ t.1 ∧ t.1 < w + k) := by dsimp [t]; omega
      rw [dif_neg hnc, dif_neg hnt]
      have hsub : (⟨t.1 - w, by omega⟩ : Fin (w + w)) = c := Fin.ext (by simp [c, t])
      rw [hsub]
    · rw [Function.update_of_ne hut]
      by_cases hu : w ≤ u.1 ∧ u.1 < w + k
      · have hu' : w ≤ u.1 ∧ u.1 < w + (k + 1) := by omega
        rw [dif_pos hu, dif_pos hu']
      · have hu' : ¬ (w ≤ u.1 ∧ u.1 < w + (k + 1)) := by
          intro h; apply hu; refine ⟨h.1, ?_⟩
          by_contra hge
          apply hut; apply Fin.ext; dsimp [t]; omega
        rw [dif_neg hu, dif_neg hu']

/-- Bitwise XOR copy `(a, b) ↦ (a, b ^^^ a)` using `w` CNOT gates (`0` ancillas). -/
def copyRegCircuit (w : ℕ) : LayeredCircuit ((w + w) + 0) :=
  copyPrefixCircuit w w le_rfl

@[simp] lemma copyRegCircuit_size (w : ℕ) : (copyRegCircuit w).size = w :=
  copyPrefixCircuit_size w w le_rfl


lemma copyRegCircuit_implements (w : ℕ) :
    (copyRegCircuit w).ImplementsOnClean (permMat (copyRegFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [copyRegCircuit]
  have h0 : padZero (w + w) 0 x = x := by
    funext u; simp
  rw [h0, act_copyPrefixCircuit_ket]
  congr 1; funext u
  have hu := u.isLt
  by_cases hw : w ≤ u.1
  · simp [copyRegFn, hw, show u.1 < w + w by omega]
  · simp [copyRegFn, hw]

private def swapPrefixCircuit (w : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit (w + w)
  | 0, _ => LayeredCircuit.id (w + w)
  | k + 1, hk =>
    let prev := swapPrefixCircuit w k (by omega)
    let a : Fin (w + w) := ⟨k, by omega⟩
    let b : Fin (w + w) := ⟨w + k, by omega⟩
    have hab : a ≠ b := Fin.ne_of_val_ne (by dsimp [a, b]; omega)
    prev.seq (swapWiresGate a b hab)

private lemma swapPrefixCircuit_size (w k : ℕ) (hk : k ≤ w) :
    (swapPrefixCircuit w k hk).size = 3 * k := by
  induction k with
  | zero => simp [swapPrefixCircuit]
  | succ k ih => simp [swapPrefixCircuit, ih (by omega)]; omega

private lemma act_swapPrefixCircuit_ket (w k : ℕ) (hk : k ≤ w) (z : Qubits (w + w)) :
    act (swapPrefixCircuit w k hk).unitary (ket z) =
      ket (fun u =>
        if h1 : u.1 < k then z ⟨w + u.1, by omega⟩
        else if h2 : w ≤ u.1 ∧ u.1 < w + k then z ⟨u.1 - w, by omega⟩
        else z u) := by
  induction k with
  | zero =>
    simp only [swapPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    rw [dif_neg (by omega), dif_neg (by omega)]
  | succ k ih =>
    dsimp only [swapPrefixCircuit]
    rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega), act_swapWiresGate_ket]
    congr 1; funext u
    let a : Fin (w + w) := ⟨k, by omega⟩
    let b : Fin (w + w) := ⟨w + k, by omega⟩
    have ha1 : ¬ a.1 < k := by dsimp [a]; omega
    have ha2 : ¬ (w ≤ a.1 ∧ a.1 < w + k) := by dsimp [a]; omega
    have hb1 : ¬ b.1 < k := by dsimp [b]; omega
    have hb2 : ¬ (w ≤ b.1 ∧ b.1 < w + k) := by dsimp [b]; omega
    by_cases hua : u = a
    · subst hua
      have ha_new : a.1 < k + 1 := by dsimp [a]; omega
      rw [if_pos rfl, dif_neg hb1, dif_neg hb2, dif_pos ha_new]
    · rw [if_neg hua]
      by_cases hub : u = b
      · subst hub
        have hb_n1 : ¬ b.1 < k + 1 := by dsimp [b]; omega
        have hb_n2 : w ≤ b.1 ∧ b.1 < w + (k + 1) := by dsimp [b]; omega
        rw [if_pos rfl, dif_neg ha1, dif_neg ha2, dif_neg hb_n1, dif_pos hb_n2]
        exact congrArg z (Fin.ext (by simp [b]))
      · rw [if_neg hub]
        by_cases h1 : u.1 < k
        · have h1' : u.1 < k + 1 := by omega
          rw [dif_pos h1, dif_pos h1']
        · have h1' : ¬ u.1 < k + 1 := by
            intro h; apply hua; apply Fin.ext; dsimp [a]; omega
          rw [dif_neg h1, dif_neg h1']
          by_cases h2 : w ≤ u.1 ∧ u.1 < w + k
          · have h2' : w ≤ u.1 ∧ u.1 < w + (k + 1) := by omega
            rw [dif_pos h2, dif_pos h2']
          · have h2' : ¬ (w ≤ u.1 ∧ u.1 < w + (k + 1)) := by
              intro h; apply hub; apply Fin.ext; dsimp [b]; omega
            rw [dif_neg h2, dif_neg h2']

/-- Swaps two `w`-bit registers `(a, b) ↦ (b, a)` using `3 * w` CNOTs (`0` ancillas). -/
def swapRegCircuit (w : ℕ) : LayeredCircuit ((w + w) + 0) :=
  swapPrefixCircuit w w le_rfl

@[simp] lemma swapRegCircuit_size (w : ℕ) : (swapRegCircuit w).size = 3 * w :=
  swapPrefixCircuit_size w w le_rfl


lemma swapRegCircuit_implements (w : ℕ) :
    (swapRegCircuit w).ImplementsOnClean (permMat (swapRegFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [swapRegCircuit]
  have h0 : padZero (w + w) 0 x = x := by
    funext u; simp
  rw [h0, act_swapPrefixCircuit_ket]
  congr 1; funext u
  have hu := u.isLt
  by_cases h1 : u.1 < w
  · simp [swapRegFn, h1]
  · simp [swapRegFn, h1, show w ≤ u.1 ∧ u.1 < w + w by omega]

private noncomputable def cswapPrefixCircuit (w : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit (1 + w + w)
  | 0, _ => LayeredCircuit.id (1 + w + w)
  | k + 1, hk =>
    let prev := cswapPrefixCircuit w k (by omega)
    let c : Fin (1 + w + w) := ⟨0, by omega⟩
    let a : Fin (1 + w + w) := ⟨1 + k, by omega⟩
    let b : Fin (1 + w + w) := ⟨1 + w + k, by omega⟩
    have hca : c ≠ a := Fin.ne_of_val_ne (by dsimp [c, a]; omega)
    have hcb : c ≠ b := Fin.ne_of_val_ne (by dsimp [c, b]; omega)
    have hab : a ≠ b := Fin.ne_of_val_ne (by dsimp [a, b]; omega)
    prev.seq (cswapOn c a b hca hcb hab)

private lemma cswapPrefixCircuit_size (w k : ℕ) (hk : k ≤ w) :
    (cswapPrefixCircuit w k hk).size = 7 * k := by
  induction k with
  | zero => simp [cswapPrefixCircuit]
  | succ k ih => simp [cswapPrefixCircuit, ih (by omega)]; omega

private lemma act_cswapPrefixCircuit_ket (w k : ℕ) (hk : k ≤ w) (z : Qubits (1 + w + w)) :
    act (cswapPrefixCircuit w k hk).unitary (ket z) =
      ket (fun u =>
        if z ⟨0, by omega⟩ then
          if h1 : 1 ≤ u.1 ∧ u.1 < 1 + k then z ⟨u.1 + w, by omega⟩
          else if h2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k then z ⟨u.1 - w, by omega⟩
          else z u
        else z u) := by
  induction k with
  | zero =>
    simp only [cswapPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    cases hz : z ⟨0, by omega⟩
    · rfl
    · simp only [↓reduceIte]; rw [dif_neg (by omega), dif_neg (by omega)]
  | succ k ih =>
    dsimp only [cswapPrefixCircuit]
    rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega), act_cswapOn_ket]
    congr 1; funext u
    let c : Fin (1 + w + w) := ⟨0, by omega⟩
    let a : Fin (1 + w + w) := ⟨1 + k, by omega⟩
    let b : Fin (1 + w + w) := ⟨1 + w + k, by omega⟩
    have hzc : z c = z ⟨0, by omega⟩ := rfl
    by_cases hz0 : z ⟨0, by omega⟩ = true
    · have hca_n : ¬ (1 ≤ c.1 ∧ c.1 < 1 + k) := by dsimp [c]; omega
      have hcb_n : ¬ (1 + w ≤ c.1 ∧ c.1 < 1 + w + k) := by dsimp [c]; omega
      have ha1_n : ¬ (1 ≤ a.1 ∧ a.1 < 1 + k) := by dsimp [a]; omega
      have ha2_n : ¬ (1 + w ≤ a.1 ∧ a.1 < 1 + w + k) := by dsimp [a]; omega
      have hb1_n : ¬ (1 ≤ b.1 ∧ b.1 < 1 + k) := by dsimp [b]; omega
      have hb2_n : ¬ (1 + w ≤ b.1 ∧ b.1 < 1 + w + k) := by dsimp [b]; omega
      have hzc_out : (if z ⟨0, by omega⟩ = true then
          if h1 : 1 ≤ c.1 ∧ c.1 < 1 + k then z ⟨c.1 + w, by omega⟩
          else if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then z ⟨c.1 - w, by omega⟩
          else z c else z c) = true := by
        rw [if_pos hz0, dif_neg hca_n, dif_neg hcb_n, hzc, hz0]
      rw [if_pos hzc_out]; simp only [hz0, ↓reduceIte]
      by_cases hua : u = a
      · subst hua
        have ha_new : 1 ≤ a.1 ∧ a.1 < 1 + (k + 1) := by dsimp [a]; omega
        rw [if_pos rfl, dif_neg hb1_n, dif_neg hb2_n, dif_pos ha_new]
        exact congrArg z (Fin.ext (by dsimp [a]; omega))
      · rw [if_neg hua]
        by_cases hub : u = b
        · subst hub
          have hb_n1 : ¬ (1 ≤ b.1 ∧ b.1 < 1 + (k + 1)) := by dsimp [b]; omega
          have hb_n2 : 1 + w ≤ b.1 ∧ b.1 < 1 + w + (k + 1) := by dsimp [b]; omega
          rw [if_pos rfl, dif_neg ha1_n, dif_neg ha2_n, dif_neg hb_n1, dif_pos hb_n2]
          exact congrArg z (Fin.ext (by dsimp [a, b]; omega))
        · rw [if_neg hub]
          by_cases h1 : 1 ≤ u.1 ∧ u.1 < 1 + k
          · have h1' : 1 ≤ u.1 ∧ u.1 < 1 + (k + 1) := by omega
            rw [dif_pos h1, dif_pos h1']
          · have h1' : ¬ (1 ≤ u.1 ∧ u.1 < 1 + (k + 1)) := by
              intro h; apply hua; apply Fin.ext; dsimp [a]; omega
            rw [dif_neg h1, dif_neg h1']
            by_cases h2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k
            · have h2' : 1 + w ≤ u.1 ∧ u.1 < 1 + w + (k + 1) := by omega
              rw [dif_pos h2, dif_pos h2']
            · have h2' : ¬ (1 + w ≤ u.1 ∧ u.1 < 1 + w + (k + 1)) := by
                intro h; apply hub; apply Fin.ext; dsimp [b]; omega
              rw [dif_neg h2, dif_neg h2']
    · have hzc_out : (if z ⟨0, by omega⟩ = true then
          if h1 : 1 ≤ c.1 ∧ c.1 < 1 + k then z ⟨c.1 + w, by omega⟩
          else if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then z ⟨c.1 - w, by omega⟩
          else z c else z c) = false := by
        rw [if_neg hz0, hzc]
        cases hz_c : z ⟨0, by omega⟩
        · rfl
        · exact absurd hz_c hz0
      have hzc_out_ne : ¬ ((if z ⟨0, by omega⟩ = true then
          if h1 : 1 ≤ c.1 ∧ c.1 < 1 + k then z ⟨c.1 + w, by omega⟩
          else if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then z ⟨c.1 - w, by omega⟩
          else z c else z c) = true) := by rw [hzc_out]; decide
      rw [if_neg hzc_out_ne, if_neg hz0, if_neg hz0]

/-- Controlled swap of two `w`-bit registers using `7 * w` gates (`0` ancillas). -/
noncomputable def cswapRegCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + 0) :=
  cswapPrefixCircuit w w le_rfl

@[simp] lemma cswapRegCircuit_size (w : ℕ) : (cswapRegCircuit w).size = 7 * w :=
  cswapPrefixCircuit_size w w le_rfl


lemma cswapRegCircuit_implements (w : ℕ) :
    (cswapRegCircuit w).ImplementsOnClean (permMat (cswapRegFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [cswapRegCircuit]
  have h0 : padZero (1 + w + w) 0 x = x := by
    funext u; simp
  have h0' : padZero (1 + w + w) 0 (cswapRegFn w x) = cswapRegFn w x := by
    funext u; simp
  rw [h0, h0', act_cswapPrefixCircuit_ket]
  congr 1; funext u
  have hu := u.isLt
  by_cases hx : x ⟨0, by omega⟩ = true
  · dsimp only [cswapRegFn]
    rw [if_pos hx, if_pos hx]
    by_cases h1 : 1 ≤ u.1 ∧ u.1 < 1 + w
    · rw [dif_pos h1, dif_pos h1]
    · rw [dif_neg h1, dif_neg h1]
      by_cases h2 : 1 + w ≤ u.1
      · rw [dif_pos h2, dif_pos ⟨h2, hu⟩]
      · rw [dif_neg h2, dif_neg (by omega)]
  · dsimp only [cswapRegFn]; rw [if_neg hx, if_neg hx]

private def setConstPrefixCircuit (w c : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit w
  | 0, _ => LayeredCircuit.id w
  | k + 1, hk =>
    let prev := setConstPrefixCircuit w c k (by omega)
    if c.testBit k then prev.seq (pauliXGate ⟨k, by omega⟩) else prev

private lemma setConstPrefixCircuit_size (w c k : ℕ) (hk : k ≤ w) :
    (setConstPrefixCircuit w c k hk).size ≤ k := by
  induction k with
  | zero => simp [setConstPrefixCircuit]
  | succ k ih =>
    dsimp only [setConstPrefixCircuit]
    split_ifs <;> have h := ih (by omega) <;> simp <;> omega

private lemma act_setConstPrefixCircuit_ket (w c k : ℕ) (hk : k ≤ w) (z : Qubits w) :
    act (setConstPrefixCircuit w c k hk).unitary (ket z) =
      ket (fun i => if i.1 < k then xor (z i) (c.testBit i.1) else z i) := by
  induction k with
  | zero =>
    simp only [setConstPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    exact congrArg ket (funext fun i => (if_neg (Nat.not_lt_zero i.1)).symm)
  | succ k ih =>
    dsimp only [setConstPrefixCircuit]
    cases hc : c.testBit k
    · rw [if_neg (by simp), ih (by omega)]
      congr 1; funext i
      by_cases hi : i.1 < k
      · rw [if_pos hi, if_pos (by omega)]
      · rw [if_neg hi]
        by_cases hk_eq : i.1 = k
        · rw [if_pos (by omega), hk_eq, hc, Bool.xor_false]
        · rw [if_neg (by omega)]
    · rw [if_pos (by simp), LayeredCircuit.seq_unitary, act_mul, ih (by omega),
        act_pauliXGate_ket]
      congr 1; funext i
      by_cases hik : i = ⟨k, by omega⟩
      · subst hik
        simp [Function.update_self, hc]
      · rw [Function.update_of_ne hik]
        have hne_v : i.1 ≠ k := fun h => hik (Fin.ext h)
        by_cases hi : i.1 < k
        · rw [if_pos hi, if_pos (by omega)]
        · rw [if_neg hi, if_neg (by omega)]

/-- XORs classical `natToBitsLSB w c` onto a `w`-qubit register (`≤ w` gates, `0` ancillas). -/
def setConstCircuit (w c : ℕ) : LayeredCircuit (w + 0) :=
  setConstPrefixCircuit w c w le_rfl

lemma setConstCircuit_size (w c : ℕ) : (setConstCircuit w c).size ≤ w :=
  setConstPrefixCircuit_size w c w le_rfl

lemma setConstCircuit_implements (w c : ℕ) :
    (setConstCircuit w c).ImplementsOnClean
      (permMat fun x : Qubits w => fun i => xor (x i) (natToBitsLSB w c i)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [setConstCircuit]
  have h0 : padZero w 0 x = x := by
    funext u; simp
  rw [h0]
  have hact := act_setConstPrefixCircuit_ket w c w le_rfl x
  change act (setConstPrefixCircuit w c w le_rfl).unitary (ket x) = _
  rw [hact]
  congr 1; funext i
  simp [natToBitsLSB, i.isLt]

private def ctrlConstPrefixCircuit (w c : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit (1 + w)
  | 0, _ => LayeredCircuit.id (1 + w)
  | k + 1, hk =>
    let prev := ctrlConstPrefixCircuit w c k (by omega)
    let c0 : Fin (1 + w) := ⟨0, by omega⟩
    let tgt : Fin (1 + w) := ⟨1 + k, by omega⟩
    have hne : c0 ≠ tgt := Fin.ne_of_val_ne (by dsimp [c0, tgt]; omega)
    if c.testBit k then prev.seq (cnotGate c0 tgt hne) else prev

private lemma ctrlConstPrefixCircuit_size (w c k : ℕ) (hk : k ≤ w) :
    (ctrlConstPrefixCircuit w c k hk).size ≤ k := by
  induction k with
  | zero => simp [ctrlConstPrefixCircuit]
  | succ k ih =>
    dsimp only [ctrlConstPrefixCircuit]
    split_ifs <;> have h := ih (by omega) <;> simp <;> omega

private lemma act_ctrlConstPrefixCircuit_ket (w c k : ℕ) (hk : k ≤ w) (z : Qubits (1 + w)) :
    act (ctrlConstPrefixCircuit w c k hk).unitary (ket z) =
      ket (fun u =>
        if z ⟨0, by omega⟩ then if h : 1 ≤ u.1 ∧ u.1 < 1 + k then xor (z u) (c.testBit (u.1 - 1)) else z u
        else z u) := by
  induction k with
  | zero =>
    simp only [ctrlConstPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    cases z ⟨0, by omega⟩
    · rfl
    · simp only [↓reduceIte]; rw [dif_neg (by omega)]
  | succ k ih =>
    dsimp only [ctrlConstPrefixCircuit]
    cases hc : c.testBit k
    · rw [if_neg (by simp), ih (by omega)]
      congr 1; funext u
      cases hz0 : z ⟨0, by omega⟩
      · rfl
      · simp only [↓reduceIte]
        by_cases hu : 1 ≤ u.1 ∧ u.1 < 1 + k
        · rw [dif_pos hu, dif_pos (by omega)]
        · rw [dif_neg hu]
          by_cases heq : u.1 = 1 + k
          · rw [dif_pos (by omega), show u.1 - 1 = k by omega, hc, Bool.xor_false]
          · rw [dif_neg (by omega)]
    · rw [if_pos (by simp), LayeredCircuit.seq_unitary, act_mul, ih (by omega),
        act_cnotGate_ket]
      congr 1; funext u
      let c0 : Fin (1 + w) := ⟨0, by omega⟩
      let tgt : Fin (1 + w) := ⟨1 + k, by omega⟩
      have hc0_v : c0.1 = 0 := rfl
      have htgt_v : tgt.1 = 1 + k := rfl
      have hzc : z c0 = z ⟨0, by omega⟩ := rfl
      by_cases hz0 : z ⟨0, by omega⟩ = true
      · have h0_lt : ¬ (1 ≤ c0.1 ∧ c0.1 < 1 + k) := by omega
        have hzc_out : (if z ⟨0, by omega⟩ = true then
            if h : 1 ≤ c0.1 ∧ c0.1 < 1 + k then xor (z c0) (c.testBit (c0.1 - 1)) else z c0
          else z c0) = true := by
          rw [if_pos hz0, dif_neg h0_lt, hzc, hz0]
        rw [hzc_out]
        by_cases hut : u = tgt
        · subst hut
          have hnt : ¬ (1 ≤ tgt.1 ∧ tgt.1 < 1 + k) := by omega
          have hnew : 1 ≤ tgt.1 ∧ tgt.1 < 1 + (k + 1) := by omega
          rw [Function.update_self, if_pos hz0, if_pos hz0, dif_neg hnt, dif_pos hnew,
            show tgt.1 - 1 = k by omega, hc]
        · rw [Function.update_of_ne hut, if_pos hz0, if_pos hz0]
          by_cases hu : 1 ≤ u.1 ∧ u.1 < 1 + k
          · rw [dif_pos hu, dif_pos (by omega)]
          · rw [dif_neg hu, dif_neg (by intro h; apply hut; apply Fin.ext; omega)]
      · have hzc_out : (if z ⟨0, by omega⟩ = true then
            if h : 1 ≤ c0.1 ∧ c0.1 < 1 + k then xor (z c0) (c.testBit (c0.1 - 1)) else z c0
          else z c0) = false := by
          rw [if_neg hz0, hzc]
          cases hz_c : z ⟨0, by omega⟩
          · rfl
          · exact absurd hz_c hz0
        rw [hzc_out, Bool.xor_false, Function.update_eq_self, if_neg hz0, if_neg hz0]

/-- Controlled on wire `0`, XORs `natToBitsLSB w c` onto wires `1..w` (`≤ w` gates, `0` ancillas). -/
def ctrlConstXorCircuit (w c : ℕ) : LayeredCircuit ((1 + w) + 0) :=
  ctrlConstPrefixCircuit w c w le_rfl

lemma ctrlConstXorCircuit_size (w c : ℕ) : (ctrlConstXorCircuit w c).size ≤ w :=
  ctrlConstPrefixCircuit_size w c w le_rfl

def ctrlConstXorFn (w c : ℕ) (x : Qubits (1 + w)) : Qubits (1 + w) :=
  fun u => if x ⟨0, by omega⟩ then
    if h : 1 ≤ u.1 then xor (x u) (natToBitsLSB w c ⟨u.1 - 1, by have := u.isLt; omega⟩) else x u
  else x u

lemma ctrlConstXorCircuit_implements (w c : ℕ) :
    (ctrlConstXorCircuit w c).ImplementsOnClean (permMat (ctrlConstXorFn w c)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [ctrlConstXorCircuit]
  have h0 : padZero (1 + w) 0 x = x := by
    funext u; simp
  have h0' : padZero (1 + w) 0 (ctrlConstXorFn w c x) = ctrlConstXorFn w c x := by
    funext u; simp
  rw [h0, h0']
  have hact := act_ctrlConstPrefixCircuit_ket w c w le_rfl x
  change act (ctrlConstPrefixCircuit w c w le_rfl).unitary (ket x) = ket (ctrlConstXorFn w c x)
  rw [hact]
  congr 1; funext u
  have hu := u.isLt
  by_cases hx : x ⟨0, by omega⟩ = true
  · dsimp only [ctrlConstXorFn]; rw [if_pos hx, if_pos hx]
    by_cases h1 : 1 ≤ u.1
    · rw [dif_pos ⟨h1, hu⟩, dif_pos h1]
      simp [natToBitsLSB]
    · rw [dif_neg (by omega), dif_neg h1]
  · dsimp only [ctrlConstXorFn]; rw [if_neg hx, if_neg hx]

/-! ### Part 3: Equality, Constant Comparison & Particle Encoding -/

private lemma multiEqCtrl1_implements_perm (L : ℕ) (pat : Qubits L) :
    (multiEqCtrl1 L pat pauliX pauliX_mem_unitaryGroup).ImplementsOnClean
      (permMat fun v : Qubits (L + 1) =>
        Function.update v ⟨L, Nat.lt_succ_self L⟩
          (xor (v ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, v ⟨i.1, by omega⟩ = pat i)))) := by
  have h := multiEqCtrl1_implements L pat pauliX pauliX_mem_unitaryGroup
  have heq : eqCtrlMat L pat pauliX =
      permMat (fun v : Qubits (L + 1) =>
        Function.update v ⟨L, Nat.lt_succ_self L⟩
          (xor (v ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, v ⟨i.1, by omega⟩ = pat i)))) := by
    ext y z
    simp only [eqCtrlMat, permMat, Matrix.of_apply]
    by_cases hyz : ∀ i : Fin L, y ⟨i.1, by omega⟩ = z ⟨i.1, by omega⟩
    · rw [if_pos hyz]
      by_cases hall : ∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i
      · rw [if_pos hall]
        have hy_eq : (y = Function.update z ⟨L, Nat.lt_succ_self L⟩
            (xor (z ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i)))) ↔
            y ⟨L, Nat.lt_succ_self L⟩ = !z ⟨L, Nat.lt_succ_self L⟩ := by
          simp only [decide_eq_true hall, Bool.xor_true]
          constructor
          · intro h; rw [h, Function.update_self]
          · intro h; funext k
            rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
            · have hne : k'.castSucc ≠ ⟨L, Nat.lt_succ_self L⟩ := Fin.ne_of_val_ne (by simp; omega)
              rw [Function.update_of_ne hne]; exact hyz k'
            · have hlast : Fin.last L = ⟨L, Nat.lt_succ_self L⟩ := rfl
              rw [hlast, Function.update_self]; exact h
        by_cases hym : y ⟨L, Nat.lt_succ_self L⟩ = !z ⟨L, Nat.lt_succ_self L⟩
        · rw [if_pos (hy_eq.mpr hym), hym]
          cases z ⟨L, Nat.lt_succ_self L⟩ <;> simp [pauliX]
        · rw [if_neg (mt hy_eq.mp hym)]
          cases hzm : z ⟨L, Nat.lt_succ_self L⟩ <;> cases hym' : y ⟨L, Nat.lt_succ_self L⟩ <;>
            simp [pauliX, hzm, hym'] at hym ⊢
      · rw [if_neg hall]
        have hy_eq : (y = Function.update z ⟨L, Nat.lt_succ_self L⟩
            (xor (z ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i)))) ↔
            y ⟨L, Nat.lt_succ_self L⟩ = z ⟨L, Nat.lt_succ_self L⟩ := by
          simp only [decide_eq_false hall, Bool.xor_false, Function.update_eq_self]
          constructor
          · intro h; rw [h]
          · intro h; funext k
            rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
            · exact hyz k'
            · exact h
        by_cases hym : y ⟨L, Nat.lt_succ_self L⟩ = z ⟨L, Nat.lt_succ_self L⟩
        · rw [if_pos hym, if_pos (hy_eq.mpr hym)]
        · rw [if_neg hym, if_neg (mt hy_eq.mp hym)]
    · rw [if_neg hyz]
      symm; rw [if_neg]
      intro h; apply hyz; intro i
      have h1 := congrFun h ⟨i.1, by omega⟩
      have hne : (⟨i.1, by omega⟩ : Fin (L + 1)) ≠ ⟨L, Nat.lt_succ_self L⟩ :=
        Fin.ne_of_val_ne (by simp; omega)
      rwa [Function.update_of_ne hne] at h1
  rwa [← heq]

/-- Embedding `(w + w)` inside `((w + w + 1) + w)` at prefix `0 .. 2w-1`. -/
private def eqCopyEmb (w : ℕ) : Fin ((w + w) + 0) ↪ Fin ((w + w + 1) + w) where
  toFun i := ⟨i.1, by omega⟩
  inj' a b h := Fin.ext (by have := congrArg Fin.val h; exact this)

@[simp] private lemma eqCopyEmb_val (w : ℕ) (i : Fin ((w + w) + 0)) :
    (eqCopyEmb w i).1 = i.1 := rfl

/-- Embedding `(w + 1 + w)` inside `((w + w + 1) + w)` mapping `B, t, anc` cleanly. -/
private def eqZeroEmb (w : ℕ) : Fin (w + 1 + w) ↪ Fin ((w + w + 1) + w) where
  toFun i := ⟨w + i.1, by omega⟩
  inj' a b h := Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)

@[simp] private lemma eqZeroEmb_val (w : ℕ) (i : Fin (w + 1 + w)) :
    (eqZeroEmb w i).1 = w + i.1 := rfl

/-- Equality comparator `(a, b, t) ↦ (a, b, t ^^^ decide (a = b))` in `≤ 14 * w + 12` gates. -/
noncomputable def eqRegCircuit (w : ℕ) : LayeredCircuit ((w + w + 1) + w) :=
  let cpy := (copyRegCircuit w).mapWires (eqCopyEmb w)
  let eqZ := (multiEqCtrl1 w (fun _ => false) pauliX pauliX_mem_unitaryGroup).mapWires (eqZeroEmb w)
  cpy.seq (eqZ.seq cpy)

lemma eqRegCircuit_size (w : ℕ) : (eqRegCircuit w).size ≤ 14 * w + 12 := by
  dsimp only [eqRegCircuit]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size, copyRegCircuit_size]
  have h := multiEqCtrl1_size w (fun _ => false) pauliX pauliX_mem_unitaryGroup
  omega


lemma eqRegCircuit_implements (w : ℕ) :
    (eqRegCircuit w).ImplementsOnClean (permMat (eqRegFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (w + w + 1) w x
  let tgt : Fin ((w + w + 1) + w) := ⟨w + w, by omega⟩
  let cpy := (copyRegCircuit w).mapWires (eqCopyEmb w)
  let eqZ := (multiEqCtrl1 w (fun _ => false) pauliX pauliX_mem_unitaryGroup).mapWires (eqZeroEmb w)
  let z1 : Qubits ((w + w + 1) + w) := fun u =>
    if h : w ≤ u.1 ∧ u.1 < w + w then xor (z0 u) (z0 ⟨u.1 - w, by omega⟩) else z0 u
  have h1 : act cpy.unitary (ket z0) = ket z1 := by
    have hact := act_mapWires_perm (copyRegCircuit w) (copyRegFn w) (copyRegCircuit_implements w)
      (eqCopyEmb w) z0 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hu : u.1 < w + w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (eqCopyEmb w)) ⟨u.1, hu⟩ := Fin.ext rfl
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [copyRegFn, Function.comp_apply, z1]
      by_cases hw : w ≤ u.1
      · simp [hw, hu, show ((Fin.castAddEmb 0).trans (eqCopyEmb w)) ⟨u.1 - w, by omega⟩ = ⟨u.1 - w, by omega⟩ from Fin.ext rfl]
      · simp [hw]
    · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (eqCopyEmb w)) := by
        rintro ⟨j, hj⟩; have := congrArg Fin.val hj; simp at this; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]
      simp [z1, show ¬ (w ≤ u.1 ∧ u.1 < w + w) by omega]
  have hclean_z1 : ∀ j : Fin w, z1 (eqZeroEmb w (Fin.natAdd (w + 1) j)) = false := fun j => by
    dsimp only [z1]
    rw [dif_neg (by simp; omega)]
    exact padZero_val_ge x _ (by simp; omega)
  let z2 := Function.update z1 tgt
    (xor (z1 tgt) (decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = x ⟨w + i.1, by omega⟩)))
  have h2 : act eqZ.unitary (ket z1) = ket z2 := by
    have hact := act_mapWires_perm (multiEqCtrl1 w (fun _ => false) pauliX pauliX_mem_unitaryGroup)
      _ (multiEqCtrl1_implements_perm w (fun _ => false)) (eqZeroEmb w) z1 hclean_z1
    rw [hact]; congr 1; funext u
    let embM := (Fin.castAddEmb w).trans (eqZeroEmb w)
    have htgt : tgt = embM ⟨w, Nat.lt_succ_self w⟩ := by
      apply Fin.ext; dsimp [tgt, embM]; simp
    have hall_iff : (∀ i : Fin w, z1 (embM ⟨i.1, by omega⟩) = false) ↔
        (∀ i : Fin w, x ⟨i.1, by omega⟩ = x ⟨w + i.1, by omega⟩) := by
      refine forall_congr' fun i => ?_
      have hev : (embM ⟨i.1, by omega⟩).1 = w + i.1 := by simp [embM]
      dsimp only [z1]
      have hpos : w ≤ (embM ⟨i.1, by omega⟩).1 ∧ (embM ⟨i.1, by omega⟩).1 < w + w := by
        have := i.isLt; omega
      rw [dif_pos hpos]
      have hw1 : z0 (embM ⟨i.1, by omega⟩) = x ⟨w + i.1, by omega⟩ := by
        dsimp only [z0]
        rw [padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext (by simp [hev]))
      have hw2 : z0 ⟨(embM ⟨i.1, by omega⟩).1 - w, by omega⟩ = x ⟨i.1, by omega⟩ := by
        dsimp only [z0]
        rw [padZero_val_lt x _ (by dsimp; omega)]
        exact congrArg x (Fin.ext (by simp [hev]))
      rw [hw1, hw2]
      cases x ⟨w + i.1, by omega⟩ <;> cases x ⟨i.1, by omega⟩ <;> simp
    have hdec : decide (∀ i : Fin w, (z1 ∘ embM) ⟨i.1, by omega⟩ = false) =
        decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = x ⟨w + i.1, by omega⟩) := by
      rw [Bool.eq_iff_iff]; simp only [Function.comp_apply, decide_eq_true_eq]; exact hall_iff
    dsimp only [z2]
    by_cases hu : u = tgt
    · subst hu
      dsimp only [embM] at htgt
      rw [Function.update_self, htgt, updateOn_apply_emb, Function.update_self, ← htgt]
      simp only [Function.comp_apply] at hdec ⊢
      rw [← htgt, hdec]
    · rw [Function.update_of_ne hu]
      by_cases hur : u ∈ Set.range embM
      · rcases hur with ⟨k, rfl⟩
        dsimp only [embM] at hu htgt ⊢
        rw [updateOn_apply_emb]
        rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
        · have hne : k'.castSucc ≠ ⟨w, Nat.lt_succ_self w⟩ := Fin.ne_of_val_ne (by simp; omega)
          rw [Function.update_of_ne hne]; rfl
        · exfalso; exact hu htgt.symm
      · dsimp only [embM] at hur
        rw [updateOn_apply_not_mem _ _ _ hur]
  have h3 : act cpy.unitary (ket z2) = ket (padZero (w + w + 1) w (eqRegFn w x)) := by
    have hact := act_mapWires_perm (copyRegCircuit w) (copyRegFn w) (copyRegCircuit_implements w)
      (eqCopyEmb w) z2 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hu : u.1 < w + w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (eqCopyEmb w)) ⟨u.1, hu⟩ := Fin.ext rfl
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [copyRegFn, Function.comp_apply]
      have hus : u ≠ tgt := Fin.ne_of_val_ne (by dsimp [tgt]; omega)
      have hne_x : (⟨u.1, by omega⟩ : Fin (w + w + 1)) ≠ ⟨w + w, by omega⟩ :=
        Fin.ne_of_val_ne (by simp; omega)
      by_cases hw : w ≤ u.1
      · rw [dif_pos hw]
        have hsub : ((Fin.castAddEmb 0).trans (eqCopyEmb w)) ⟨u.1 - w, by omega⟩ =
            ⟨u.1 - w, by omega⟩ := Fin.ext rfl
        rw [hsub]
        have hsub_ne : (⟨u.1 - w, by omega⟩ : Fin ((w + w + 1) + w)) ≠ tgt :=
          Fin.ne_of_val_ne (by dsimp [tgt]; omega)
        dsimp only [z2]
        rw [← hu_eq, Function.update_of_ne hus, Function.update_of_ne hsub_ne]
        dsimp only [z1, z0]
        rw [dif_pos (by omega), dif_neg (by omega)]
        rw [padZero_val_lt x _ (by omega), padZero_val_lt x _ (by dsimp; omega),
          padZero_val_lt _ _ (by simp; omega)]
        dsimp only [eqRegFn]
        rw [Function.update_of_ne hne_x]
        cases x ⟨u.1, by omega⟩ <;> cases x ⟨u.1 - w, by omega⟩ <;> simp
      · rw [dif_neg hw]
        dsimp only [z2]
        rw [← hu_eq, Function.update_of_ne hus]
        dsimp only [z1, z0]
        rw [dif_neg (by simp [hw]), padZero_val_lt x _ (by omega),
          padZero_val_lt _ _ (by simp; omega), eqRegFn, Function.update_of_ne hne_x]
    · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (eqCopyEmb w)) := by
        rintro ⟨j, hj⟩; have := congrArg Fin.val hj; simp at this; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]
      by_cases hus : u = tgt
      · subst hus
        dsimp only [z2]; rw [Function.update_self]
        dsimp only [z1, z0]; rw [dif_neg (by dsimp [tgt]; omega)]
        rw [padZero_val_lt x _ (by dsimp [tgt]; omega), padZero_val_lt _ _ (by dsimp [tgt]; omega),
          eqRegFn, Function.update_self]
      · have hgt : w + w + 1 ≤ u.1 := by
          have hne : u.1 ≠ w + w := fun h => hus (Fin.ext h)
          omega
        dsimp only [z2]; rw [Function.update_of_ne hus]
        dsimp only [z1, z0]; rw [dif_neg (by omega), padZero_val_ge x u hgt, padZero_val_ge _ u hgt]
  dsimp only [eqRegCircuit]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  change act cpy.unitary (act eqZ.unitary (act cpy.unitary (ket z0))) = _
  rw [h1, h2, h3]

/-- Embedding `(w + 0)` inside `((w + 1) + w)`. -/
private def eqConstSetEmb (w : ℕ) : Fin (w + 0) ↪ Fin ((w + 1) + w) where
  toFun i := ⟨i.1, by omega⟩
  inj' a b h := Fin.ext (by have := congrArg Fin.val h; exact this)

@[simp] private lemma eqConstSetEmb_val (w : ℕ) (i : Fin (w + 0)) :
    (eqConstSetEmb w i).1 = i.1 := rfl

/-- Constant equality `(x, t) ↦ (x, t ^^^ decide (x = natToBitsLSB w c))` in `≤ 14 * w + 12` gates. -/
noncomputable def eqConstCircuit (w c : ℕ) : LayeredCircuit ((w + 1) + w) :=
  let sc := (setConstCircuit w c).mapWires (eqConstSetEmb w)
  let eqZ := multiEqCtrl1 w (fun _ => false) pauliX pauliX_mem_unitaryGroup
  sc.seq (eqZ.seq sc)

lemma eqConstCircuit_size (w c : ℕ) : (eqConstCircuit w c).size ≤ 14 * w + 12 := by
  dsimp only [eqConstCircuit]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size]
  have h1 := setConstCircuit_size w c
  have h2 := multiEqCtrl1_size w (fun _ => false) pauliX pauliX_mem_unitaryGroup
  omega

def eqConstFn (w c : ℕ) (x : Qubits (w + 1)) : Qubits (w + 1) :=
  Function.update x ⟨w, by omega⟩
    (xor (x ⟨w, by omega⟩)
      (decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = natToBitsLSB w c i)))

lemma eqConstCircuit_implements (w c : ℕ) :
    (eqConstCircuit w c).ImplementsOnClean (permMat (eqConstFn w c)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (w + 1) w x
  let tgt : Fin ((w + 1) + w) := ⟨w, by omega⟩
  let sc := (setConstCircuit w c).mapWires (eqConstSetEmb w)
  let eqZ := multiEqCtrl1 w (fun _ => false) pauliX pauliX_mem_unitaryGroup
  let pat := natToBitsLSB w c
  let z1 : Qubits ((w + 1) + w) := fun u =>
    if h : u.1 < w then xor (z0 u) (pat ⟨u.1, h⟩) else z0 u
  have h1 : act sc.unitary (ket z0) = ket z1 := by
    have hact := act_mapWires_perm (setConstCircuit w c) _ (setConstCircuit_implements w c)
      (eqConstSetEmb w) z0 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hu : u.1 < w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (eqConstSetEmb w)) ⟨u.1, hu⟩ := Fin.ext rfl
      rw [hu_eq, updateOn_apply_emb]
      simp [Function.comp_apply, z1, pat, hu, Fin.castAddEmb]
    · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (eqConstSetEmb w)) := by
        rintro ⟨j, hj⟩; have := congrArg Fin.val hj; simp at this; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]
      simp [z1, hu]
  have hclean_z1 : ∀ j : Fin w, z1 (Fin.natAdd (w + 1) j) = false := fun j => by
    dsimp only [z1]; rw [dif_neg (by simp; omega)]; exact padZero_natAdd (w + 1) w x j
  have hz1_w : z1 tgt = x ⟨w, by omega⟩ := by
    dsimp only [z1]; rw [dif_neg (by dsimp [tgt]; omega)]
    exact padZero_val_lt x tgt (by dsimp [tgt]; omega)
  let z2 := Function.update z1 tgt (xor (z1 tgt) (decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = pat i)))
  have h2 : act eqZ.unitary (ket z1) = ket z2 := by
    have hact := act_ket_of_implementsOnClean_perm (multiEqCtrl1_implements_perm w (fun _ => false))
      (fun i : Fin (w + 1) => z1 (Fin.castAdd w i))
    have hz1_eq : z1 = padZero (w + 1) w (fun i : Fin (w + 1) => z1 (Fin.castAdd w i)) := by
      funext u; refine Fin.addCases (fun i => ?_) (fun j => ?_) u
      · simp
      · simp [hclean_z1 j]
    rw [← hz1_eq] at hact
    rw [hact]; congr 1; funext u
    have hall_iff : (∀ i : Fin w, z1 (Fin.castAdd w ⟨i.1, by omega⟩) = false) ↔
        (∀ i : Fin w, x ⟨i.1, by omega⟩ = pat i) := by
      refine forall_congr' fun i => ?_
      dsimp only [z1, z0]
      have hflt : (Fin.castAdd w (⟨i.1, by omega⟩ : Fin (w + 1))).1 < w := by simp
      rw [dif_pos hflt, padZero_val_lt x _ (by omega)]
      have hsub : (⟨(Fin.castAdd w (⟨i.1, by omega⟩ : Fin (w + 1))).1, hflt⟩ : Fin w) = i := rfl
      have hsub2 : (⟨(Fin.castAdd w (⟨i.1, by omega⟩ : Fin (w + 1))).1, by omega⟩ : Fin (w + 1)) =
          ⟨i.1, by omega⟩ := rfl
      rw [hsub, hsub2]
      cases x ⟨i.1, by omega⟩ <;> cases pat i <;> simp
    have hdec : decide (∀ i : Fin w, z1 (Fin.castAdd w ⟨i.1, by omega⟩) = false) =
        decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = pat i) := by
      rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; exact hall_iff
    by_cases hu_lt : u.1 < w + 1
    · rw [padZero_val_lt _ u hu_lt]
      by_cases huw : u.1 = w
      · have hut : u = tgt := Fin.ext huw
        subst hut
        have hi_eq : (⟨tgt.1, hu_lt⟩ : Fin (w + 1)) = ⟨w, Nat.lt_succ_self w⟩ := Fin.ext rfl
        rw [hi_eq, Function.update_self]
        dsimp only [z2]; rw [Function.update_self, hdec]
        rfl
      · have hut : u ≠ tgt := Fin.ne_of_val_ne huw
        have hne_x : (⟨u.1, hu_lt⟩ : Fin (w + 1)) ≠ ⟨w, Nat.lt_succ_self w⟩ :=
          Fin.ne_of_val_ne huw
        rw [Function.update_of_ne hne_x]
        dsimp only [z2]; rw [Function.update_of_ne hut]
        congr 1
    · have hge : w + 1 ≤ u.1 := by omega
      have hut : u ≠ tgt := Fin.ne_of_val_ne (by dsimp [tgt]; omega)
      rw [padZero_val_ge _ u hge]
      have hu_eq : u = Fin.natAdd (w + 1) ⟨u.1 - (w + 1), by have := u.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      dsimp only [z2]; rw [Function.update_of_ne hut, hu_eq, hclean_z1]
  have h3 : act sc.unitary (ket z2) = ket (padZero (w + 1) w (eqConstFn w c x)) := by
    have hact := act_mapWires_perm (setConstCircuit w c) _ (setConstCircuit_implements w c)
      (eqConstSetEmb w) z2 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hu : u.1 < w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (eqConstSetEmb w)) ⟨u.1, hu⟩ := Fin.ext rfl
      rw [hu_eq, updateOn_apply_emb]
      have hne_t : u ≠ tgt := Fin.ne_of_val_ne (by dsimp [tgt]; omega)
      have hne_x : (⟨u.1, by omega⟩ : Fin (w + 1)) ≠ ⟨w, by omega⟩ := Fin.ne_of_val_ne (by simp; omega)
      dsimp only [Function.comp_apply]
      change xor (z2 u) (natToBitsLSB w c ⟨u.1, hu⟩) = _
      dsimp only [z2]; rw [← hu_eq, Function.update_of_ne hne_t]
      dsimp only [z1, z0]; rw [dif_pos hu, padZero_val_lt x u (by omega),
        padZero_val_lt _ u (by omega), eqConstFn, Function.update_of_ne hne_x]
      dsimp only [pat]
      cases x ⟨u.1, by omega⟩ <;> cases natToBitsLSB w c ⟨u.1, hu⟩ <;> simp
    · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (eqConstSetEmb w)) := by
        rintro ⟨j, hj⟩; have := congrArg Fin.val hj; simp at this; omega
      rw [updateOn_apply_not_mem _ _ _ hnot]
      by_cases huw : u = tgt
      · subst huw
        dsimp only [z2]; rw [Function.update_self, hz1_w]
        rw [padZero_val_lt _ tgt (by dsimp [tgt]; omega), eqConstFn, Function.update_self]
      · have hge : w + 1 ≤ u.1 := by
          have hne : u.1 ≠ w := fun h => huw (Fin.ext h)
          omega
        dsimp only [z2]; rw [Function.update_of_ne huw]
        dsimp only [z1, z0]; rw [dif_neg hu, padZero_val_ge x u hge, padZero_val_ge _ u hge]
  dsimp only [eqConstCircuit]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  change act sc.unitary (act eqZ.unitary (act sc.unitary (ket z0))) = _
  rw [h1, h2, h3]

lemma ltConstCircuit_implements_perm (q_w H : ℕ) :
    (ltConstCircuit q_w H).ImplementsOnClean
      (permMat fun x : Qubits (q_w + 1) =>
        Function.update x ⟨q_w, Nat.lt_succ_self q_w⟩
          (xor (x ⟨q_w, Nat.lt_succ_self q_w⟩)
            (decide (bitsToNatLSB (fun i : Fin q_w => x ⟨i.1, by omega⟩) < H)))) :=
  ltConstCircuit_implements q_w H

/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/

private noncomputable def cuccaroMAJ {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : LayeredCircuit m :=
  (cnotGate a b hba.symm).seq ((cnotGate a c hca.symm).seq (toffoliOn c b a hcb hca hba))

private noncomputable def cuccaroUMA {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : LayeredCircuit m :=
  (toffoliOn c b a hcb hca hba).seq ((cnotGate a c hca.symm).seq (cnotGate c b hcb))

@[simp] private lemma cuccaroMAJ_size {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : (cuccaroMAJ c b a hcb hca hba).size = 7 := by
  simp [cuccaroMAJ]

@[simp] private lemma cuccaroUMA_size {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) : (cuccaroUMA c b a hcb hca hba).size = 7 := by
  simp [cuccaroUMA]

private lemma act_cuccaroMAJ_ket {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) (z : Qubits m) :
    act (cuccaroMAJ c b a hcb hca hba).unitary (ket z) =
      ket (fun w =>
        if w = c then xor (z c) (z a)
        else if w = b then xor (z b) (z a)
        else if w = a then xor (z a) ((xor (z c) (z a)) && (xor (z b) (z a)))
        else z w) := by
  simp only [cuccaroMAJ, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  congr 1; funext w
  by_cases hwc : w = c
  · subst hwc
    simp only [Function.update_self, Function.update_of_ne hca, Function.update_of_ne hcb,
      Function.update_of_ne hca.symm, Function.update_of_ne hcb.symm,
      Function.update_of_ne hba.symm, ↓reduceIte]
  · by_cases hwb : w = b
    · subst hwb
      simp only [Function.update_self, Function.update_of_ne hba, Function.update_of_ne hba.symm,
        Function.update_of_ne hcb, Function.update_of_ne hcb.symm,
        Function.update_of_ne hca.symm, if_neg hwc, ↓reduceIte]
    · by_cases hwa : w = a
      · subst hwa
        simp only [Function.update_self, Function.update_of_ne hca.symm,
          Function.update_of_ne hba.symm,
          Function.update_of_ne hcb, Function.update_of_ne hcb.symm,
          if_neg hwc, if_neg hwb, ↓reduceIte]
      · rw [Function.update_of_ne hwa, Function.update_of_ne hwc, Function.update_of_ne hwb,
          if_neg hwc, if_neg hwb, if_neg hwa]

private lemma act_cuccaroUMA_ket {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) (z : Qubits m) :
    act (cuccaroUMA c b a hcb hca hba).unitary (ket z) =
      ket (fun w =>
        let a1 := xor (z a) (z c && z b)
        let c1 := xor (z c) a1
        if w = c then c1
        else if w = b then xor (z b) c1
        else if w = a then a1
        else z w) := by
  simp only [cuccaroUMA, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  congr 1; funext w
  by_cases hwc : w = c
  · subst hwc
    simp only [Function.update_self, Function.update_of_ne hcb, Function.update_of_ne hcb.symm,
      Function.update_of_ne hca, Function.update_of_ne hba, ↓reduceIte]
  · by_cases hwb : w = b
    · subst hwb
      simp only [Function.update_self, Function.update_of_ne hba,
        Function.update_of_ne hcb.symm,
        Function.update_of_ne hca, if_neg hwc, ↓reduceIte]
    · by_cases hwa : w = a
      · subst hwa
        simp only [Function.update_self, Function.update_of_ne hwc, Function.update_of_ne hwb,
          Function.update_of_ne hca,
          Function.update_of_ne hba,
          Function.update_of_ne hcb.symm,
          if_neg hwc, if_neg hwb, ↓reduceIte]
      · rw [Function.update_of_ne hwb, Function.update_of_ne hwc, Function.update_of_ne hwa,
          if_neg hwc, if_neg hwb, if_neg hwa]

private lemma bool_maj_carry (va vb vc : Bool) :
    xor va ((xor vc va) && (xor vb va)) =
      decide (2 ≤ (if va then 1 else 0) + (if vb then 1 else 0) + (if vc then 1 else 0)) := by
  cases va <;> cases vb <;> cases vc <;> decide

private lemma bool_uma_step (va vb vc : Bool) :
    let c1 := xor vc va
    let b1 := xor vb va
    let a1 := xor va (c1 && b1)
    let a2 := xor a1 (c1 && b1)
    let c2 := xor c1 a2
    let b2 := xor b1 c2
    a2 = va ∧ c2 = vc ∧ b2 = xor (xor va vb) vc := by
  cases va <;> cases vb <;> cases vc <;> decide

/-- Shift embedding `Fin (1 + 2 * w) ↪ Fin (1 + 2 * (w + 1))` mapping `0 ↦ 1` (`a_0`) and `1+j ↦ 3+j`. -/
private def cuccaroShiftEmb (w : ℕ) : Fin (1 + 2 * w) ↪ Fin (1 + 2 * (w + 1)) where
  toFun i := if i.1 = 0 then ⟨1, by omega⟩ else ⟨i.1 + 2, by have := i.isLt; omega⟩
  inj' a b h := by
    have hv := congrArg Fin.val h; dsimp only at hv
    by_cases ha : a.1 = 0 <;> by_cases hb : b.1 = 0
    · exact Fin.ext (ha.trans hb.symm)
    · simp only [ha, hb, ↓reduceIte] at hv; omega
    · simp only [ha, hb, ↓reduceIte] at hv; omega
    · simp only [ha, hb, ↓reduceIte] at hv; exact Fin.ext (by omega)

@[simp] private lemma cuccaroShiftEmb_val (w : ℕ) (i : Fin (1 + 2 * w)) :
    (cuccaroShiftEmb w i).1 = if i.1 = 0 then 1 else i.1 + 2 := by
  change (if i.1 = 0 then (⟨1, _⟩ : Fin (1 + 2 * (w + 1))) else ⟨i.1 + 2, _⟩).1 = _
  split_ifs <;> rfl

/-- Recursive Cuccaro core on interleaved wires `(c0, a_0, b_0, ..., a_{w-1}, b_{w-1})`. -/
noncomputable def cuccaroCore : (w : ℕ) → LayeredCircuit (1 + 2 * w)
  | 0 => LayeredCircuit.id 1
  | w + 1 =>
    let maj0 := cuccaroMAJ (⟨0, by omega⟩ : Fin (1 + 2 * (w + 1))) ⟨2, by omega⟩ ⟨1, by omega⟩
      (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    let mid := (cuccaroCore w).mapWires (cuccaroShiftEmb w)
    let uma0 := cuccaroUMA (⟨0, by omega⟩ : Fin (1 + 2 * (w + 1))) ⟨2, by omega⟩ ⟨1, by omega⟩
      (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    maj0.seq (mid.seq uma0)

lemma cuccaroCore_size (w : ℕ) : (cuccaroCore w).size = 14 * w := by
  induction w with
  | zero => simp [cuccaroCore]
  | succ w ih =>
    simp only [cuccaroCore, LayeredCircuit.seq_size, LayeredCircuit.mapWires_size,
      cuccaroMAJ_size, cuccaroUMA_size, ih]
    omega

theorem act_cuccaroCore_ket (w : ℕ) (cin : Bool) (a b : Qubits w) :
    let init : Qubits (1 + 2 * w) := fun u =>
      if h0 : u.1 = 0 then cin
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    let sNat := bitsToNatLSB a + bitsToNatLSB b + (if cin then 1 else 0)
    let sout := natToBitsLSB w sNat
    let out : Qubits (1 + 2 * w) := fun u =>
      if h0 : u.1 = 0 then cin
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else sout ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    act (cuccaroCore w).unitary (ket init) = ket out := by
  induction w generalizing cin with
  | zero =>
    intro init sNat sout out
    simp only [cuccaroCore, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    simp [init, out]
  | succ w ih =>
    intro init sNat sout out
    dsimp only [cuccaroCore]
    simp only [LayeredCircuit.seq_unitary, act_mul]
    let c0 : Fin (1 + 2 * (w + 1)) := ⟨0, by omega⟩
    let a0 : Fin (1 + 2 * (w + 1)) := ⟨1, by omega⟩
    let b0 : Fin (1 + 2 * (w + 1)) := ⟨2, by omega⟩
    have hc0_v : c0.1 = 0 := rfl
    have ha0_v : a0.1 = 1 := rfl
    have hb0_v : b0.1 = 2 := rfl
    have hc_init : init c0 = cin := by dsimp [init, c0]
    have ha_init : init a0 = a 0 := by
      dsimp only [init]; rw [dif_neg (by omega), dif_pos (by omega)]
      exact congrArg a (Fin.ext (by dsimp; omega))
    have hb_init : init b0 = b 0 := by
      dsimp only [init]; rw [dif_neg (by omega), dif_neg (by omega)]
      exact congrArg b (Fin.ext (by dsimp; omega))
    let a' : Qubits w := fun i => a i.succ
    let b' : Qubits w := fun i => b i.succ
    let cin' := decide (2 ≤ (if a 0 then 1 else 0) + (if b 0 then 1 else 0) + (if cin then 1 else 0))
    let z1 : Qubits (1 + 2 * (w + 1)) := fun u =>
      if u = c0 then xor cin (a 0)
      else if u = b0 then xor (b 0) (a 0)
      else if u = a0 then cin'
      else init u
    have hmaj : act (cuccaroMAJ c0 b0 a0 (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))).unitary (ket init) =
        ket z1 := by
      rw [act_cuccaroMAJ_ket]
      congr 1; funext u
      rw [hc_init, ha_init, hb_init]
      by_cases huc : u = c0
      · simp [z1, huc]
      · by_cases hub : u = b0
        · simp [z1, hub]
        · by_cases hua : u = a0
          · simp [z1, hua, cin', bool_maj_carry]
          · simp [z1, huc, hub, hua]
    have hih := ih cin' a' b'
    dsimp only at hih
    let emb := cuccaroShiftEmb w
    have hz1_comp : z1 ∘ emb = fun u : Fin (1 + 2 * w) =>
        if h0 : u.1 = 0 then cin'
        else if hm : (u.1 - 1) % 2 = 0 then a' ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
        else b' ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ := by
      funext u
      dsimp only [Function.comp_apply]
      by_cases hu0 : u.1 = 0
      · have he : emb u = a0 := Fin.ext (by simp [emb, a0, hu0])
        rw [he, dif_pos hu0]
        dsimp only [z1]
        have h1 : a0 ≠ c0 := Fin.ne_of_val_ne (by omega)
        have h2 : a0 ≠ b0 := Fin.ne_of_val_ne (by omega)
        rw [if_neg h1, if_neg h2, if_pos rfl]
      · rw [dif_neg hu0]
        have hev : (emb u).1 = u.1 + 2 := by simp [emb, hu0]
        have hnc : emb u ≠ c0 := Fin.ne_of_val_ne (by omega)
        have hnb : emb u ≠ b0 := Fin.ne_of_val_ne (by omega)
        have hna : emb u ≠ a0 := Fin.ne_of_val_ne (by omega)
        dsimp only [z1]; rw [if_neg hnc, if_neg hnb, if_neg hna]
        dsimp only [init, a', b']
        rw [dif_neg (by omega)]
        have hmod : ((emb u).1 - 1) % 2 = 0 ↔ (u.1 - 1) % 2 = 0 := by omega
        have hdiv : ((emb u).1 - 1) / 2 = (u.1 - 1) / 2 + 1 := by omega
        by_cases hp1 : ((emb u).1 - 1) % 2 = 0 <;> by_cases hp2 : (u.1 - 1) % 2 = 0
        · rw [dif_pos hp1, dif_pos hp2]; exact congrArg a (Fin.ext (by dsimp [Fin.succ]; omega))
        · exact absurd (hmod.mp hp1) hp2
        · exact absurd (hmod.mpr hp2) hp1
        · rw [dif_neg hp1, dif_neg hp2]; exact congrArg b (Fin.ext (by dsimp [Fin.succ]; omega))
    let sNat' := bitsToNatLSB a' + bitsToNatLSB b' + (if cin' then 1 else 0)
    let sout' := natToBitsLSB w sNat'
    let z2 : Qubits (1 + 2 * (w + 1)) := fun u =>
      if hc : u = c0 then xor cin (a 0)
      else if hb : u = b0 then xor (b 0) (a 0)
      else if ha : u = a0 then cin'
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else sout' ⟨(u.1 - 1) / 2 - 1, by
        have hu3 : 3 ≤ u.1 := by
          by_contra hlt
          have : u.1 = 0 ∨ u.1 = 1 ∨ u.1 = 2 := by omega
          rcases this with h | h | h
          · exact hc (Fin.ext h)
          · exact ha (Fin.ext h)
          · exact hb (Fin.ext h)
        have := u.isLt; omega⟩
    have hmid : act ((cuccaroCore w).mapWires emb).unitary (ket z1) = ket z2 := by
      refine act_mapWires_ket (cuccaroCore w) emb z1 _ (by rw [hz1_comp]; exact hih) z2 ?_ ?_
      · funext u
        dsimp only [Function.comp_apply]
        by_cases hu0 : u.1 = 0
        · have he : emb u = a0 := Fin.ext (by simp [emb, a0, hu0])
          rw [he, dif_pos hu0]
          dsimp only [z2]
          rw [dif_neg (Fin.ne_of_val_ne (by omega)),
            dif_neg (Fin.ne_of_val_ne (by omega)), dif_pos rfl]
        · rw [dif_neg hu0]
          have hev : (emb u).1 = u.1 + 2 := by simp [emb, hu0]
          have hnc : emb u ≠ c0 := Fin.ne_of_val_ne (by omega)
          have hnb : emb u ≠ b0 := Fin.ne_of_val_ne (by omega)
          have hna : emb u ≠ a0 := Fin.ne_of_val_ne (by omega)
          dsimp only [z2]; rw [dif_neg hnc, dif_neg hnb, dif_neg hna]
          have hmod : ((emb u).1 - 1) % 2 = 0 ↔ (u.1 - 1) % 2 = 0 := by omega
          have hdiv1 : ((emb u).1 - 1) / 2 = (u.1 - 1) / 2 + 1 := by omega
          have hdiv2 : ((emb u).1 - 1) / 2 - 1 = (u.1 - 1) / 2 := by omega
          by_cases hp1 : ((emb u).1 - 1) % 2 = 0 <;> by_cases hp2 : (u.1 - 1) % 2 = 0
          · rw [dif_pos hp1, dif_pos hp2]; exact congrArg a (Fin.ext (by dsimp [Fin.succ]; omega))
          · exact absurd (hmod.mp hp1) hp2
          · exact absurd (hmod.mpr hp2) hp1
          · rw [dif_neg hp1, dif_neg hp2]; exact congrArg sout' (Fin.ext (by dsimp; omega))
      · intro u hu
        have hu_le2 : u.1 = 0 ∨ u.1 = 2 := by
          by_contra h
          have hne0 : u.1 ≠ 0 := fun h0 => h (Or.inl h0)
          have hne2 : u.1 ≠ 2 := fun h2 => h (Or.inr h2)
          by_cases hu1 : u.1 = 1
          · exact hu ⟨0, Fin.ext (by simp [emb, hu1])⟩
          · exact hu ⟨⟨u.1 - 2, by have := u.isLt; omega⟩,
              Fin.ext (by simp [emb, show u.1 - 2 ≠ 0 by omega]; omega)⟩
        rcases hu_le2 with h0 | h2
        · have huc : u = c0 := Fin.ext h0
          rw [huc]; simp [z1, z2]
        · have hub : u = b0 := Fin.ext h2
          rw [hub]; simp [z1, z2]
    have hsNat_eq : sNat = 2 * sNat' + (if xor (xor (a 0) (b 0)) cin then 1 else 0) := by
      have ha_s : bitsToNatLSB a = 2 * bitsToNatLSB a' + (if a 0 then 1 else 0) := by
        simp only [bitsToNatLSB, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero]
        have hs : (∑ i : Fin w, if a i.succ then 2 ^ (i.1 + 1) else 0) =
            2 * ∑ i : Fin w, if a' i then 2 ^ i.1 else 0 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [a']; split_ifs <;> simp [pow_succ']
        rw [hs]; omega
      have hb_s : bitsToNatLSB b = 2 * bitsToNatLSB b' + (if b 0 then 1 else 0) := by
        simp only [bitsToNatLSB, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero]
        have hs : (∑ i : Fin w, if b i.succ then 2 ^ (i.1 + 1) else 0) =
            2 * ∑ i : Fin w, if b' i then 2 ^ i.1 else 0 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [b']; split_ifs <;> simp [pow_succ']
        rw [hs]; omega
      dsimp only [sNat, sNat']
      rw [ha_s, hb_s]
      cases hax : a 0 <;> cases hbx : b 0 <;> cases hcx : cin <;> simp [cin', hax, hbx, hcx] <;> omega
    have hsout0 : sout 0 = xor (xor (a 0) (b 0)) cin := by
      simp only [sout, natToBitsLSB, Fin.val_zero, Nat.testBit_zero]
      rw [hsNat_eq]
      cases xor (xor (a 0) (b 0)) cin <;> simp
    have hsout_succ : ∀ i : Fin w, sout i.succ = sout' i := fun i => by
      simp only [sout, sout', natToBitsLSB, Fin.val_succ]
      rw [hsNat_eq, Nat.testBit_succ]
      have hdiv2 : (2 * sNat' + (if xor (xor (a 0) (b 0)) cin then 1 else 0)) / 2 = sNat' := by
        split_ifs <;> omega
      rw [hdiv2]
    rw [hmaj, hmid, act_cuccaroUMA_ket]
    congr 1; funext u
    have hbc : b0 ≠ c0 := Fin.ne_of_val_ne (by omega)
    have hac : a0 ≠ c0 := Fin.ne_of_val_ne (by omega)
    have hab : a0 ≠ b0 := Fin.ne_of_val_ne (by omega)
    have hz2_c : z2 c0 = xor cin (a 0) := by simp [z2]
    have hz2_b : z2 b0 = xor (b 0) (a 0) := by simp [z2, hbc]
    have hz2_a : z2 a0 = cin' := by simp [z2, hac, hab]
    have hcin' : cin' = xor (a 0) (xor cin (a 0) && xor (b 0) (a 0)) := (bool_maj_carry (a 0) (b 0) cin).symm
    have huma_a : xor (z2 a0) (z2 c0 && z2 b0) = a 0 := by
      rw [hz2_a, hz2_c, hz2_b, hcin']
      cases a 0 <;> cases b 0 <;> cases cin <;> rfl
    have huma_c : xor (z2 c0) (xor (z2 a0) (z2 c0 && z2 b0)) = cin := by
      rw [hz2_a, hz2_c, hz2_b, hcin']
      cases a 0 <;> cases b 0 <;> cases cin <;> rfl
    have huma_b : xor (z2 b0) (xor (z2 c0) (xor (z2 a0) (z2 c0 && z2 b0))) =
        xor (xor (a 0) (b 0)) cin := by
      rw [hz2_a, hz2_c, hz2_b, hcin']
      cases a 0 <;> cases b 0 <;> cases cin <;> rfl
    by_cases huc : u = c0
    · subst huc; rw [if_pos rfl, huma_c]; dsimp [out, c0]
    · rw [if_neg huc]
      by_cases hub : u = b0
      · subst hub; rw [if_pos rfl, huma_b]
        dsimp only [out]; rw [dif_neg (by omega), dif_neg (by omega)]
        have hb0_idx : (⟨(b0.1 - 1) / 2, by have := b0.isLt; omega⟩ : Fin (w + 1)) = 0 :=
          Fin.ext (by dsimp; omega)
        rw [hb0_idx, hsout0]
      · rw [if_neg hub]
        by_cases hua : u = a0
        · subst hua; rw [if_pos rfl, huma_a]
          dsimp only [out]; rw [dif_neg (by omega), dif_pos (by omega)]
          exact congrArg a (Fin.ext (by dsimp; omega))
        · rw [if_neg hua]
          have hge3 : 3 ≤ u.1 := by
            by_contra h; have h1 : u.1 = 0 ∨ u.1 = 1 ∨ u.1 = 2 := by omega
            rcases h1 with h | h | h
            · exact huc (Fin.ext h)
            · exact hua (Fin.ext h)
            · exact hub (Fin.ext h)
          have hu0 : u.1 ≠ 0 := by omega
          dsimp only [z2, out]
          rw [dif_neg huc, dif_neg hub, dif_neg hua, dif_neg hu0]
          by_cases hm : (u.1 - 1) % 2 = 0
          · rw [dif_pos hm, dif_pos hm]
          · rw [dif_neg hm, dif_neg hm]
            have hidx_eq : (⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ : Fin (w + 1)) =
                Fin.succ ⟨(u.1 - 1) / 2 - 1, by have := u.isLt; omega⟩ := by
              apply Fin.ext; dsimp [Fin.succ]; omega
            rw [hidx_eq, hsout_succ]

private def cuccaroWireEmb (w : ℕ) : Fin (1 + 2 * w) ↪ Fin ((w + w) + 1) where
  toFun u :=
    if u.1 = 0 then ⟨w + w, by omega⟩
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    else ⟨w + (u.1 - 1) / 2, by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

@[simp] private lemma cuccaroWireEmb_val (w : ℕ) (u : Fin (1 + 2 * w)) :
    (cuccaroWireEmb w u).1 =
      if u.1 = 0 then w + w
      else if (u.1 - 1) % 2 = 0 then (u.1 - 1) / 2
      else w + (u.1 - 1) / 2 := by
  change (if u.1 = 0 then (⟨w + w, _⟩ : Fin ((w + w) + 1))
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, _⟩ else ⟨w + (u.1 - 1) / 2, _⟩).1 = _
  split_ifs <;> rfl

/-- In-place `w`-bit adder `(a, b) ↦ (a, natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b))`
in `14 * w` gates with `1` clean ancilla. -/
noncomputable def addInPlaceCircuit (w : ℕ) : LayeredCircuit ((w + w) + 1) :=
  (cuccaroCore w).mapWires (cuccaroWireEmb w)

lemma addInPlaceCircuit_size (w : ℕ) : (addInPlaceCircuit w).size = 14 * w := by
  simp [addInPlaceCircuit, cuccaroCore_size]

def addInPlaceFn (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let sum := natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)
  fun i => if h : i.1 < w then a ⟨i.1, h⟩ else sum ⟨i.1 - w, by omega⟩

theorem addInPlaceCircuit_implements (w : ℕ) :
    (addInPlaceCircuit w).ImplementsOnClean (permMat (addInPlaceFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (w + w) 1 x
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let emb := cuccaroWireEmb w
  have hz0_comp : z0 ∘ emb = fun u : Fin (1 + 2 * w) =>
      if h0 : u.1 = 0 then false
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ := by
    funext u
    dsimp only [Function.comp_apply]
    by_cases h0 : u.1 = 0
    · rw [dif_pos h0]; dsimp only [z0]; exact padZero_val_ge x _ (by simp [emb, h0])
    · rw [dif_neg h0]
      by_cases hm : (u.1 - 1) % 2 = 0
      · have hev : (emb u).1 = (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_pos hm]; dsimp only [z0]
        rw [padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext (by dsimp; omega))
      · have hev : (emb u).1 = w + (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_neg hm]; dsimp only [z0]
        rw [padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext (by dsimp; omega))
  have hact_core := act_cuccaroCore_ket w false a b
  dsimp only at hact_core
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hact_core
  have hact := act_mapWires_ket (cuccaroCore w) emb z0 _ (by rw [hz0_comp]; exact hact_core)
    (padZero (w + w) 1 (addInPlaceFn w x)) ?_ ?_
  · exact hact
  · funext u
    dsimp only [Function.comp_apply]
    by_cases h0 : u.1 = 0
    · rw [dif_pos h0]
      have hev : (emb u).1 = w + w := by simp [emb, h0]
      exact padZero_val_ge (addInPlaceFn w x) (emb u) (by omega)
    · rw [dif_neg h0]
      by_cases hm : (u.1 - 1) % 2 = 0
      · have hev : (emb u).1 = (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_pos hm, padZero_val_lt _ _ (by omega)]
        dsimp only [addInPlaceFn]; rw [dif_pos (by omega)]
        exact congrArg x (Fin.ext (by dsimp; omega))
      · have hev : (emb u).1 = w + (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_neg hm, padZero_val_lt _ _ (by omega)]
        dsimp only [addInPlaceFn]; rw [dif_neg (by omega)]
        exact congrArg (natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)) (Fin.ext (by dsimp; omega))
  · intro u hu
    exfalso; apply hu
    have hlt := u.isLt
    by_cases huw : u.1 = w + w
    · exact ⟨0, Fin.ext (by simp [emb, huw])⟩
    · by_cases hw : u.1 < w
      · exact ⟨⟨1 + 2 * u.1, by omega⟩, Fin.ext (by simp [emb])⟩
      · exact ⟨⟨1 + 2 * (u.1 - w) + 1, by omega⟩, Fin.ext (by simp [emb]; omega)⟩

/-- In-place `w`-bit subtractor `(a, b) ↦ (a, (b - a) mod 2^w)` (`(addInPlaceCircuit w).adj`). -/
noncomputable def subInPlaceCircuit (w : ℕ) : LayeredCircuit ((w + w) + 1) :=
  (addInPlaceCircuit w).adj

lemma subInPlaceCircuit_size (w : ℕ) : (subInPlaceCircuit w).size = 14 * w := by
  simp [subInPlaceCircuit, addInPlaceCircuit_size]

def subInPlaceFn (w : ℕ) (x : Qubits (w + w)) : Qubits (w + w) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let diff := natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a)
  fun i => if h : i.1 < w then a ⟨i.1, h⟩ else diff ⟨i.1 - w, by omega⟩

lemma addInPlaceFn_subInPlaceFn (w : ℕ) (x : Qubits (w + w)) :
    addInPlaceFn w (subInPlaceFn w x) = x ∧ subInPlaceFn w (addInPlaceFn w x) = x := by
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  have ha_lt := bitsToNatLSB_lt w a
  have hb_lt := bitsToNatLSB_lt w b
  have ha_s : (fun i : Fin w => subInPlaceFn w x ⟨i.1, by omega⟩) = a := by
    funext i; simp [subInPlaceFn, a, i.isLt]
  have hb_s : (fun i : Fin w => subInPlaceFn w x ⟨w + i.1, by omega⟩) =
      natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) := by
    funext i; simp [subInPlaceFn, a, b, show ¬ w + i.1 < w by omega]
  have ha_a : (fun i : Fin w => addInPlaceFn w x ⟨i.1, by omega⟩) = a := by
    funext i; simp [addInPlaceFn, a, i.isLt]
  have hb_a : (fun i : Fin w => addInPlaceFn w x ⟨w + i.1, by omega⟩) =
      natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b) := by
    funext i; simp [addInPlaceFn, a, b, show ¬ w + i.1 < w by omega]
  have hmod1 : (bitsToNatLSB a + (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) % 2 ^ w) % 2 ^ w =
      bitsToNatLSB b := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
      show bitsToNatLSB a + (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) = 2 ^ w + bitsToNatLSB b by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hb_lt]
  have hmod2 : (2 ^ w + (bitsToNatLSB a + bitsToNatLSB b) % 2 ^ w - bitsToNatLSB a) % 2 ^ w =
      bitsToNatLSB b := by
    by_cases hsum : bitsToNatLSB a + bitsToNatLSB b < 2 ^ w
    · rw [Nat.mod_eq_of_lt hsum, show 2 ^ w + (bitsToNatLSB a + bitsToNatLSB b) - bitsToNatLSB a =
        2 ^ w + bitsToNatLSB b by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hb_lt]
    · have hmod_eq : (bitsToNatLSB a + bitsToNatLSB b) % 2 ^ w =
          bitsToNatLSB a + bitsToNatLSB b - 2 ^ w := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hmod_eq, show 2 ^ w + (bitsToNatLSB a + bitsToNatLSB b - 2 ^ w) - bitsToNatLSB a =
        bitsToNatLSB b by omega, Nat.mod_eq_of_lt hb_lt]
  have hntb_eq : ∀ u : ℕ, natToBitsLSB w (u % 2 ^ w) = natToBitsLSB w u := fun u => by
    funext i; simp [natToBitsLSB, Nat.testBit_mod_two_pow, i.isLt]
  constructor
  · funext i; by_cases hi : i.1 < w
    · simp [addInPlaceFn, subInPlaceFn, hi]
    · simp only [addInPlaceFn, hi, ↓reduceDIte, ha_s, hb_s]
      have h1 : bitsToNatLSB (natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a)) =
          (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) % 2 ^ w := by
        rw [← hntb_eq, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
      rw [h1, ← hntb_eq, hmod1, natToBitsLSB_bitsToNatLSB]
      have hie : b ⟨i.1 - w, by omega⟩ = x i := by
        dsimp only [b]; exact congrArg x (Fin.ext (by dsimp; omega))
      exact hie
  · funext i; by_cases hi : i.1 < w
    · simp [subInPlaceFn, addInPlaceFn, hi]
    · simp only [subInPlaceFn, hi, ↓reduceDIte, ha_a, hb_a]
      have h1 : bitsToNatLSB (natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)) =
          (bitsToNatLSB a + bitsToNatLSB b) % 2 ^ w := by
        rw [← hntb_eq, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
      rw [h1, ← hntb_eq, hmod2, natToBitsLSB_bitsToNatLSB]
      have hie : b ⟨i.1 - w, by omega⟩ = x i := by
        dsimp only [b]; exact congrArg x (Fin.ext (by dsimp; omega))
      exact hie

theorem subInPlaceCircuit_implements (w : ℕ) :
    (subInPlaceCircuit w).ImplementsOnClean (permMat (subInPlaceFn w)) :=
  adj_implementsOnClean_perm (addInPlaceCircuit w)
    (fun x => (addInPlaceFn_subInPlaceFn w x).2)
    (fun x => (addInPlaceFn_subInPlaceFn w x).1)
    (addInPlaceCircuit_implements w)

/-- Recursive Cuccaro carry-out: XORs `decide (2^w ≤ a + b + cin)` into wire `1 + 2*w`. -/
private def cuccaroCarryShiftEmb (w : ℕ) :
    Fin (1 + 2 * w + 1) ↪ Fin (1 + 2 * (w + 1) + 1) where
  toFun i :=
    if i.1 = 0 then ⟨1, by omega⟩
    else if i.1 = 1 + 2 * w then ⟨1 + 2 * (w + 1), by omega⟩
    else ⟨i.1 + 2, by have := i.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

@[simp] private lemma cuccaroCarryShiftEmb_val (w : ℕ) (i : Fin (1 + 2 * w + 1)) :
    (cuccaroCarryShiftEmb w i).1 =
      if i.1 = 0 then 1 else if i.1 = 1 + 2 * w then 1 + 2 * (w + 1) else i.1 + 2 := by
  change (if i.1 = 0 then (⟨1, _⟩ : Fin (1 + 2 * (w + 1) + 1))
    else if i.1 = 1 + 2 * w then ⟨1 + 2 * (w + 1), _⟩ else ⟨i.1 + 2, _⟩).1 = _
  split_ifs <;> rfl

noncomputable def cuccaroCarryOut : (w : ℕ) → LayeredCircuit (1 + 2 * w + 1)
  | 0 => cnotGate ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.ne_of_val_ne (by simp))
  | w + 1 =>
    let maj0 := cuccaroMAJ (⟨0, by omega⟩ : Fin (1 + 2 * (w + 1) + 1)) ⟨2, by omega⟩ ⟨1, by omega⟩
      (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp)) (Fin.ne_of_val_ne (by simp))
    let mid := (cuccaroCarryOut w).mapWires (cuccaroCarryShiftEmb w)
    maj0.seq (mid.seq maj0.adj)

lemma cuccaroCarryOut_size (w : ℕ) : (cuccaroCarryOut w).size = 14 * w + 1 := by
  induction w with
  | zero => simp [cuccaroCarryOut]
  | succ w ih =>
    simp only [cuccaroCarryOut, LayeredCircuit.seq_size, LayeredCircuit.adj_size,
      LayeredCircuit.mapWires_size, cuccaroMAJ_size, ih]
    omega

theorem act_cuccaroCarryOut_ket (w : ℕ) (cin tgt : Bool) (a b : Qubits w) :
    let init : Qubits (1 + 2 * w + 1) := fun u =>
      if h0 : u.1 = 0 then cin
      else if ht : u.1 = 1 + 2 * w then tgt
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    let carryBit := decide (2 ^ w ≤ bitsToNatLSB a + bitsToNatLSB b + (if cin then 1 else 0))
    let out : Qubits (1 + 2 * w + 1) := Function.update init ⟨1 + 2 * w, by omega⟩ (xor tgt carryBit)
    act (cuccaroCarryOut w).unitary (ket init) = ket out := by
  induction w generalizing cin with
  | zero =>
    intro init carryBit out
    simp only [cuccaroCarryOut, act_cnotGate_ket]
    congr 1; funext u
    have h0 : init ⟨0, by omega⟩ = cin := by dsimp [init]
    have h1 : init ⟨1, by omega⟩ = tgt := by
      dsimp only [init]; rw [dif_neg (by omega), dif_pos rfl]
    have hc : carryBit = cin := by
      dsimp only [carryBit]; simp only [bitsToNatLSB, Finset.univ_eq_empty, Finset.sum_empty,
        pow_zero, zero_add]
      cases cin <;> simp
    have h1_eq : (⟨1 + 2 * 0, by omega⟩ : Fin (1 + 2 * 0 + 1)) = ⟨1, by omega⟩ := rfl
    dsimp only [out]; rw [h1_eq]
    by_cases hu : u = ⟨1, by omega⟩
    · subst hu; rw [Function.update_self, Function.update_self, h0, h1, hc]
    · rw [Function.update_of_ne hu, Function.update_of_ne hu]
  | succ w ih =>
    intro init carryBit out
    dsimp only [cuccaroCarryOut]
    simp only [LayeredCircuit.seq_unitary, act_mul]
    let c0 : Fin (1 + 2 * (w + 1) + 1) := ⟨0, by omega⟩
    let a0 : Fin (1 + 2 * (w + 1) + 1) := ⟨1, by omega⟩
    let b0 : Fin (1 + 2 * (w + 1) + 1) := ⟨2, by omega⟩
    let tW : Fin (1 + 2 * (w + 1) + 1) := ⟨1 + 2 * (w + 1), by omega⟩
    have hc0_v : c0.1 = 0 := rfl
    have ha0_v : a0.1 = 1 := rfl
    have hb0_v : b0.1 = 2 := rfl
    have htW_v : tW.1 = 1 + 2 * (w + 1) := rfl
    let maj0 := cuccaroMAJ c0 b0 a0 (Fin.ne_of_val_ne (by omega))
      (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
    have hc_init : init c0 = cin := by dsimp [init, c0]
    have ha_init : init a0 = a 0 := by
      dsimp only [init]; rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
      exact congrArg a (Fin.ext (by dsimp; omega))
    have hb_init : init b0 = b 0 := by
      dsimp only [init]; rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
      exact congrArg b (Fin.ext (by dsimp; omega))
    let a' : Qubits w := fun i => a i.succ
    let b' : Qubits w := fun i => b i.succ
    let cin' := decide (2 ≤ (if a 0 then 1 else 0) + (if b 0 then 1 else 0) + (if cin then 1 else 0))
    let z1 : Qubits (1 + 2 * (w + 1) + 1) := fun u =>
      if u = c0 then xor cin (a 0)
      else if u = b0 then xor (b 0) (a 0)
      else if u = a0 then cin'
      else init u
    have hmaj : act maj0.unitary (ket init) = ket z1 := by
      dsimp only [maj0]; rw [act_cuccaroMAJ_ket]; congr 1; funext u
      rw [hc_init, ha_init, hb_init]
      by_cases huc : u = c0
      · simp [z1, huc]
      · by_cases hub : u = b0
        · simp [z1, hub]
        · by_cases hua : u = a0
          · simp [z1, hua, cin', bool_maj_carry]
          · simp [z1, huc, hub, hua]
    have hcarry_eq : carryBit =
        decide (2 ^ w ≤ bitsToNatLSB a' + bitsToNatLSB b' + (if cin' then 1 else 0)) := by
      have ha_s : bitsToNatLSB a = 2 * bitsToNatLSB a' + (if a 0 then 1 else 0) := by
        simp only [bitsToNatLSB, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero]
        have hs : (∑ i : Fin w, if a i.succ then 2 ^ (i.1 + 1) else 0) =
            2 * ∑ i : Fin w, if a' i then 2 ^ i.1 else 0 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [a']; split_ifs <;> simp [pow_succ']
        rw [hs]; omega
      have hb_s : bitsToNatLSB b = 2 * bitsToNatLSB b' + (if b 0 then 1 else 0) := by
        simp only [bitsToNatLSB, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero]
        have hs : (∑ i : Fin w, if b i.succ then 2 ^ (i.1 + 1) else 0) =
            2 * ∑ i : Fin w, if b' i then 2 ^ i.1 else 0 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [b']; split_ifs <;> simp [pow_succ']
        rw [hs]; omega
      dsimp only [carryBit]
      rw [ha_s, hb_s, pow_succ', Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      cases hax : a 0 <;> cases hbx : b 0 <;> cases hcx : cin <;> simp [cin', hax, hbx, hcx] <;> omega
    let emb := cuccaroCarryShiftEmb w
    have hih := ih cin' a' b'
    dsimp only at hih
    have hz1_comp : z1 ∘ emb = fun u : Fin (1 + 2 * w + 1) =>
        if h0 : u.1 = 0 then cin'
        else if ht : u.1 = 1 + 2 * w then tgt
        else if hm : (u.1 - 1) % 2 = 0 then a' ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
        else b' ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ := by
      funext u
      dsimp only [Function.comp_apply]
      by_cases hu0 : u.1 = 0
      · have he : emb u = a0 := Fin.ext (by simp [emb, a0, hu0])
        rw [he, dif_pos hu0]
        dsimp only [z1]
        rw [if_neg (Fin.ne_of_val_ne (by omega)),
          if_neg (Fin.ne_of_val_ne (by omega)), if_pos rfl]
      · rw [dif_neg hu0]
        by_cases hut : u.1 = 1 + 2 * w
        · have he : emb u = tW := Fin.ext (by simp [emb, tW, hut])
          rw [he, dif_pos hut]
          dsimp only [z1]
          rw [if_neg (Fin.ne_of_val_ne (by omega)),
            if_neg (Fin.ne_of_val_ne (by omega)),
            if_neg (Fin.ne_of_val_ne (by omega))]
          dsimp only [init]; rw [dif_neg (by omega), dif_pos (by omega)]
        · rw [dif_neg hut]
          have hev : (emb u).1 = u.1 + 2 := by simp [emb, hu0, hut]
          have hnc : emb u ≠ c0 := Fin.ne_of_val_ne (by omega)
          have hnb : emb u ≠ b0 := Fin.ne_of_val_ne (by omega)
          have hna : emb u ≠ a0 := Fin.ne_of_val_ne (by omega)
          dsimp only [z1]; rw [if_neg hnc, if_neg hnb, if_neg hna]
          dsimp only [init, a', b']
          rw [dif_neg (by omega), dif_neg (by omega)]
          have hmod : ((emb u).1 - 1) % 2 = 0 ↔ (u.1 - 1) % 2 = 0 := by omega
          have hdiv : ((emb u).1 - 1) / 2 = (u.1 - 1) / 2 + 1 := by omega
          by_cases hp1 : ((emb u).1 - 1) % 2 = 0 <;> by_cases hp2 : (u.1 - 1) % 2 = 0
          · rw [dif_pos hp1, dif_pos hp2]; exact congrArg a (Fin.ext (by dsimp [Fin.succ]; omega))
          · exact absurd (hmod.mp hp1) hp2
          · exact absurd (hmod.mpr hp2) hp1
          · rw [dif_neg hp1, dif_neg hp2]; exact congrArg b (Fin.ext (by dsimp [Fin.succ]; omega))
    let z2 := Function.update z1 tW (xor tgt carryBit)
    have hmid : act ((cuccaroCarryOut w).mapWires emb).unitary (ket z1) = ket z2 := by
      refine act_mapWires_ket (cuccaroCarryOut w) emb z1 _ (by rw [hz1_comp]; exact hih) z2 ?_ ?_
      · funext u
        dsimp only [Function.comp_apply]
        by_cases hu0 : u.1 = 0
        · have he : emb u = a0 := Fin.ext (by simp [emb, a0, hu0])
          have hne : a0 ≠ tW := Fin.ne_of_val_ne (by omega)
          have hne' : u ≠ ⟨1 + 2 * w, by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
          rw [he]; dsimp only [z2]; rw [Function.update_of_ne hne, Function.update_of_ne hne']
          rw [← he]
          exact congrFun hz1_comp u
        · by_cases hut : u.1 = 1 + 2 * w
          · have he : emb u = tW := Fin.ext (by simp [emb, tW, hut])
            have hu_eq : u = ⟨1 + 2 * w, by omega⟩ := Fin.ext hut
            rw [he, hu_eq]; dsimp only [z2]; rw [Function.update_self, Function.update_self, hcarry_eq]
          · have hev : (emb u).1 = u.1 + 2 := by simp [emb, hu0, hut]
            have hne1 : emb u ≠ tW := Fin.ne_of_val_ne (by omega)
            have hne2 : u ≠ ⟨1 + 2 * w, by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
            dsimp only [z2]; rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
            exact congrFun hz1_comp u
      · intro u hu
        have hne_t : u ≠ tW := fun heq => hu ⟨⟨1 + 2 * w, by omega⟩, by
          apply Fin.ext; simp [emb, heq, tW]⟩
        dsimp only [z2]; rw [Function.update_of_ne hne_t]
    have hmaj_uses : maj0.UsesOnly {c0, b0, a0} := by
      refine LayeredCircuit.seq_usesOnly
        ((cnotGate_usesOnly a0 b0 (Fin.ne_of_val_ne (by omega))).mono
          (by intro x hx; simp at hx ⊢; tauto))
        (LayeredCircuit.seq_usesOnly ?_ (toffoliOn_usesOnly c0 b0 a0
          (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega))))
      exact (cnotGate_usesOnly a0 c0 (Fin.ne_of_val_ne (by omega))).mono
        (by intro x hx; simp at hx ⊢; tauto)
    have hnot_tW : tW ∉ ({c0, b0, a0} : Finset (Fin (1 + 2 * (w + 1) + 1))) := by
      intro hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h <;> have hv := congrArg Fin.val h <;> omega
    have hupd_adj := act_ket_update_of_not_mem maj0 hmaj_uses tW hnot_tW hmaj (xor tgt carryBit)
    have hadj_z2 : act maj0.adj.unitary (ket z2) = ket out := by
      have hz2_eq : z2 = Function.update z1 tW (xor tgt carryBit) := rfl
      rw [hz2_eq, ← hupd_adj, ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp maj0.unitary_mem_unitaryGroup, act_one]
    rw [hmaj, hmid, hadj_z2]

private def flipRegCircuit (w : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit w
  | 0, _ => LayeredCircuit.id w
  | k + 1, hk => (flipRegCircuit w k (by omega)).seq (pauliXGate ⟨k, by omega⟩)

private lemma flipRegCircuit_size (w k : ℕ) (hk : k ≤ w) :
    (flipRegCircuit w k hk).size = k := by
  induction k with
  | zero => simp [flipRegCircuit]
  | succ k ih => simp [flipRegCircuit, ih (by omega)]

private lemma act_flipRegCircuit_ket (w k : ℕ) (hk : k ≤ w) (z : Qubits w) :
    act (flipRegCircuit w k hk).unitary (ket z) =
      ket (fun i => if i.1 < k then !z i else z i) := by
  induction k with
  | zero => simp [flipRegCircuit, LayeredCircuit.id_unitary, act_one]
  | succ k ih =>
    dsimp only [flipRegCircuit]; rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega),
      act_pauliXGate_ket]
    congr 1; funext i
    by_cases hik : i = ⟨k, by omega⟩
    · subst hik; simp [Function.update_self]
    · rw [Function.update_of_ne hik]
      have hne : i.1 ≠ k := fun h => hik (Fin.ext h)
      by_cases hi : i.1 < k <;> simp [hi, show i.1 < k + 1 ↔ i.1 < k ∨ i.1 = k by omega, hne]

private def ltFlipEmb (w : ℕ) : Fin w ↪ Fin ((w + w + 1) + 1) where
  toFun i := ⟨i.1, by omega⟩
  inj' a b h := Fin.ext (by have := congrArg Fin.val h; exact this)

@[simp] private lemma ltFlipEmb_val (w : ℕ) (i : Fin w) : (ltFlipEmb w i).1 = i.1 := rfl

private def ltCarryEmb (w : ℕ) : Fin (1 + 2 * w + 1) ↪ Fin ((w + w + 1) + 1) where
  toFun u :=
    if u.1 = 0 then ⟨w + w + 1, by omega⟩
    else if u.1 = 1 + 2 * w then ⟨w + w, by omega⟩
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    else ⟨w + (u.1 - 1) / 2, by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

@[simp] private lemma ltCarryEmb_val (w : ℕ) (u : Fin (1 + 2 * w + 1)) :
    (ltCarryEmb w u).1 =
      if u.1 = 0 then w + w + 1
      else if u.1 = 1 + 2 * w then w + w
      else if (u.1 - 1) % 2 = 0 then (u.1 - 1) / 2
      else w + (u.1 - 1) / 2 := by
  change (if u.1 = 0 then (⟨w + w + 1, _⟩ : Fin ((w + w + 1) + 1))
    else if u.1 = 1 + 2 * w then ⟨w + w, _⟩
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, _⟩ else ⟨w + (u.1 - 1) / 2, _⟩).1 = _
  split_ifs <;> rfl

/-- Unsigned register comparator `(a, b, t) ↦ (a, b, t ^^^ decide (a < b))` in `16 * w + 1` gates with `1` ancilla. -/
noncomputable def ltRegCircuit (w : ℕ) : LayeredCircuit ((w + w + 1) + 1) :=
  let flipA := (flipRegCircuit w w le_rfl).mapWires (ltFlipEmb w)
  let carry := (cuccaroCarryOut w).mapWires (ltCarryEmb w)
  flipA.seq (carry.seq flipA)

lemma ltRegCircuit_size (w : ℕ) : (ltRegCircuit w).size = 16 * w + 1 := by
  dsimp only [ltRegCircuit]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size, flipRegCircuit_size,
    cuccaroCarryOut_size]
  omega

def ltRegFn (w : ℕ) (x : Qubits (w + w + 1)) : Qubits (w + w + 1) :=
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  Function.update x ⟨w + w, by omega⟩
    (xor (x ⟨w + w, by omega⟩) (decide (bitsToNatLSB a < bitsToNatLSB b)))

theorem ltRegCircuit_implements (w : ℕ) :
    (ltRegCircuit w).ImplementsOnClean (permMat (ltRegFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (w + w + 1) 1 x
  let tgt : Fin ((w + w + 1) + 1) := ⟨w + w, by omega⟩
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let flipA := (flipRegCircuit w w le_rfl).mapWires (ltFlipEmb w)
  let carry := (cuccaroCarryOut w).mapWires (ltCarryEmb w)
  let z1 : Qubits ((w + w + 1) + 1) := fun u =>
    if u.1 < w then !z0 u else z0 u
  have hflip1 : act flipA.unitary (ket z0) = ket z1 := by
    refine act_mapWires_ket (flipRegCircuit w w le_rfl) (ltFlipEmb w) z0 _
      (act_flipRegCircuit_ket w w le_rfl _) z1 ?_ ?_
    · funext i
      simp [Function.comp_apply, z1, i.isLt]
    · intro u hu
      have hge : w ≤ u.1 := by
        by_contra hlt; exact hu ⟨⟨u.1, by omega⟩, Fin.ext rfl⟩
      simp [z1, hge]
  let z2 := Function.update z1 tgt (xor (z1 tgt) (decide (bitsToNatLSB a < bitsToNatLSB b)))
  have hz1_comp : z1 ∘ ltCarryEmb w = fun u : Fin (1 + 2 * w + 1) =>
      if h0 : u.1 = 0 then false
      else if ht : u.1 = 1 + 2 * w then z1 tgt
      else if hm : (u.1 - 1) % 2 = 0 then (!a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩)
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ := by
    funext u
    dsimp only [Function.comp_apply]
    by_cases h0 : u.1 = 0
    · rw [dif_pos h0]
      have he : ltCarryEmb w u = Fin.natAdd (w + w + 1) ⟨0, by omega⟩ := Fin.ext (by simp [h0])
      rw [he]; dsimp only [z1, z0]; rw [if_neg (by simp; omega), padZero_natAdd]
    · rw [dif_neg h0]
      by_cases ht : u.1 = 1 + 2 * w
      · rw [dif_pos ht]
        have he : ltCarryEmb w u = tgt := Fin.ext (by dsimp [tgt]; simp [ht])
        rw [he]
      · rw [dif_neg ht]
        by_cases hm : (u.1 - 1) % 2 = 0
        · rw [dif_pos hm]
          have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
          have hev : (ltCarryEmb w u).1 = (u.1 - 1) / 2 := by simp [h0, ht, hm]
          dsimp only [z1, z0]; rw [if_pos (by omega), padZero_val_lt x _ (by omega)]
          exact congrArg Bool.not (congrArg x (Fin.ext (by dsimp [a]; exact hev)))
        · rw [dif_neg hm]
          have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
          have hev : (ltCarryEmb w u).1 = w + (u.1 - 1) / 2 := by simp [h0, ht, hm]
          dsimp only [z1, z0]; rw [if_neg (by omega), padZero_val_lt x _ (by omega)]
          exact congrArg x (Fin.ext (by dsimp [b]; exact hev))
  have hcarry_eq : decide (2 ^ w ≤ bitsToNatLSB (fun i => !a i) + bitsToNatLSB b + (if false then 1 else 0)) =
      decide (bitsToNatLSB a < bitsToNatLSB b) := by
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
    exact bitsToNatLSB_complement_lt_iff w a b
  have hcarry : act carry.unitary (ket z1) = ket z2 := by
    have hact_c := act_cuccaroCarryOut_ket w false (z1 tgt) (fun i => !a i) b
    dsimp only at hact_c
    rw [hcarry_eq] at hact_c
    refine act_mapWires_ket (cuccaroCarryOut w) (ltCarryEmb w) z1 _ (by rw [hz1_comp]; exact hact_c) z2 ?_ ?_
    · funext u
      dsimp only [Function.comp_apply]
      by_cases ht : u.1 = 1 + 2 * w
      · have he : ltCarryEmb w u = tgt := Fin.ext (by dsimp [tgt]; simp [ht])
        have hu_eq : u = ⟨1 + 2 * w, by omega⟩ := Fin.ext ht
        rw [he, hu_eq]; dsimp only [z2]; rw [Function.update_self, Function.update_self]
      · have hne1 : ltCarryEmb w u ≠ tgt := Fin.ne_of_val_ne (by
          dsimp [tgt]
          by_cases h0 : u.1 = 0
          · simp [h0]
          · by_cases hm : (u.1 - 1) % 2 = 0 <;> simp [h0, ht, hm] <;> omega)
        have hne2 : u ≠ ⟨1 + 2 * w, by omega⟩ := Fin.ne_of_val_ne ht
        dsimp only [z2]; rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
        exact congrFun hz1_comp u
    · intro u hu
      have hne : u ≠ tgt := fun heq => hu ⟨⟨1 + 2 * w, by omega⟩, Fin.ext (by
        simp [heq, tgt])⟩
      dsimp only [z2]; rw [Function.update_of_ne hne]
  have hflip2 : act flipA.unitary (ket z2) = ket (padZero (w + w + 1) 1 (ltRegFn w x)) := by
    refine act_mapWires_ket (flipRegCircuit w w le_rfl) (ltFlipEmb w) z2 _
      (act_flipRegCircuit_ket w w le_rfl _) (padZero (w + w + 1) 1 (ltRegFn w x)) ?_ ?_
    · funext i
      have hne_t : ltFlipEmb w i ≠ tgt := Fin.ne_of_val_ne (by rw [ltFlipEmb_val]; dsimp [tgt]; omega)
      have hne_x : (⟨i.1, by omega⟩ : Fin (w + w + 1)) ≠ ⟨w + w, by omega⟩ :=
        Fin.ne_of_val_ne (by simp; omega)
      simp only [Function.comp_apply, i.isLt, ↓reduceIte]
      dsimp only [z2]; rw [Function.update_of_ne hne_t]
      dsimp only [z1, z0]; rw [if_pos (by simp [i.isLt]), Bool.not_not,
        padZero_val_lt x _ (by simp; omega), padZero_val_lt _ _ (by simp; omega), ltRegFn]
      have hfl : (⟨(ltFlipEmb w i).1, by simp; omega⟩ : Fin (w + w + 1)) = ⟨i.1, by omega⟩ := Fin.ext rfl
      rw [hfl, Function.update_of_ne hne_x]
    · intro u hu
      have hge : w ≤ u.1 := by
        by_contra hlt; exact hu ⟨⟨u.1, by omega⟩, Fin.ext rfl⟩
      by_cases huw : u = tgt
      · subst huw
        dsimp only [z2]; rw [Function.update_self]
        dsimp only [z1, z0]; rw [if_neg (by dsimp [tgt]; omega),
          padZero_val_lt x tgt (by dsimp [tgt]; omega),
          padZero_val_lt _ tgt (by dsimp [tgt]; omega),
          ltRegFn, Function.update_self]
      · dsimp only [z2]; rw [Function.update_of_ne huw]
        dsimp only [z1, z0]; rw [if_neg (by omega : ¬ u.1 < w)]
        by_cases hlt_main : u.1 < w + w + 1
        · have hne_x : (⟨u.1, hlt_main⟩ : Fin (w + w + 1)) ≠ ⟨w + w, by omega⟩ :=
            Fin.ne_of_val_ne (fun h => huw (Fin.ext h))
          rw [padZero_val_lt x u hlt_main, padZero_val_lt _ u hlt_main,
            ltRegFn, Function.update_of_ne hne_x]
        · rw [padZero_val_ge x u (by omega), padZero_val_ge _ u (by omega)]
  dsimp only [ltRegCircuit]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  change act flipA.unitary (act carry.unitary (act flipA.unitary (ket z0))) = _
  rw [hflip1, hcarry, hflip2]

/-! ### Part 5: Sub-register Combinators, Controlled Arithmetic & Bit-Reversal -/


private noncomputable def ctrlCopyPrefixCircuit (w : ℕ) :
    (k : ℕ) → k ≤ w → LayeredCircuit (1 + w + w)
  | 0, _ => LayeredCircuit.id (1 + w + w)
  | k + 1, hk =>
    let prev := ctrlCopyPrefixCircuit w k (by omega)
    let c : Fin (1 + w + w) := ⟨0, by omega⟩
    let a : Fin (1 + w + w) := ⟨1 + k, by omega⟩
    let b : Fin (1 + w + w) := ⟨1 + w + k, by omega⟩
    have hca : c ≠ a := Fin.ne_of_val_ne (by dsimp [c, a]; omega)
    have hcb : c ≠ b := Fin.ne_of_val_ne (by dsimp [c, b]; omega)
    have hab : a ≠ b := Fin.ne_of_val_ne (by dsimp [a, b]; omega)
    prev.seq (toffoliOn c a b hca hcb hab)

private lemma ctrlCopyPrefixCircuit_size (w k : ℕ) (hk : k ≤ w) :
    (ctrlCopyPrefixCircuit w k hk).size = 5 * k := by
  induction k with
  | zero => simp [ctrlCopyPrefixCircuit]
  | succ k ih =>
    dsimp only [ctrlCopyPrefixCircuit]
    rw [LayeredCircuit.seq_size, ih (by omega), toffoliOn_size]
    omega

private lemma act_ctrlCopyPrefixCircuit_ket (w k : ℕ) (hk : k ≤ w) (z : Qubits (1 + w + w)) :
    act (ctrlCopyPrefixCircuit w k hk).unitary (ket z) =
      ket (fun u =>
        if z ⟨0, by omega⟩ then
          if h2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k then
            xor (z u) (z ⟨u.1 - w, by omega⟩)
          else z u
        else z u) := by
  induction k with
  | zero =>
    simp only [ctrlCopyPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    cases z ⟨0, by omega⟩
    · rfl
    · simp only [↓reduceIte]; rw [dif_neg (by omega)]
  | succ k ih =>
    dsimp only [ctrlCopyPrefixCircuit]
    rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega), act_toffoliOn_ket]
    congr 1; funext u
    let c : Fin (1 + w + w) := ⟨0, by omega⟩
    let a : Fin (1 + w + w) := ⟨1 + k, by omega⟩
    let b : Fin (1 + w + w) := ⟨1 + w + k, by omega⟩
    have hc_v : c.1 = 0 := rfl
    have ha_v : a.1 = 1 + k := rfl
    have hb_v : b.1 = 1 + w + k := rfl
    by_cases hz0 : z ⟨0, by omega⟩ = true
    · have hzc_out : (if z ⟨0, by omega⟩ = true then
          if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then xor (z c) (z ⟨c.1 - w, by omega⟩) else z c
        else z c) = true := by
        rw [if_pos hz0, dif_neg (by omega)]; exact hz0
      have hza_out : (if z ⟨0, by omega⟩ = true then
          if h2 : 1 + w ≤ a.1 ∧ a.1 < 1 + w + k then xor (z a) (z ⟨a.1 - w, by omega⟩) else z a
        else z a) = z a := by
        rw [if_pos hz0, dif_neg (by omega)]
      have hz0' : z ⟨0, by omega⟩ = true := hz0
      rw [hzc_out, hza_out, if_pos hz0]
      by_cases hub : u = b
      · subst hub
        have hb_n : ¬ (1 + w ≤ b.1 ∧ b.1 < 1 + w + k) := by dsimp only [b]; omega
        have hb_new : 1 + w ≤ b.1 ∧ b.1 < 1 + w + (k + 1) := by dsimp only [b]; omega
        rw [Function.update_self, dif_neg hb_n, dif_pos hb_new]
        have hsub : (⟨b.1 - w, by omega⟩ : Fin (1 + w + w)) = a := Fin.ext (by dsimp only [a, b]; omega)
        rw [hsub]
        rw [if_pos hz0']
        rfl
      · rw [Function.update_of_ne hub]
        by_cases h2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k
        · rw [dif_pos h2, dif_pos (by omega)]
        · have h2' : ¬ (1 + w ≤ u.1 ∧ u.1 < 1 + w + (k + 1)) := by
            intro h; apply hub; apply Fin.ext; omega
          rw [dif_neg h2, dif_neg h2']
    · have hzc_out : (if z ⟨0, by omega⟩ = true then
          if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then xor (z c) (z ⟨c.1 - w, by omega⟩) else z c
        else z c) = false := by
        rw [if_neg hz0]
        cases hz_c : z ⟨0, by omega⟩
        · rfl
        · exact absurd hz_c hz0
      rw [hzc_out, Bool.false_and, Bool.xor_false, Function.update_eq_self, if_neg hz0, if_neg hz0]

/-- Controlled bitwise copy `(ctrl, a, b) ↦ (ctrl, a, if ctrl then b ^^^ a else b)` in `5 * w` gates. -/
noncomputable def ctrlCopyRegCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + 0) :=
  ctrlCopyPrefixCircuit w w le_rfl

lemma ctrlCopyRegCircuit_size (w : ℕ) : (ctrlCopyRegCircuit w).size = 5 * w :=
  ctrlCopyPrefixCircuit_size w w le_rfl


theorem ctrlCopyRegCircuit_implements (w : ℕ) :
    (ctrlCopyRegCircuit w).ImplementsOnClean (permMat (ctrlCopyRegFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [ctrlCopyRegCircuit]
  have h0 : padZero (1 + w + w) 0 x = x := by funext u; simp
  have h0' : padZero (1 + w + w) 0 (ctrlCopyRegFn w x) = ctrlCopyRegFn w x := by funext u; simp
  rw [h0, h0', act_ctrlCopyPrefixCircuit_ket]
  congr 1; funext u
  have hu := u.isLt
  by_cases hx : x ⟨0, by omega⟩ = true
  · dsimp only [ctrlCopyRegFn]; rw [if_pos hx, if_pos hx]
    by_cases h2 : 1 + w ≤ u.1
    · rw [dif_pos ⟨h2, hu⟩, dif_pos h2]
    · rw [dif_neg (by omega), dif_neg h2]
  · dsimp only [ctrlCopyRegFn]; rw [if_neg hx, if_neg hx]

private def cAddCopyEmb (w : ℕ) : Fin (1 + w + w) ↪ Fin ((1 + w + w) + (w + 1)) where
  toFun u :=
    if u.1 < 1 + w then ⟨u.1, by omega⟩ else ⟨u.1 + w, by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

@[simp] private lemma cAddCopyEmb_val (w : ℕ) (u : Fin (1 + w + w)) :
    (cAddCopyEmb w u).1 = if u.1 < 1 + w then u.1 else u.1 + w := by
  change (if u.1 < 1 + w then (⟨u.1, _⟩ : Fin ((1 + w + w) + (w + 1))) else ⟨u.1 + w, _⟩).1 = _
  split_ifs <;> rfl

@[simp] private lemma castAdd0_cAddCopyEmb_val (w : ℕ) (u : Fin (1 + w + w)) :
    (((Fin.castAddEmb 0).trans (cAddCopyEmb w)) u).1 = if u.1 < 1 + w then u.1 else u.1 + w := by
  change (cAddCopyEmb w (Fin.castAdd 0 u)).1 = _
  rw [cAddCopyEmb_val]; rfl

private def cAddCoreMainEmb (w : ℕ) : Fin (w + w) ↪ Fin ((1 + w + w) + (w + 1)) where
  toFun u := if h : u.1 < w then ⟨1 + w + w + u.1, by omega⟩ else ⟨1 + u.1, by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

@[simp] private lemma cAddCoreMainEmb_val (w : ℕ) (u : Fin (w + w)) :
    (cAddCoreMainEmb w u).1 = if u.1 < w then 1 + w + w + u.1 else 1 + u.1 := by
  change (if h : u.1 < w then (⟨1 + w + w + u.1, _⟩ : Fin ((1 + w + w) + (w + 1)))
    else ⟨1 + u.1, _⟩).1 = _
  split_ifs <;> rfl

private def cAddCoreAncEmb (w : ℕ) : Fin 1 ↪ Fin ((1 + w + w) + (w + 1)) where
  toFun _ := ⟨1 + w + w + w, by omega⟩
  inj' a b _ := Subsingleton.elim a b

private lemma cAddCoreAncEmb_val (w : ℕ) (j : Fin 1) :
    (cAddCoreAncEmb w j).1 = 1 + w + w + w := rfl

private lemma cAddCoreDisj (w : ℕ) (i : Fin (w + w)) (j : Fin 1) :
    cAddCoreMainEmb w i ≠ cAddCoreAncEmb w j := by
  apply Fin.ne_of_val_ne
  rw [cAddCoreMainEmb_val, cAddCoreAncEmb_val]
  split_ifs <;> have := i.isLt <;> omega

/-- Controlled in-place `w`-bit adder `(ctrl, a, b) ↦ (ctrl, a, if ctrl then (a+b) mod 2^w else b)` in `24 * w` gates (`w + 1` ancillas). -/
noncomputable def ctrlAddInPlaceCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + (w + 1)) :=
  let cpy := (ctrlCopyRegCircuit w).mapWires (cAddCopyEmb w)
  let addC := (addInPlaceCircuit w).mapWires (combineEmb (cAddCoreMainEmb w) (cAddCoreAncEmb w) (cAddCoreDisj w))
  cpy.seq (addC.seq cpy)

lemma ctrlAddInPlaceCircuit_size (w : ℕ) : (ctrlAddInPlaceCircuit w).size = 24 * w := by
  dsimp only [ctrlAddInPlaceCircuit]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size, ctrlCopyRegCircuit_size,
    addInPlaceCircuit_size]
  omega

def ctrlAddInPlaceFn (w : ℕ) (x : Qubits (1 + w + w)) : Qubits (1 + w + w) :=
  let a : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨1 + w + i.1, by omega⟩
  let s := natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)
  fun u =>
    if x ⟨0, by omega⟩ then
      if h : 1 + w ≤ u.1 then s ⟨u.1 - (1 + w), by omega⟩ else x u
    else x u

def ctrlSubInPlaceFn (w : ℕ) (x : Qubits (1 + w + w)) : Qubits (1 + w + w) :=
  let a : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨1 + w + i.1, by omega⟩
  let d := natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a)
  fun u =>
    if x ⟨0, by omega⟩ then
      if h : 1 + w ≤ u.1 then d ⟨u.1 - (1 + w), by omega⟩ else x u
    else x u

theorem ctrlAddInPlaceCircuit_implements (w : ℕ) :
    (ctrlAddInPlaceCircuit w).ImplementsOnClean (permMat (ctrlAddInPlaceFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (1 + w + w) (w + 1) x
  let a : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨1 + w + i.1, by omega⟩
  let cpy := (ctrlCopyRegCircuit w).mapWires (cAddCopyEmb w)
  let addC := (addInPlaceCircuit w).mapWires
    (combineEmb (cAddCoreMainEmb w) (cAddCoreAncEmb w) (cAddCoreDisj w))
  let z1 : Qubits ((1 + w + w) + (w + 1)) := fun u =>
    if h : 1 + w + w ≤ u.1 ∧ u.1 < 1 + w + w + w then
      if x ⟨0, by omega⟩ then a ⟨u.1 - (1 + w + w), by omega⟩ else false
    else z0 u
  have h1 : act cpy.unitary (ket z0) = ket z1 := by
    have hact := act_mapWires_perm (ctrlCopyRegCircuit w) (ctrlCopyRegFn w)
      (ctrlCopyRegCircuit_implements w) (cAddCopyEmb w) z0 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hu : u.1 < 1 + w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨u.1, by change u.1 < 1 + w + w; omega⟩ :=
        Fin.ext (by rw [castAdd0_cAddCopyEmb_val, if_pos (by dsimp only; exact hu)])
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [ctrlCopyRegFn, Function.comp_apply]
      have hz0c : z0 (((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩) = x ⟨0, by omega⟩ := by
        dsimp only [z0]
        have h0v : (((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩).1 = 0 := by
          rw [castAdd0_cAddCopyEmb_val]; simp
        rw [padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext h0v)
      simp only [hz0c]
      have hnot : ¬ (1 + w ≤ (⟨u.1, by change u.1 < 1 + w + w; omega⟩ : Fin ((1 + w + w) + 0)).1) := by dsimp only; omega
      by_cases hx : x ⟨0, by omega⟩ = true
      · rw [if_pos hx, dif_neg hnot, ← hu_eq]; dsimp only [z1]; rw [dif_neg (by omega)]
      · rw [if_neg hx, ← hu_eq]; dsimp only [z1]; rw [dif_neg (by omega)]
    · by_cases hS : 1 + w + w ≤ u.1 ∧ u.1 < 1 + w + w + w
      · have hu_eq : u = ((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨u.1 - w, by change u.1 - w < 1 + w + w; omega⟩ :=
          Fin.ext (by rw [castAdd0_cAddCopyEmb_val, if_neg (by dsimp only; omega)]; dsimp only; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [ctrlCopyRegFn, Function.comp_apply]
        have hz0c : z0 (((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩) =
            x ⟨0, by omega⟩ := by
          dsimp only [z0]
          have h0v : (((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩).1 = 0 := by
            rw [castAdd0_cAddCopyEmb_val]; simp
          rw [padZero_val_lt x _ (by omega)]
          exact congrArg x (Fin.ext h0v)
        simp only [hz0c]
        have h1w : 1 + w ≤ (⟨u.1 - w, by change u.1 - w < 1 + w + w; omega⟩ : Fin ((1 + w + w) + 0)).1 := by dsimp only; omega
        have hzu : z0 u = false := padZero_val_ge x u hS.1
        have he_sub : ((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨u.1 - w - w, by change u.1 - w - w < 1 + w + w; omega⟩ =
            ⟨1 + (u.1 - (1 + w + w)), by omega⟩ := Fin.ext (by
          rw [castAdd0_cAddCopyEmb_val, if_pos (by dsimp only; omega)]; dsimp only; omega)
        dsimp only [z1]; conv_rhs => rw [← hu_eq, dif_pos hS]
        cases hx0 : x ⟨0, by omega⟩
        · rw [if_neg (by decide), if_neg (by decide), ← hu_eq, hzu]
        · rw [if_pos rfl, if_pos rfl, dif_pos h1w, ← hu_eq, hzu, Bool.false_xor, he_sub]
          dsimp only [z0]; rw [padZero_val_lt x _ (by dsimp only; omega)]
      · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (cAddCopyEmb w)) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj
          rw [castAdd0_cAddCopyEmb_val] at hv
          have hjlt : j.1 < 1 + w + w := Nat.lt_of_lt_of_eq j.isLt (Nat.add_zero _)
          split_ifs at hv <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        dsimp only [z1]; rw [dif_neg hS]
  have hclean_z1 : ∀ j : Fin 1, z1 (cAddCoreAncEmb w j) = false := fun j => by
    have hjv : (cAddCoreAncEmb w j).1 = 1 + w + w + w := cAddCoreAncEmb_val w j
    dsimp only [z1]
    rw [dif_neg (by omega)]
    exact padZero_val_ge x _ (by omega)
  let z2 : Qubits ((1 + w + w) + (w + 1)) := fun u =>
    if h : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w then
      if x ⟨0, by omega⟩ then natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b) ⟨u.1 - (1 + w), by omega⟩
      else b ⟨u.1 - (1 + w), by omega⟩
    else z1 u
  have h2 : act addC.unitary (ket z1) = ket z2 := by
    have hact := act_subReg_perm (addInPlaceCircuit w) (addInPlaceFn w) (addInPlaceCircuit_implements w)
      (cAddCoreMainEmb w) (cAddCoreAncEmb w) (cAddCoreDisj w) z1 hclean_z1
    rw [hact]; congr 1; funext u
    have hcomp_s : (fun i : Fin w => (z1 ∘ cAddCoreMainEmb w) ⟨i.1, by omega⟩) =
        (if x ⟨0, by omega⟩ then a else fun _ => false) := by
      funext i
      dsimp only [Function.comp_apply, z1]
      have hv : (cAddCoreMainEmb w ⟨i.1, by omega⟩).1 = 1 + w + w + i.1 := by
        simp [cAddCoreMainEmb_val, i.isLt]
      rw [dif_pos (by omega)]
      cases x ⟨0, by omega⟩
      · simp
      · simp only [↓reduceIte]; exact congrArg a (Fin.ext (by dsimp only; omega))
    have hcomp_b : (fun i : Fin w => (z1 ∘ cAddCoreMainEmb w) ⟨w + i.1, by omega⟩) = b := by
      funext i
      dsimp only [Function.comp_apply, z1]
      have hv : (cAddCoreMainEmb w ⟨w + i.1, by omega⟩).1 = 1 + w + i.1 := by
        simp [cAddCoreMainEmb_val, show ¬ w + i.1 < w by omega]; omega
      rw [dif_neg (by omega)]
      dsimp only [z0]; rw [padZero_val_lt x _ (by omega)]
      exact congrArg x (Fin.ext (by dsimp only [b]; omega))
    by_cases hb : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w
    · have hu_eq : u = cAddCoreMainEmb w ⟨w + (u.1 - (1 + w)), by omega⟩ := Fin.ext (by
        simp [cAddCoreMainEmb_val, show ¬ w + (u.1 - (1 + w)) < w by omega]; omega)
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [addInPlaceFn]
      rw [dif_neg (by omega), hcomp_s, hcomp_b]
      dsimp only [z2]; rw [← hu_eq, dif_pos hb]
      cases hx : x ⟨0, by omega⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [bitsToNatLSB_all_false, zero_add, natToBitsLSB_bitsToNatLSB]
        exact congrArg b (Fin.ext (by dsimp only; omega))
      · simp only [↓reduceIte]
        exact congrArg (natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)) (Fin.ext (by dsimp only; omega))
    · by_cases hS : 1 + w + w ≤ u.1 ∧ u.1 < 1 + w + w + w
      · have hu_eq : u = cAddCoreMainEmb w ⟨u.1 - (1 + w + w), by omega⟩ := Fin.ext (by
          simp [cAddCoreMainEmb_val, show u.1 - (1 + w + w) < w by omega]; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [addInPlaceFn]
        rw [dif_pos (by omega)]
        dsimp only [Function.comp_apply, z2]; rw [← hu_eq, dif_neg hb]
      · have hnot : u ∉ Set.range (cAddCoreMainEmb w) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj
          rw [cAddCoreMainEmb_val] at hv
          split_ifs at hv <;> have := j.isLt <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        dsimp only [z2]; rw [dif_neg hb]
  have h3 : act cpy.unitary (ket z2) = ket (padZero (1 + w + w) (w + 1) (ctrlAddInPlaceFn w x)) := by
    have hact := act_mapWires_perm (ctrlCopyRegCircuit w) (ctrlCopyRegFn w)
      (ctrlCopyRegCircuit_implements w) (cAddCopyEmb w) z2 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hu : u.1 < 1 + w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨u.1, by change u.1 < 1 + w + w; omega⟩ :=
        Fin.ext (by rw [castAdd0_cAddCopyEmb_val, if_pos (by dsimp only; exact hu)])
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [ctrlCopyRegFn, Function.comp_apply]
      have hz2c : z2 (((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩) = x ⟨0, by omega⟩ := by
        dsimp only [z2, z1, z0]
        have h0v : (((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩).1 = 0 := by
          rw [castAdd0_cAddCopyEmb_val]; simp
        rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext h0v)
      simp only [hz2c]
      have hnot : ¬ (1 + w ≤ (⟨u.1, by change u.1 < 1 + w + w; omega⟩ : Fin ((1 + w + w) + 0)).1) := by dsimp only; omega
      have h1w : u.1 < 1 + w + w := by omega
      conv_rhs => rw [← hu_eq, padZero_val_lt _ u h1w]
      dsimp only [ctrlAddInPlaceFn]
      have h1w' : ¬ (1 + w ≤ u.1) := by omega
      by_cases hx : x ⟨0, by omega⟩ = true
      · rw [if_pos hx, dif_neg hnot, ← hu_eq, if_pos hx, dif_neg h1w']
        dsimp only [z2, z1, z0]; rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
      · rw [if_neg hx, ← hu_eq, if_neg hx]
        dsimp only [z2, z1, z0]; rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
    · by_cases hS : 1 + w + w ≤ u.1 ∧ u.1 < 1 + w + w + w
      · have hu_eq : u = ((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨u.1 - w, by change u.1 - w < 1 + w + w; omega⟩ :=
          Fin.ext (by rw [castAdd0_cAddCopyEmb_val, if_neg (by dsimp only; omega)]; dsimp only; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [ctrlCopyRegFn, Function.comp_apply]
        have hz2c : z2 (((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩) = x ⟨0, by omega⟩ := by
          dsimp only [z2, z1, z0]
          have h0v : (((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩).1 = 0 := by
            rw [castAdd0_cAddCopyEmb_val]; simp
          rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
          exact congrArg x (Fin.ext h0v)
        simp only [hz2c]
        have h1w : 1 + w ≤ (⟨u.1 - w, by change u.1 - w < 1 + w + w; omega⟩ : Fin ((1 + w + w) + 0)).1 := by dsimp only; omega
        have he_S : z2 u = if x ⟨0, by omega⟩ then a ⟨u.1 - (1 + w + w), by omega⟩ else false := by
          dsimp only [z2, z1]; rw [dif_neg (by omega), dif_pos hS]
        have he_sub : ((Fin.castAddEmb 0).trans (cAddCopyEmb w)) ⟨u.1 - w - w, by change u.1 - w - w < 1 + w + w; omega⟩ =
            ⟨1 + (u.1 - (1 + w + w)), by omega⟩ := Fin.ext (by
          rw [castAdd0_cAddCopyEmb_val, if_pos (by dsimp only; omega)]; dsimp only; omega)
        have he_a : z2 ⟨1 + (u.1 - (1 + w + w)), by omega⟩ = a ⟨u.1 - (1 + w + w), by omega⟩ := by
          dsimp only [z2, z1, z0]
          rw [dif_neg (by omega), dif_neg (by omega),
            padZero_val_lt x _ (by dsimp only; omega)]
        conv_rhs => rw [← hu_eq, padZero_val_ge _ u hS.1]
        by_cases hx : x ⟨0, by omega⟩ = true
        · rw [if_pos hx, dif_pos h1w, ← hu_eq, he_S, if_pos hx, he_sub, he_a, Bool.xor_self]
        · rw [if_neg hx, ← hu_eq, he_S, if_neg hx]
      · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (cAddCopyEmb w)) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj
          rw [castAdd0_cAddCopyEmb_val] at hv
          have hjlt : j.1 < 1 + w + w := Nat.lt_of_lt_of_eq j.isLt (Nat.add_zero _)
          split_ifs at hv <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        by_cases hb : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w
        · rw [padZero_val_lt _ u hb.2]; dsimp only [ctrlAddInPlaceFn, z2]; rw [dif_pos hb, dif_pos hb.1]
          cases hx : x ⟨0, by omega⟩
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact congrArg x (Fin.ext (by dsimp only [b]; omega))
          · rfl
        · have hanc : u.1 = 1 + w + w + w := by have := u.isLt; omega
          rw [padZero_val_ge _ u (by omega)]
          dsimp only [z2, z1, z0]; rw [dif_neg hb, dif_neg hS, padZero_val_ge x u (by omega)]
  dsimp only [ctrlAddInPlaceCircuit]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  change act cpy.unitary (act addC.unitary (act cpy.unitary (ket z0))) = _
  rw [h1, h2, h3]

lemma ctrlAddInPlaceFn_ctrlSubInPlaceFn (w : ℕ) (x : Qubits (1 + w + w)) :
    ctrlAddInPlaceFn w (ctrlSubInPlaceFn w x) = x ∧
      ctrlSubInPlaceFn w (ctrlAddInPlaceFn w x) = x := by
  by_cases hx : x ⟨0, by omega⟩ = true
  · let x' : Qubits (w + w) := fun i => x ⟨1 + i.1, by omega⟩
    have hinv := addInPlaceFn_subInPlaceFn w x'
    have hsub_ctrl : ctrlSubInPlaceFn w x ⟨0, by omega⟩ = true := by
      dsimp only [ctrlSubInPlaceFn]; rw [if_pos hx, dif_neg (by omega)]; exact hx
    have hadd_ctrl : ctrlAddInPlaceFn w x ⟨0, by omega⟩ = true := by
      dsimp only [ctrlAddInPlaceFn]; rw [if_pos hx, dif_neg (by omega)]; exact hx
    have ha_s : (fun i : Fin w => ctrlSubInPlaceFn w x ⟨1 + i.1, by omega⟩) =
        fun i : Fin w => subInPlaceFn w x' ⟨i.1, by omega⟩ := by
      funext i; dsimp only [ctrlSubInPlaceFn, subInPlaceFn, x']
      rw [if_pos hx, dif_neg (by omega), dif_pos i.isLt]
    have hb_s : (fun i : Fin w => ctrlSubInPlaceFn w x ⟨1 + w + i.1, by omega⟩) =
        fun i : Fin w => subInPlaceFn w x' ⟨w + i.1, by omega⟩ := by
      funext i; dsimp only [ctrlSubInPlaceFn, subInPlaceFn, x']
      rw [if_pos hx, dif_pos (by omega), dif_neg (by omega)]
      congr 1
      · congr 2; congr 1; funext j; exact congrArg x (Fin.ext (by dsimp only; omega))
      · exact Fin.ext (by dsimp only; omega)
    have ha_a : (fun i : Fin w => ctrlAddInPlaceFn w x ⟨1 + i.1, by omega⟩) =
        fun i : Fin w => addInPlaceFn w x' ⟨i.1, by omega⟩ := by
      funext i; dsimp only [ctrlAddInPlaceFn, addInPlaceFn, x']
      rw [if_pos hx, dif_neg (by omega), dif_pos i.isLt]
    have hb_a : (fun i : Fin w => ctrlAddInPlaceFn w x ⟨1 + w + i.1, by omega⟩) =
        fun i : Fin w => addInPlaceFn w x' ⟨w + i.1, by omega⟩ := by
      funext i; dsimp only [ctrlAddInPlaceFn, addInPlaceFn, x']
      rw [if_pos hx, dif_pos (by omega), dif_neg (by omega)]
      congr 1
      · congr 2; funext j; exact congrArg x (Fin.ext (by dsimp only; omega))
      · exact Fin.ext (by dsimp only; omega)
    constructor
    · funext u
      by_cases hu0 : u.1 = 0
      · have hu_eq : u = ⟨0, by omega⟩ := Fin.ext hu0
        rw [hu_eq]; dsimp only [ctrlAddInPlaceFn]; rw [if_pos hsub_ctrl, dif_neg (by omega), hsub_ctrl, hx]
      · by_cases h1w : 1 + w ≤ u.1
        · have hu_lt : u.1 - (1 + w) < w := by have := u.isLt; omega
          have h1 := congrFun hinv.1 ⟨w + (u.1 - (1 + w)), by omega⟩
          dsimp only [ctrlAddInPlaceFn]; rw [if_pos hsub_ctrl, dif_pos h1w]
          have hadd_rw : natToBitsLSB w
              (bitsToNatLSB (fun i : Fin w => ctrlSubInPlaceFn w x ⟨1 + i.1, by omega⟩) +
                bitsToNatLSB (fun i : Fin w => ctrlSubInPlaceFn w x ⟨1 + w + i.1, by omega⟩))
              ⟨u.1 - (1 + w), hu_lt⟩ =
              addInPlaceFn w (subInPlaceFn w x') ⟨w + (u.1 - (1 + w)), by omega⟩ := by
            rw [ha_s, hb_s]
            dsimp only [addInPlaceFn]
            rw [dif_neg (by omega)]
            exact congrArg _ (Fin.ext (by dsimp only; omega))
          rw [hadd_rw, h1]; exact congrArg x (Fin.ext (by dsimp only [x']; omega))
        · dsimp only [ctrlAddInPlaceFn]; rw [if_pos hsub_ctrl, dif_neg h1w]
          have hu_eq : (⟨1 + (u.1 - 1), by omega⟩ : Fin (1 + w + w)) = u :=
            Fin.ext (by dsimp only; omega)
          rw [← hu_eq]
          refine (congrFun ha_s ⟨u.1 - 1, by omega⟩).trans ?_
          dsimp only [subInPlaceFn, x']; rw [dif_pos (by omega)]
    · funext u
      by_cases hu0 : u.1 = 0
      · have hu_eq : u = ⟨0, by omega⟩ := Fin.ext hu0
        rw [hu_eq]; dsimp only [ctrlSubInPlaceFn]; rw [if_pos hadd_ctrl, dif_neg (by omega), hadd_ctrl, hx]
      · by_cases h1w : 1 + w ≤ u.1
        · have hu_lt : u.1 - (1 + w) < w := by have := u.isLt; omega
          have h2 := congrFun hinv.2 ⟨w + (u.1 - (1 + w)), by omega⟩
          dsimp only [ctrlSubInPlaceFn]; rw [if_pos hadd_ctrl, dif_pos h1w]
          have hsub_rw : natToBitsLSB w
              (2 ^ w + bitsToNatLSB (fun i : Fin w => ctrlAddInPlaceFn w x ⟨1 + w + i.1, by omega⟩) -
                bitsToNatLSB (fun i : Fin w => ctrlAddInPlaceFn w x ⟨1 + i.1, by omega⟩))
              ⟨u.1 - (1 + w), hu_lt⟩ =
              subInPlaceFn w (addInPlaceFn w x') ⟨w + (u.1 - (1 + w)), by omega⟩ := by
            rw [ha_a, hb_a]
            dsimp only [subInPlaceFn]
            rw [dif_neg (by omega)]
            exact congrArg _ (Fin.ext (by dsimp only; omega))
          rw [hsub_rw, h2]; exact congrArg x (Fin.ext (by dsimp only [x']; omega))
        · dsimp only [ctrlSubInPlaceFn]; rw [if_pos hadd_ctrl, dif_neg h1w]
          have hu_eq : (⟨1 + (u.1 - 1), by omega⟩ : Fin (1 + w + w)) = u :=
            Fin.ext (by dsimp only; omega)
          rw [← hu_eq]
          refine (congrFun ha_a ⟨u.1 - 1, by omega⟩).trans ?_
          dsimp only [addInPlaceFn, x']; rw [dif_pos (by omega)]
  · have hsub_eq : ctrlSubInPlaceFn w x = x := by funext u; dsimp only [ctrlSubInPlaceFn]; rw [if_neg hx]
    have hadd_eq : ctrlAddInPlaceFn w x = x := by funext u; dsimp only [ctrlAddInPlaceFn]; rw [if_neg hx]
    simp only [hsub_eq, hadd_eq, and_self]

/-- Controlled in-place `w`-bit subtractor `(ctrl, a, b) ↦ (ctrl, a, if ctrl then (2^w + b - a) mod 2^w else b)` in `24 * w` gates (`w + 1` ancillas). -/
noncomputable def ctrlSubInPlaceCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + (w + 1)) :=
  (ctrlAddInPlaceCircuit w).adj

lemma ctrlSubInPlaceCircuit_size (w : ℕ) : (ctrlSubInPlaceCircuit w).size = 24 * w := by
  simp [ctrlSubInPlaceCircuit, ctrlAddInPlaceCircuit_size]

theorem ctrlSubInPlaceCircuit_implements (w : ℕ) :
    (ctrlSubInPlaceCircuit w).ImplementsOnClean (permMat (ctrlSubInPlaceFn w)) :=
  adj_implementsOnClean_perm (ctrlAddInPlaceCircuit w)
    (fun x => (ctrlAddInPlaceFn_ctrlSubInPlaceFn w x).2)
    (fun x => (ctrlAddInPlaceFn_ctrlSubInPlaceFn w x).1)
    (ctrlAddInPlaceCircuit_implements w)

private def cacXorEmb (w : ℕ) : Fin (1 + w) ↪ Fin ((1 + w) + (w + 1)) where
  toFun u := if u.1 = 0 then ⟨0, by omega⟩ else ⟨1 + w + (u.1 - 1), by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

@[simp] private lemma cacXorEmb_val (w : ℕ) (u : Fin (1 + w)) :
    (cacXorEmb w u).1 = if u.1 = 0 then 0 else 1 + w + (u.1 - 1) := by
  change (if u.1 = 0 then (⟨0, _⟩ : Fin ((1 + w) + (w + 1))) else ⟨1 + w + (u.1 - 1), _⟩).1 = _
  split_ifs <;> rfl

@[simp] private lemma castAdd0_cacXorEmb_val (w : ℕ) (u : Fin (1 + w)) :
    (((Fin.castAddEmb 0).trans (cacXorEmb w)) u).1 = if u.1 = 0 then 0 else 1 + w + (u.1 - 1) := by
  change (cacXorEmb w (Fin.castAdd 0 u)).1 = _
  rw [cacXorEmb_val]; rfl

private def cacAddMainEmb (w : ℕ) : Fin (w + w) ↪ Fin ((1 + w) + (w + 1)) where
  toFun u := if h : u.1 < w then ⟨1 + w + u.1, by omega⟩ else ⟨1 + (u.1 - w), by have := u.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val h; dsimp only at hv
    split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

@[simp] private lemma cacAddMainEmb_val (w : ℕ) (u : Fin (w + w)) :
    (cacAddMainEmb w u).1 = if u.1 < w then 1 + w + u.1 else 1 + (u.1 - w) := by
  change (if h : u.1 < w then (⟨1 + w + u.1, _⟩ : Fin ((1 + w) + (w + 1)))
    else ⟨1 + (u.1 - w), _⟩).1 = _
  split_ifs <;> rfl

private def cacAddAncEmb (w : ℕ) : Fin 1 ↪ Fin ((1 + w) + (w + 1)) where
  toFun _ := ⟨1 + w + w, by omega⟩
  inj' a b _ := Subsingleton.elim a b

private lemma cacAddAncEmb_val (w : ℕ) (j : Fin 1) :
    (cacAddAncEmb w j).1 = 1 + w + w := rfl

private lemma cacAddDisj (w : ℕ) (i : Fin (w + w)) (j : Fin 1) :
    cacAddMainEmb w i ≠ cacAddAncEmb w j := by
  apply Fin.ne_of_val_ne
  rw [cacAddMainEmb_val, cacAddAncEmb_val]
  split_ifs <;> have := i.isLt <;> omega

/-- Controlled in-place `+ c mod 2^w`: `(ctrl, b) ↦ (ctrl, if ctrl then (c % 2^w + b) mod 2^w else b)` in `≤ 16 * w` gates (`w + 1` ancillas). -/
noncomputable def ctrlAddConstInPlaceCircuit (w c : ℕ) : LayeredCircuit ((1 + w) + (w + 1)) :=
  let sc := (ctrlConstXorCircuit w c).mapWires (cacXorEmb w)
  let addC := (addInPlaceCircuit w).mapWires (combineEmb (cacAddMainEmb w) (cacAddAncEmb w) (cacAddDisj w))
  sc.seq (addC.seq sc)

lemma ctrlAddConstInPlaceCircuit_size (w c : ℕ) : (ctrlAddConstInPlaceCircuit w c).size ≤ 16 * w := by
  dsimp only [ctrlAddConstInPlaceCircuit]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size, addInPlaceCircuit_size]
  have h1 := ctrlConstXorCircuit_size w c
  omega

def ctrlAddConstInPlaceFn (w c : ℕ) (x : Qubits (1 + w)) : Qubits (1 + w) :=
  let b : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let s := natToBitsLSB w (c % 2 ^ w + bitsToNatLSB b)
  fun u => if x ⟨0, by omega⟩ then if h : 1 ≤ u.1 then s ⟨u.1 - 1, by omega⟩ else x u else x u

def ctrlSubConstInPlaceFn (w c : ℕ) (x : Qubits (1 + w)) : Qubits (1 + w) :=
  let b : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let d := natToBitsLSB w (2 ^ w + bitsToNatLSB b - c % 2 ^ w)
  fun u => if x ⟨0, by omega⟩ then if h : 1 ≤ u.1 then d ⟨u.1 - 1, by omega⟩ else x u else x u

theorem ctrlAddConstInPlaceCircuit_implements (w c : ℕ) :
    (ctrlAddConstInPlaceCircuit w c).ImplementsOnClean (permMat (ctrlAddConstInPlaceFn w c)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (1 + w) (w + 1) x
  let b : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let pat := natToBitsLSB w c
  have hpat_mod : pat = natToBitsLSB w (c % 2 ^ w) := by
    funext i; simp [pat, natToBitsLSB, Nat.testBit_mod_two_pow, i.isLt]
  let sc := (ctrlConstXorCircuit w c).mapWires (cacXorEmb w)
  let addC := (addInPlaceCircuit w).mapWires
    (combineEmb (cacAddMainEmb w) (cacAddAncEmb w) (cacAddDisj w))
  let z1 : Qubits ((1 + w) + (w + 1)) := fun u =>
    if h : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w then
      if x ⟨0, by omega⟩ then pat ⟨u.1 - (1 + w), by omega⟩ else false
    else z0 u
  have h1 : act sc.unitary (ket z0) = ket z1 := by
    have hact := act_mapWires_perm (ctrlConstXorCircuit w c) (ctrlConstXorFn w c)
      (ctrlConstXorCircuit_implements w c) (cacXorEmb w) z0 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hS : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨1 + (u.1 - (1 + w)), by change 1 + (u.1 - (1 + w)) < 1 + w; omega⟩ :=
        Fin.ext (by rw [castAdd0_cacXorEmb_val, if_neg (by dsimp only; omega)]; dsimp only; omega)
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [ctrlConstXorFn, Function.comp_apply]
      have hz0c : z0 (((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩) = x ⟨0, by omega⟩ := by
        dsimp only [z0]
        have h0v : (((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩).1 = 0 := by
          rw [castAdd0_cacXorEmb_val]; rfl
        rw [padZero_val_lt x _ (by omega)]; exact congrArg x (Fin.ext h0v)
      simp only [hz0c]
      have hzu : z0 u = false := padZero_val_ge x u hS.1
      dsimp only [z1]; conv_rhs => rw [← hu_eq, dif_pos hS]
      by_cases hx : x ⟨0, by omega⟩ = true
      · rw [if_pos hx, dif_pos (by omega), ← hu_eq, hzu, Bool.false_xor, if_pos hx]
        exact congrArg (natToBitsLSB w c) (Fin.ext (by dsimp only; omega))
      · rw [if_neg hx, ← hu_eq, hzu, if_neg hx]
    · by_cases hu0 : u.1 = 0
      · have hu_eq : u = ((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩ :=
          Fin.ext (by rw [castAdd0_cacXorEmb_val, if_pos rfl]; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [ctrlConstXorFn, Function.comp_apply]
        have hz0c : z0 (((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩) = x ⟨0, by omega⟩ := by
          dsimp only [z0]
          have h0v : (((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩).1 = 0 := by
            rw [castAdd0_cacXorEmb_val]; rfl
          rw [padZero_val_lt x _ (by omega)]; exact congrArg x (Fin.ext h0v)
        simp only [hz0c]
        dsimp only [z1]; conv_rhs => rw [← hu_eq, dif_neg hS]
        have hzx : z0 u = x ⟨0, by omega⟩ := by
          dsimp only [z0]; rw [padZero_val_lt x u (by omega)]; exact congrArg x (Fin.ext hu0)
        cases hx : x ⟨0, by omega⟩
        · rw [if_neg (by simp), hzx, hx]
        · rw [if_pos rfl, dif_neg (by omega), hzx, hx]
      · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (cacXorEmb w)) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; rw [castAdd0_cacXorEmb_val] at hv
          have hjlt : j.1 < 1 + w := Nat.lt_of_lt_of_eq j.isLt (Nat.add_zero _)
          split_ifs at hv <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        dsimp only [z1]; rw [dif_neg hS]
  have hclean_z1 : ∀ j : Fin 1, z1 (cacAddAncEmb w j) = false := fun j => by
    have hjv : (cacAddAncEmb w j).1 = 1 + w + w := cacAddAncEmb_val w j
    dsimp only [z1]; rw [dif_neg (by omega)]; exact padZero_val_ge x _ (by omega)
  let z2 : Qubits ((1 + w) + (w + 1)) := fun u =>
    if h : 1 ≤ u.1 ∧ u.1 < 1 + w then
      if x ⟨0, by omega⟩ then natToBitsLSB w (c % 2 ^ w + bitsToNatLSB b) ⟨u.1 - 1, by omega⟩
      else b ⟨u.1 - 1, by omega⟩
    else z1 u
  have h2 : act addC.unitary (ket z1) = ket z2 := by
    have hact := act_subReg_perm (addInPlaceCircuit w) (addInPlaceFn w) (addInPlaceCircuit_implements w)
      (cacAddMainEmb w) (cacAddAncEmb w) (cacAddDisj w) z1 hclean_z1
    rw [hact]; congr 1; funext u
    have hcomp_s : (fun i : Fin w => (z1 ∘ cacAddMainEmb w) ⟨i.1, by omega⟩) =
        (if x ⟨0, by omega⟩ then pat else fun _ => false) := by
      funext i; dsimp only [Function.comp_apply, z1]
      have hv : (cacAddMainEmb w ⟨i.1, by omega⟩).1 = 1 + w + i.1 := by simp [i.isLt]
      rw [dif_pos (by omega)]
      cases x ⟨0, by omega⟩
      · simp
      · simp only [↓reduceIte]; exact congrArg pat (Fin.ext (by dsimp only; omega))
    have hcomp_b : (fun i : Fin w => (z1 ∘ cacAddMainEmb w) ⟨w + i.1, by omega⟩) = b := by
      funext i; dsimp only [Function.comp_apply, z1]
      have hv : (cacAddMainEmb w ⟨w + i.1, by omega⟩).1 = 1 + i.1 := by
        simp [show ¬ w + i.1 < w by omega]
      rw [dif_neg (by omega)]
      dsimp only [z0]; rw [padZero_val_lt x _ (by omega)]
      exact congrArg x (Fin.ext (by dsimp only [b]; omega))
    by_cases hb : 1 ≤ u.1 ∧ u.1 < 1 + w
    · have hu_eq : u = cacAddMainEmb w ⟨w + (u.1 - 1), by omega⟩ := Fin.ext (by
        simp [show ¬ w + (u.1 - 1) < w by omega]; omega)
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [addInPlaceFn]
      rw [dif_neg (by omega), hcomp_s, hcomp_b]
      dsimp only [z2]; rw [← hu_eq, dif_pos hb]
      cases hx : x ⟨0, by omega⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [bitsToNatLSB_all_false, zero_add, natToBitsLSB_bitsToNatLSB]
        exact congrArg b (Fin.ext (by dsimp only; omega))
      · simp only [↓reduceIte]
        rw [hpat_mod, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
        exact congrArg (natToBitsLSB w (c % 2 ^ w + bitsToNatLSB b)) (Fin.ext (by dsimp only; omega))
    · by_cases hS : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w
      · have hu_eq : u = cacAddMainEmb w ⟨u.1 - (1 + w), by omega⟩ := Fin.ext (by
          simp [show u.1 - (1 + w) < w by omega]; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [addInPlaceFn]; rw [dif_pos (by omega)]
        dsimp only [Function.comp_apply, z2]; rw [← hu_eq, dif_neg hb]
      · have hnot : u ∉ Set.range (cacAddMainEmb w) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj
          rw [cacAddMainEmb_val] at hv
          split_ifs at hv <;> have := j.isLt <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        dsimp only [z2]; rw [dif_neg hb]
  have h3 : act sc.unitary (ket z2) = ket (padZero (1 + w) (w + 1) (ctrlAddConstInPlaceFn w c x)) := by
    have hact := act_mapWires_perm (ctrlConstXorCircuit w c) (ctrlConstXorFn w c)
      (ctrlConstXorCircuit_implements w c) (cacXorEmb w) z2 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hS : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨1 + (u.1 - (1 + w)), by change 1 + (u.1 - (1 + w)) < 1 + w; omega⟩ :=
        Fin.ext (by rw [castAdd0_cacXorEmb_val, if_neg (by dsimp only; omega)]; dsimp only; omega)
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [ctrlConstXorFn, Function.comp_apply]
      have hz2c : z2 (((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩) = x ⟨0, by omega⟩ := by
        dsimp only [z2, z1, z0]
        have h0v : (((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩).1 = 0 := by
          rw [castAdd0_cacXorEmb_val]; rfl
        rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext h0v)
      simp only [hz2c]; conv_rhs => rw [← hu_eq, padZero_val_ge _ u hS.1]
      have hzu : z2 u = if x ⟨0, by omega⟩ then pat ⟨u.1 - (1 + w), by omega⟩ else false := by
        dsimp only [z2, z1]; rw [dif_neg (by omega), dif_pos hS]
      by_cases hx : x ⟨0, by omega⟩ = true
      · rw [if_pos hx, dif_pos (by omega), ← hu_eq, hzu, if_pos hx]
        have heq_b : natToBitsLSB w c ⟨1 + (u.1 - (1 + w)) - 1, by omega⟩ = pat ⟨u.1 - (1 + w), by omega⟩ :=
          congrArg (natToBitsLSB w c) (Fin.ext (by dsimp only; omega))
        rw [heq_b, Bool.xor_self]
      · rw [if_neg hx, ← hu_eq, hzu, if_neg hx]
    · by_cases hu0 : u.1 = 0
      · have hu_eq : u = ((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩ :=
          Fin.ext (by rw [castAdd0_cacXorEmb_val, if_pos rfl]; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [ctrlConstXorFn, Function.comp_apply]
        have hz2c : z2 (((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩) = x ⟨0, by omega⟩ := by
          dsimp only [z2, z1, z0]
          have h0v : (((Fin.castAddEmb 0).trans (cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩).1 = 0 := by
            rw [castAdd0_cacXorEmb_val]; rfl
          rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
          exact congrArg x (Fin.ext h0v)
        simp only [hz2c]; conv_rhs => rw [← hu_eq, padZero_val_lt _ u (by omega)]
        have hx_rhs : ctrlAddConstInPlaceFn w c x ⟨u.1, by omega⟩ = x ⟨0, by omega⟩ := by
          dsimp only [ctrlAddConstInPlaceFn]
          by_cases hx : x ⟨0, by omega⟩ = true
          · rw [if_pos hx, dif_neg (by omega)]; exact congrArg x (Fin.ext hu0)
          · rw [if_neg hx]; exact congrArg x (Fin.ext hu0)
        by_cases hx : x ⟨0, by omega⟩ = true
        · rw [if_pos hx, dif_neg (by omega), hx_rhs, hx]
        · rw [if_neg hx, hx_rhs]
      · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (cacXorEmb w)) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; rw [castAdd0_cacXorEmb_val] at hv
          have hjlt : j.1 < 1 + w := Nat.lt_of_lt_of_eq j.isLt (Nat.add_zero _)
          split_ifs at hv <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        by_cases hb : 1 ≤ u.1 ∧ u.1 < 1 + w
        · rw [padZero_val_lt _ u hb.2]; dsimp only [ctrlAddConstInPlaceFn, z2]; rw [dif_pos hb, dif_pos hb.1]
          cases hx : x ⟨0, by omega⟩
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact congrArg x (Fin.ext (by dsimp only [b]; omega))
          · rfl
        · have hanc : u.1 = 1 + w + w := by have := u.isLt; omega
          rw [padZero_val_ge _ u (by omega)]
          dsimp only [z2, z1, z0]; rw [dif_neg hb, dif_neg hS, padZero_val_ge x u (by omega)]
  dsimp only [ctrlAddConstInPlaceCircuit]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  change act sc.unitary (act addC.unitary (act sc.unitary (ket z0))) = _
  rw [h1, h2, h3]

lemma ctrlAddConstInPlaceFn_ctrlSubConstInPlaceFn (w c : ℕ) (x : Qubits (1 + w)) :
    ctrlAddConstInPlaceFn w c (ctrlSubConstInPlaceFn w c x) = x ∧
      ctrlSubConstInPlaceFn w c (ctrlAddConstInPlaceFn w c x) = x := by
  by_cases hx : x ⟨0, by omega⟩ = true
  · let b : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
    have hcm : c % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    have hb_lt := bitsToNatLSB_lt w b
    have hntb_eq : ∀ u : ℕ, natToBitsLSB w (u % 2 ^ w) = natToBitsLSB w u := fun u => by
      funext i; simp [natToBitsLSB, Nat.testBit_mod_two_pow, i.isLt]
    have hsub_ctrl : ctrlSubConstInPlaceFn w c x ⟨0, by omega⟩ = true := by
      dsimp only [ctrlSubConstInPlaceFn]; rw [if_pos hx, dif_neg (by omega)]; exact hx
    have hadd_ctrl : ctrlAddConstInPlaceFn w c x ⟨0, by omega⟩ = true := by
      dsimp only [ctrlAddConstInPlaceFn]; rw [if_pos hx, dif_neg (by omega)]; exact hx
    have hb_s : (fun i : Fin w => ctrlSubConstInPlaceFn w c x ⟨1 + i.1, by omega⟩) =
        natToBitsLSB w (2 ^ w + bitsToNatLSB b - c % 2 ^ w) := by
      funext i; dsimp only [ctrlSubConstInPlaceFn]; rw [if_pos hx, dif_pos (by omega)]
      exact congrArg _ (Fin.ext (by dsimp only; omega))
    have hb_a : (fun i : Fin w => ctrlAddConstInPlaceFn w c x ⟨1 + i.1, by omega⟩) =
        natToBitsLSB w (c % 2 ^ w + bitsToNatLSB b) := by
      funext i; dsimp only [ctrlAddConstInPlaceFn]; rw [if_pos hx, dif_pos (by omega)]
      exact congrArg _ (Fin.ext (by dsimp only; omega))
    have hadd_m : ∀ u v : ℕ, (u + v % 2 ^ w) % 2 ^ w = (u + v) % 2 ^ w := fun u v => by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hmod1 : (c % 2 ^ w + (2 ^ w + bitsToNatLSB b - c % 2 ^ w) % 2 ^ w) % 2 ^ w = bitsToNatLSB b := by
      rw [hadd_m, show c % 2 ^ w + (2 ^ w + bitsToNatLSB b - c % 2 ^ w) = 2 ^ w + bitsToNatLSB b by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt hb_lt]
    have hmod2 : (2 ^ w + (c % 2 ^ w + bitsToNatLSB b) % 2 ^ w - c % 2 ^ w) % 2 ^ w = bitsToNatLSB b := by
      by_cases hsum : c % 2 ^ w + bitsToNatLSB b < 2 ^ w
      · rw [Nat.mod_eq_of_lt hsum, show 2 ^ w + (c % 2 ^ w + bitsToNatLSB b) - c % 2 ^ w =
          2 ^ w + bitsToNatLSB b by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hb_lt]
      · have hmeq : (c % 2 ^ w + bitsToNatLSB b) % 2 ^ w = c % 2 ^ w + bitsToNatLSB b - 2 ^ w := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hmeq, show 2 ^ w + (c % 2 ^ w + bitsToNatLSB b - 2 ^ w) - c % 2 ^ w = bitsToNatLSB b by omega,
          Nat.mod_eq_of_lt hb_lt]
    constructor
    · funext u; by_cases hu0 : u.1 = 0
      · have hu_eq : u = ⟨0, by omega⟩ := Fin.ext hu0
        rw [hu_eq]; dsimp only [ctrlAddConstInPlaceFn]; rw [if_pos hsub_ctrl, dif_neg (by omega), hsub_ctrl, hx]
      · dsimp only [ctrlAddConstInPlaceFn]; rw [if_pos hsub_ctrl, dif_pos (by omega), hb_s]
        have h1 : bitsToNatLSB (natToBitsLSB w (2 ^ w + bitsToNatLSB b - c % 2 ^ w)) =
            (2 ^ w + bitsToNatLSB b - c % 2 ^ w) % 2 ^ w := by
          rw [← hntb_eq, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
        rw [h1, ← hntb_eq, hmod1, natToBitsLSB_bitsToNatLSB]
        exact congrArg x (Fin.ext (by dsimp only [b]; omega))
    · funext u; by_cases hu0 : u.1 = 0
      · have hu_eq : u = ⟨0, by omega⟩ := Fin.ext hu0
        rw [hu_eq]; dsimp only [ctrlSubConstInPlaceFn]; rw [if_pos hadd_ctrl, dif_neg (by omega), hadd_ctrl, hx]
      · dsimp only [ctrlSubConstInPlaceFn]; rw [if_pos hadd_ctrl, dif_pos (by omega), hb_a]
        have h1 : bitsToNatLSB (natToBitsLSB w (c % 2 ^ w + bitsToNatLSB b)) =
            (c % 2 ^ w + bitsToNatLSB b) % 2 ^ w := by
          rw [← hntb_eq, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
        rw [h1, ← hntb_eq, hmod2, natToBitsLSB_bitsToNatLSB]
        exact congrArg x (Fin.ext (by dsimp only [b]; omega))
  · have hsub_eq : ctrlSubConstInPlaceFn w c x = x := by
      funext u; dsimp only [ctrlSubConstInPlaceFn]; rw [if_neg hx]
    have hadd_eq : ctrlAddConstInPlaceFn w c x = x := by
      funext u; dsimp only [ctrlAddConstInPlaceFn]; rw [if_neg hx]
    simp only [hsub_eq, hadd_eq, and_self]

/-- Controlled in-place `- (c % 2^w) mod 2^w` in `≤ 16 * w` gates (`w + 1` ancillas). -/
noncomputable def ctrlSubConstInPlaceCircuit (w c : ℕ) : LayeredCircuit ((1 + w) + (w + 1)) :=
  (ctrlAddConstInPlaceCircuit w c).adj

lemma ctrlSubConstInPlaceCircuit_size (w c : ℕ) : (ctrlSubConstInPlaceCircuit w c).size ≤ 16 * w := by
  simpa [ctrlSubConstInPlaceCircuit] using ctrlAddConstInPlaceCircuit_size w c

theorem ctrlSubConstInPlaceCircuit_implements (w c : ℕ) :
    (ctrlSubConstInPlaceCircuit w c).ImplementsOnClean (permMat (ctrlSubConstInPlaceFn w c)) :=
  adj_implementsOnClean_perm (ctrlAddConstInPlaceCircuit w c)
    (fun x => (ctrlAddConstInPlaceFn_ctrlSubConstInPlaceFn w c x).2)
    (fun x => (ctrlAddConstInPlaceFn_ctrlSubConstInPlaceFn w c x).1)
    (ctrlAddConstInPlaceCircuit_implements w c)

/-! ### MSB-First Circuit Wrappers via Zero-Gate `Fin.revPerm` Conjugation -/

private def addPerm {a b : ℕ} (eA : Equiv.Perm (Fin a)) (eB : Equiv.Perm (Fin b)) :
    Equiv.Perm (Fin (a + b)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr eA eB)).trans finSumFinEquiv

@[simp] private lemma addPerm_castAdd {a b : ℕ} (eA : Equiv.Perm (Fin a)) (eB : Equiv.Perm (Fin b))
    (i : Fin a) :
    addPerm eA eB (Fin.castAdd b i) = Fin.castAdd b (eA i) := by
  change finSumFinEquiv (Equiv.sumCongr eA eB (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))) = _
  simp

@[simp] private lemma addPerm_natAdd {a b : ℕ} (eA : Equiv.Perm (Fin a)) (eB : Equiv.Perm (Fin b))
    (j : Fin b) :
    addPerm eA eB (Fin.natAdd a j) = Fin.natAdd a (eB j) := by
  change finSumFinEquiv (Equiv.sumCongr eA eB (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j)))) = _
  simp

private lemma implementsOnClean_conjPerm {main anc : ℕ} (lc : LayeredCircuit (main + anc))
    (eM : Equiv.Perm (Fin main)) (eA : Equiv.Perm (Fin anc))
    {fLSB fMSB : Qubits main → Qubits main}
    (hlc : lc.ImplementsOnClean (permMat fLSB))
    (hconj : ∀ x : Qubits main, fMSB x ∘ eM = fLSB (x ∘ eM)) :
    (lc.mapWires (addPerm eM eA).toEmbedding).ImplementsOnClean (permMat fMSB) := by
  apply implementsOnClean_of_act_perm
  intro x
  let emb := (addPerm eM eA).toEmbedding
  have hclean : ∀ j : Fin anc, padZero main anc x (emb (Fin.natAdd main j)) = false := fun j => by
    have he : emb (Fin.natAdd main j) = Fin.natAdd main (eA j) := by dsimp [emb]; simp
    rw [he]
    exact padZero_natAdd main anc x (eA j)
  have hact := act_mapWires_perm lc fLSB hlc emb (padZero main anc x) hclean
  dsimp only at hact
  rw [hact]
  congr 1; funext u
  let embM := (Fin.castAddEmb anc).trans emb
  have hembM_apply : ∀ i : Fin main, embM i = Fin.castAdd anc (eM i) := fun i => by
    change addPerm eM eA (Fin.castAdd anc i) = _
    simp
  have hcomp_eq : padZero main anc x ∘ embM = x ∘ eM := by
    funext i
    simp [Function.comp_apply, hembM_apply]
  refine Fin.addCases (fun k => ?_) (fun j => ?_) u
  · have hk_eq : Fin.castAdd anc k = embM (eM.symm k) := by
      rw [hembM_apply, Equiv.apply_symm_apply]
    rw [hk_eq, updateOn_apply_emb, hcomp_eq, ← hconj x, Function.comp_apply,
      Equiv.apply_symm_apply, ← hk_eq, padZero_castAdd]
  · have hnot : Fin.natAdd main j ∉ Set.range embM := by
      rintro ⟨i, hi⟩
      rw [hembM_apply] at hi
      exact absurd hi (Fin.ext_iff.ne.mpr (by simp; omega))
    rw [updateOn_apply_not_mem _ _ _ hnot, padZero_natAdd, padZero_natAdd]

private lemma natToBitsLSB_eq_comp_revPerm (w c : ℕ) (i : Fin w) :
    natToBitsLSB w c i = natToBits w c i.rev := by
  have hmod1 : natToBitsLSB w c i = natToBitsLSB w (c % 2 ^ w) i := by
    simp [natToBitsLSB, Nat.testBit_mod_two_pow, i.isLt]
  have hmod2 : natToBits w c = natToBits w (c % 2 ^ w) := by
    funext j; simp [natToBits]
  rw [hmod1, hmod2, natToBits_apply (Nat.mod_lt _ (Nat.two_pow_pos w)), Fin.rev_rev]

private lemma natToBits_eq_comp_revPerm (w c : ℕ) (i : Fin w) :
    natToBits w c i = natToBitsLSB w c i.rev := by
  rw [natToBitsLSB_eq_comp_revPerm, Fin.rev_rev]

-- 1. setConstMSBCircuit
noncomputable def setConstMSBCircuit (w c : ℕ) : LayeredCircuit (w + 0) :=
  (setConstCircuit w c).mapWires (addPerm Fin.revPerm (1 : Equiv.Perm (Fin 0))).toEmbedding

lemma setConstMSBCircuit_size (w c : ℕ) : (setConstMSBCircuit w c).size ≤ w := by
  simpa [setConstMSBCircuit] using setConstCircuit_size w c

theorem setConstMSBCircuit_implements (w c : ℕ) :
    (setConstMSBCircuit w c).ImplementsOnClean (permMat (setConstMSBFn w c)) := by
  refine implementsOnClean_conjPerm (setConstCircuit w c) Fin.revPerm 1
    (setConstCircuit_implements w c) fun x => ?_
  funext i
  simp [Function.comp_apply, setConstMSBFn, natToBitsLSB_eq_comp_revPerm]

-- 2. ctrlConstXorMSBCircuit
noncomputable def ctrlConstXorMSBCircuit (w c : ℕ) : LayeredCircuit ((1 + w) + 0) :=
  (ctrlConstXorCircuit w c).mapWires (addPerm (addPerm 1 Fin.revPerm) 1).toEmbedding

lemma ctrlConstXorMSBCircuit_size (w c : ℕ) : (ctrlConstXorMSBCircuit w c).size ≤ w := by
  simpa [ctrlConstXorMSBCircuit] using ctrlConstXorCircuit_size w c

theorem ctrlConstXorMSBCircuit_implements (w c : ℕ) :
    (ctrlConstXorMSBCircuit w c).ImplementsOnClean (permMat (ctrlConstXorMSBFn w c)) := by
  let eM := addPerm (1 : Equiv.Perm (Fin 1)) (Fin.revPerm : Equiv.Perm (Fin w))
  refine implementsOnClean_conjPerm (ctrlConstXorCircuit w c) eM 1
    (ctrlConstXorCircuit_implements w c) fun x => ?_
  funext u
  have h0 : eM ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    change eM (Fin.castAdd w 0) = Fin.castAdd w 0
    dsimp only [eM]; rw [addPerm_castAdd]; rfl
  refine Fin.addCases (fun z => ?_) (fun j => ?_) u
  · have hz : z = 0 := Fin.ext (by omega); subst hz
    have hca : (Fin.castAdd w (0 : Fin 1) : Fin (1 + w)) = ⟨0, by omega⟩ := rfl
    unfold ctrlConstXorMSBFn ctrlConstXorFn
    simp only [Function.comp_apply, hca, h0]
    have hge : ¬ (1 ≤ (⟨0, by omega⟩ : Fin (1 + w)).1) := by simp
    rw [dif_neg hge, dif_neg hge]
  · have hnat : eM (Fin.natAdd 1 j) = Fin.natAdd 1 j.rev := by
      dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
    unfold ctrlConstXorMSBFn ctrlConstXorFn
    simp only [Function.comp_apply, hnat, h0]
    have h1a : 1 ≤ (Fin.natAdd 1 j.rev : Fin (1 + w)).1 := by simp [Fin.natAdd]
    have h1b : 1 ≤ (Fin.natAdd 1 j : Fin (1 + w)).1 := by simp [Fin.natAdd]
    cases hx0 : x ⟨0, by omega⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte, dif_pos h1a, dif_pos h1b]
      have hj1 : (⟨(Fin.natAdd 1 j.rev : Fin (1 + w)).1 - 1, by have := j.rev.isLt; simp [Fin.natAdd]; omega⟩ : Fin w) = j.rev :=
        Fin.ext (by simp [Fin.natAdd])
      have hj2 : (⟨(Fin.natAdd 1 j : Fin (1 + w)).1 - 1, by simp [Fin.natAdd]⟩ : Fin w) = j :=
        Fin.ext (by simp [Fin.natAdd])
      rw [hj1, hj2, natToBits_eq_comp_revPerm, Fin.rev_rev]

-- 3. eqConstMSBCircuit
noncomputable def eqConstMSBCircuit (w c : ℕ) : LayeredCircuit ((w + 1) + w) :=
  (eqConstCircuit w c).mapWires (addPerm (addPerm Fin.revPerm 1) 1).toEmbedding

lemma eqConstMSBCircuit_size (w c : ℕ) : (eqConstMSBCircuit w c).size ≤ 14 * w + 12 := by
  simpa [eqConstMSBCircuit] using eqConstCircuit_size w c

theorem eqConstMSBCircuit_implements (w c : ℕ) :
    (eqConstMSBCircuit w c).ImplementsOnClean (permMat (eqConstMSBFn w c)) := by
  let eM := addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (1 : Equiv.Perm (Fin 1))
  refine implementsOnClean_conjPerm (eqConstCircuit w c) eM 1
    (eqConstCircuit_implements w c) fun x => ?_
  have hw_fix : eM ⟨w, by omega⟩ = ⟨w, by omega⟩ := by
    change eM (Fin.natAdd w 0) = Fin.natAdd w 0; simp [eM]
  have hi_rev : ∀ i : Fin w, eM ⟨i.1, by omega⟩ = ⟨i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.castAdd 1 i) = Fin.castAdd 1 (Fin.revPerm i); simp [eM, Fin.revPerm_apply]
  have heq_pred :
      decide (∀ i : Fin w, x ⟨i.1, by omega⟩ = natToBits w c i) =
      decide (∀ i : Fin w, (x ∘ eM) ⟨i.1, by omega⟩ = natToBitsLSB w c i) := by
    rw [Bool.eq_iff_iff]
    simp only [Function.comp_apply, decide_eq_true_eq]
    rw [← (Fin.revPerm : Equiv.Perm (Fin w)).forall_congr_right]
    refine forall_congr' fun i => ?_
    simp only [Fin.revPerm_apply, hi_rev, natToBits_eq_comp_revPerm, Fin.rev_rev]
  funext u
  rw [Function.comp_apply]
  refine Fin.addCases (fun i => ?_) (fun t => ?_) u
  · have hne1 : eM (Fin.castAdd 1 i) ≠ ⟨w, by omega⟩ := by
      rw [show (Fin.castAdd 1 i : Fin (w + 1)) = ⟨i.1, by omega⟩ from rfl, hi_rev]
      exact Fin.ne_of_val_ne (by simp; omega)
    have hne2 : Fin.castAdd 1 i ≠ ⟨w, by omega⟩ := Fin.ne_of_val_ne (by simp; omega)
    dsimp only [eqConstMSBFn, eqConstFn]
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
    rfl
  · have ht0 : t = 0 := Fin.ext (by omega); subst ht0
    have hnw : Fin.natAdd w (0 : Fin 1) = ⟨w, by omega⟩ := rfl
    dsimp only [eqConstMSBFn, eqConstFn]
    rw [hnw, hw_fix, Function.update_self, Function.update_self, Function.comp_apply, hw_fix, heq_pred]

-- 4. ltConstMSBCircuit
noncomputable def ltConstMSBCircuit (w H : ℕ) : LayeredCircuit ((w + 1) + w) :=
  (ltConstCircuit w H).mapWires (addPerm (addPerm Fin.revPerm 1) 1).toEmbedding

lemma ltConstMSBCircuit_size (w H : ℕ) : (ltConstMSBCircuit w H).size ≤ 20 * w + 1 := by
  have h := ltConstCircuit_size w H
  dsimp only [ltConstMSBCircuit]
  rw [LayeredCircuit.mapWires_size]
  omega

theorem ltConstMSBCircuit_implements (w H : ℕ) :
    (ltConstMSBCircuit w H).ImplementsOnClean (permMat (ltConstMSBFn w H)) := by
  let eM := addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (1 : Equiv.Perm (Fin 1))
  refine implementsOnClean_conjPerm (ltConstCircuit w H) eM 1
    (ltConstCircuit_implements_perm w H) fun x => ?_
  have hw_fix : eM ⟨w, Nat.lt_succ_self w⟩ = ⟨w, Nat.lt_succ_self w⟩ := by
    change eM (Fin.natAdd w 0) = Fin.natAdd w 0; simp [eM]
  have hi_rev : ∀ i : Fin w, eM ⟨i.1, by omega⟩ = ⟨i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.castAdd 1 i) = Fin.castAdd 1 (Fin.revPerm i); simp [eM, Fin.revPerm_apply]
  have hbits : bitsToNatLSB (fun i : Fin w => (x ∘ eM) ⟨i.1, by omega⟩) =
      bitsToNat (fun i : Fin w => x ⟨i.1, by omega⟩) := by
    have hcomp : (fun i : Fin w => (x ∘ eM) ⟨i.1, by omega⟩) =
        fun i : Fin w => (fun j : Fin w => x ⟨j.1, by omega⟩) i.rev := by
      funext i; simp only [Function.comp_apply, hi_rev]
    rw [hcomp]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨j.1, by omega⟩)
  funext u
  rw [Function.comp_apply]
  refine Fin.addCases (fun i => ?_) (fun t => ?_) u
  · have hne1 : eM (Fin.castAdd 1 i) ≠ ⟨w, Nat.lt_succ_self w⟩ := by
      rw [show (Fin.castAdd 1 i : Fin (w + 1)) = ⟨i.1, by omega⟩ from rfl, hi_rev]
      exact Fin.ne_of_val_ne (by simp; omega)
    have hne2 : Fin.castAdd 1 i ≠ ⟨w, Nat.lt_succ_self w⟩ := Fin.ne_of_val_ne (by simp; omega)
    dsimp only [ltConstMSBFn]
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
    rfl
  · have ht0 : t = 0 := Fin.ext (by omega); subst ht0
    have hnw : Fin.natAdd w (0 : Fin 1) = ⟨w, Nat.lt_succ_self w⟩ := rfl
    dsimp only [ltConstMSBFn]
    rw [hnw, hw_fix, Function.update_self, Function.update_self, Function.comp_apply, hw_fix, hbits]

-- 5. ltRegMSBCircuit
noncomputable def ltRegMSBCircuit (w : ℕ) : LayeredCircuit ((w + w + 1) + 1) :=
  (ltRegCircuit w).mapWires (addPerm (addPerm (addPerm Fin.revPerm Fin.revPerm) 1) 1).toEmbedding

lemma ltRegMSBCircuit_size (w : ℕ) : (ltRegMSBCircuit w).size = 16 * w + 1 := by
  simpa [ltRegMSBCircuit] using ltRegCircuit_size w

theorem ltRegMSBCircuit_implements (w : ℕ) :
    (ltRegMSBCircuit w).ImplementsOnClean (permMat (ltRegMSBFn w)) := by
  let ePair := addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (Fin.revPerm : Equiv.Perm (Fin w))
  let eM := addPerm ePair (1 : Equiv.Perm (Fin 1))
  refine implementsOnClean_conjPerm (ltRegCircuit w) eM 1 (ltRegCircuit_implements w) fun x => ?_
  have hw_fix : eM ⟨w + w, by omega⟩ = ⟨w + w, by omega⟩ := by
    change eM (Fin.natAdd (w + w) 0) = Fin.natAdd (w + w) 0
    dsimp only [eM]; rw [addPerm_natAdd]; rfl
  have ha_rev : ∀ i : Fin w, eM ⟨i.1, by omega⟩ = ⟨i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.castAdd 1 (Fin.castAdd w i)) = Fin.castAdd 1 (Fin.castAdd w i.rev)
    dsimp only [eM, ePair]; rw [addPerm_castAdd, addPerm_castAdd, Fin.revPerm_apply]
  have hb_rev : ∀ i : Fin w, eM ⟨w + i.1, by omega⟩ = ⟨w + i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.castAdd 1 (Fin.natAdd w i)) = Fin.castAdd 1 (Fin.natAdd w i.rev)
    dsimp only [eM, ePair]; rw [addPerm_castAdd, addPerm_natAdd, Fin.revPerm_apply]
  have ha_bits : bitsToNatLSB (fun i : Fin w => (x ∘ eM) ⟨i.1, by omega⟩) =
      bitsToNat (fun i : Fin w => x ⟨i.1, by omega⟩) := by
    rw [show (fun i : Fin w => (x ∘ eM) ⟨i.1, by omega⟩) =
      fun i : Fin w => (fun j : Fin w => x ⟨j.1, by omega⟩) i.rev from funext fun i => by simp [ha_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨j.1, by omega⟩)
  have hb_bits : bitsToNatLSB (fun i : Fin w => (x ∘ eM) ⟨w + i.1, by omega⟩) =
      bitsToNat (fun i : Fin w => x ⟨w + i.1, by omega⟩) := by
    rw [show (fun i : Fin w => (x ∘ eM) ⟨w + i.1, by omega⟩) =
      fun i : Fin w => (fun j : Fin w => x ⟨w + j.1, by omega⟩) i.rev from funext fun i => by simp [hb_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨w + j.1, by omega⟩)
  funext u
  rw [Function.comp_apply]
  refine Fin.addCases (fun ij => ?_) (fun t => ?_) u
  · have hne1 : eM (Fin.castAdd 1 ij) ≠ ⟨w + w, by omega⟩ := by
      have h1 : (eM (Fin.castAdd 1 ij)).1 = (ePair ij).1 := by
        change (addPerm ePair (1 : Equiv.Perm (Fin 1)) (Fin.castAdd 1 ij)).1 = _
        simp
      exact Fin.ne_of_val_ne (by rw [h1]; exact (ePair ij).isLt.ne)
    have hne2 : Fin.castAdd 1 ij ≠ ⟨w + w, by omega⟩ := Fin.ne_of_val_ne (by simp; omega)
    dsimp only [ltRegMSBFn, ltRegFn]
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
    rfl
  · have ht0 : t = 0 := Fin.ext (by omega); subst ht0
    have hnw : Fin.natAdd (w + w) (0 : Fin 1) = ⟨w + w, by omega⟩ := rfl
    dsimp only [ltRegMSBFn, ltRegFn]
    rw [hnw, hw_fix, Function.update_self, Function.update_self, Function.comp_apply, hw_fix,
      ha_bits, hb_bits]

-- 6 & 7. addInPlaceMSBCircuit & subInPlaceMSBCircuit
noncomputable def addInPlaceMSBCircuit (w : ℕ) : LayeredCircuit ((w + w) + 1) :=
  (addInPlaceCircuit w).mapWires (addPerm (addPerm Fin.revPerm Fin.revPerm) 1).toEmbedding

lemma addInPlaceMSBCircuit_size (w : ℕ) : (addInPlaceMSBCircuit w).size = 14 * w := by
  simpa [addInPlaceMSBCircuit] using addInPlaceCircuit_size w

noncomputable def subInPlaceMSBCircuit (w : ℕ) : LayeredCircuit ((w + w) + 1) :=
  (subInPlaceCircuit w).mapWires (addPerm (addPerm Fin.revPerm Fin.revPerm) 1).toEmbedding

lemma subInPlaceMSBCircuit_size (w : ℕ) : (subInPlaceMSBCircuit w).size = 14 * w := by
  simpa [subInPlaceMSBCircuit] using subInPlaceCircuit_size w

private lemma addInPlaceMSB_conj (w : ℕ) (x : Qubits (w + w)) :
    addInPlaceMSBFn w x ∘ addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (Fin.revPerm : Equiv.Perm (Fin w)) =
      addInPlaceFn w (x ∘ addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (Fin.revPerm : Equiv.Perm (Fin w))) := by
  let eM := addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (Fin.revPerm : Equiv.Perm (Fin w))
  have ha_rev : ∀ i : Fin w, eM ⟨i.1, by omega⟩ = ⟨i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.castAdd w i) = Fin.castAdd w i.rev; dsimp only [eM]; rw [addPerm_castAdd, Fin.revPerm_apply]
  have hb_rev : ∀ i : Fin w, eM ⟨w + i.1, by omega⟩ = ⟨w + i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.natAdd w i) = Fin.natAdd w i.rev; dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
  have ha_bits : bitsToNatLSB (fun i : Fin w => x (eM ⟨i.1, by omega⟩)) =
      bitsToNat (fun i : Fin w => x ⟨i.1, by omega⟩) := by
    rw [show (fun i : Fin w => x (eM ⟨i.1, by omega⟩)) =
      fun i : Fin w => (fun j : Fin w => x ⟨j.1, by omega⟩) i.rev from funext fun i => by simp [ha_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨j.1, by omega⟩)
  have hb_bits : bitsToNatLSB (fun i : Fin w => x (eM ⟨w + i.1, by omega⟩)) =
      bitsToNat (fun i : Fin w => x ⟨w + i.1, by omega⟩) := by
    rw [show (fun i : Fin w => x (eM ⟨w + i.1, by omega⟩)) =
      fun i : Fin w => (fun j : Fin w => x ⟨w + j.1, by omega⟩) i.rev from funext fun i => by simp [hb_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨w + j.1, by omega⟩)
  funext u
  rw [Function.comp_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) u
  · have hm : eM (Fin.castAdd w i) = Fin.castAdd w i.rev := by dsimp only [eM]; rw [addPerm_castAdd, Fin.revPerm_apply]
    dsimp only [addInPlaceMSBFn, addInPlaceFn]
    rw [show addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (Fin.revPerm : Equiv.Perm (Fin w)) = eM from rfl, hm]
    have hlt1 : (Fin.castAdd w i.rev : Fin (w + w)).1 < w := by dsimp [Fin.castAdd]; exact i.rev.isLt
    have hlt2 : (Fin.castAdd w i : Fin (w + w)).1 < w := by dsimp [Fin.castAdd]; exact i.isLt
    rw [dif_pos hlt1, dif_pos hlt2]
    simp only [Function.comp_apply]
    rw [show (⟨(Fin.castAdd w i : Fin (w + w)).1, (Fin.castAdd w i).isLt⟩ : Fin (w + w)) = Fin.castAdd w i from Fin.ext rfl, hm]
  · have hm : eM (Fin.natAdd w i) = Fin.natAdd w i.rev := by dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
    dsimp only [addInPlaceMSBFn, addInPlaceFn]
    rw [show addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (Fin.revPerm : Equiv.Perm (Fin w)) = eM from rfl, hm]
    have hge1 : ¬ ((Fin.natAdd w i.rev : Fin (w + w)).1 < w) := by simp [Fin.natAdd]
    have hge2 : ¬ ((Fin.natAdd w i : Fin (w + w)).1 < w) := by simp [Fin.natAdd]
    rw [dif_neg hge1, dif_neg hge2]
    dsimp only [Function.comp_apply]
    rw [ha_bits, hb_bits]
    have hidx1 : (⟨(Fin.natAdd w i.rev : Fin (w + w)).1 - w, by have := i.rev.isLt; simp [Fin.natAdd]; omega⟩ : Fin w) = i.rev :=
      Fin.ext (by simp [Fin.natAdd])
    have hidx2 : (⟨(Fin.natAdd w i : Fin (w + w)).1 - w, by simp [Fin.natAdd]⟩ : Fin w) = i :=
      Fin.ext (by simp [Fin.natAdd])
    rw [hidx1, hidx2, natToBits_eq_comp_revPerm, Fin.rev_rev]

theorem addInPlaceMSBCircuit_implements (w : ℕ) :
    (addInPlaceMSBCircuit w).ImplementsOnClean (permMat (addInPlaceMSBFn w)) :=
  implementsOnClean_conjPerm (addInPlaceCircuit w) (addPerm Fin.revPerm Fin.revPerm) 1
    (addInPlaceCircuit_implements w) (addInPlaceMSB_conj w)

private lemma subInPlaceMSB_conj (w : ℕ) (x : Qubits (w + w)) :
    subInPlaceMSBFn w x ∘ addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (Fin.revPerm : Equiv.Perm (Fin w)) =
      subInPlaceFn w (x ∘ addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (Fin.revPerm : Equiv.Perm (Fin w))) := by
  let eM := addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (Fin.revPerm : Equiv.Perm (Fin w))
  have ha_rev : ∀ i : Fin w, eM ⟨i.1, by omega⟩ = ⟨i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.castAdd w i) = Fin.castAdd w i.rev; dsimp only [eM]; rw [addPerm_castAdd, Fin.revPerm_apply]
  have hb_rev : ∀ i : Fin w, eM ⟨w + i.1, by omega⟩ = ⟨w + i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.natAdd w i) = Fin.natAdd w i.rev; dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
  have ha_bits : bitsToNatLSB (fun i : Fin w => x (eM ⟨i.1, by omega⟩)) =
      bitsToNat (fun i : Fin w => x ⟨i.1, by omega⟩) := by
    rw [show (fun i : Fin w => x (eM ⟨i.1, by omega⟩)) =
      fun i : Fin w => (fun j : Fin w => x ⟨j.1, by omega⟩) i.rev from funext fun i => by simp [ha_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨j.1, by omega⟩)
  have hb_bits : bitsToNatLSB (fun i : Fin w => x (eM ⟨w + i.1, by omega⟩)) =
      bitsToNat (fun i : Fin w => x ⟨w + i.1, by omega⟩) := by
    rw [show (fun i : Fin w => x (eM ⟨w + i.1, by omega⟩)) =
      fun i : Fin w => (fun j : Fin w => x ⟨w + j.1, by omega⟩) i.rev from funext fun i => by simp [hb_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨w + j.1, by omega⟩)
  funext u
  rw [Function.comp_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) u
  · have hm : eM (Fin.castAdd w i) = Fin.castAdd w i.rev := by dsimp only [eM]; rw [addPerm_castAdd, Fin.revPerm_apply]
    dsimp only [subInPlaceMSBFn, subInPlaceFn]
    rw [show addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (Fin.revPerm : Equiv.Perm (Fin w)) = eM from rfl, hm]
    have hlt1 : (Fin.castAdd w i.rev : Fin (w + w)).1 < w := by dsimp [Fin.castAdd]; exact i.rev.isLt
    have hlt2 : (Fin.castAdd w i : Fin (w + w)).1 < w := by dsimp [Fin.castAdd]; exact i.isLt
    rw [dif_pos hlt1, dif_pos hlt2]
    simp only [Function.comp_apply]
    rw [show (⟨(Fin.castAdd w i : Fin (w + w)).1, (Fin.castAdd w i).isLt⟩ : Fin (w + w)) = Fin.castAdd w i from Fin.ext rfl, hm]
  · have hm : eM (Fin.natAdd w i) = Fin.natAdd w i.rev := by dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
    dsimp only [subInPlaceMSBFn, subInPlaceFn]
    rw [show addPerm (Fin.revPerm : Equiv.Perm (Fin w)) (Fin.revPerm : Equiv.Perm (Fin w)) = eM from rfl, hm]
    have hge1 : ¬ ((Fin.natAdd w i.rev : Fin (w + w)).1 < w) := by simp [Fin.natAdd]
    have hge2 : ¬ ((Fin.natAdd w i : Fin (w + w)).1 < w) := by simp [Fin.natAdd]
    rw [dif_neg hge1, dif_neg hge2]
    dsimp only [Function.comp_apply]
    rw [ha_bits, hb_bits]
    have hidx1 : (⟨(Fin.natAdd w i.rev : Fin (w + w)).1 - w, by have := i.rev.isLt; simp [Fin.natAdd]; omega⟩ : Fin w) = i.rev :=
      Fin.ext (by simp [Fin.natAdd])
    have hidx2 : (⟨(Fin.natAdd w i : Fin (w + w)).1 - w, by simp [Fin.natAdd]⟩ : Fin w) = i :=
      Fin.ext (by simp [Fin.natAdd])
    rw [hidx1, hidx2, natToBits_eq_comp_revPerm, Fin.rev_rev]

theorem subInPlaceMSBCircuit_implements (w : ℕ) :
    (subInPlaceMSBCircuit w).ImplementsOnClean (permMat (subInPlaceMSBFn w)) :=
  implementsOnClean_conjPerm (subInPlaceCircuit w) (addPerm Fin.revPerm Fin.revPerm) 1
    (subInPlaceCircuit_implements w) (subInPlaceMSB_conj w)

-- 8 & 9. ctrlAddInPlaceMSBCircuit & ctrlSubInPlaceMSBCircuit
noncomputable def ctrlAddInPlaceMSBCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + (w + 1)) :=
  (ctrlAddInPlaceCircuit w).mapWires (addPerm (addPerm (addPerm 1 Fin.revPerm) Fin.revPerm) 1).toEmbedding

lemma ctrlAddInPlaceMSBCircuit_size (w : ℕ) : (ctrlAddInPlaceMSBCircuit w).size = 24 * w := by
  simpa [ctrlAddInPlaceMSBCircuit] using ctrlAddInPlaceCircuit_size w

noncomputable def ctrlSubInPlaceMSBCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + (w + 1)) :=
  (ctrlSubInPlaceCircuit w).mapWires (addPerm (addPerm (addPerm 1 Fin.revPerm) Fin.revPerm) 1).toEmbedding

lemma ctrlSubInPlaceMSBCircuit_size (w : ℕ) : (ctrlSubInPlaceMSBCircuit w).size = 24 * w := by
  simpa [ctrlSubInPlaceMSBCircuit] using ctrlSubInPlaceCircuit_size w

private lemma ctrlAddInPlaceMSB_conj (w : ℕ) (x : Qubits (1 + w + w)) :
    ctrlAddInPlaceMSBFn w x ∘ addPerm (addPerm 1 (Fin.revPerm : Equiv.Perm (Fin w))) (Fin.revPerm : Equiv.Perm (Fin w)) =
      ctrlAddInPlaceFn w (x ∘ addPerm (addPerm 1 (Fin.revPerm : Equiv.Perm (Fin w))) (Fin.revPerm : Equiv.Perm (Fin w))) := by
  let e1 := addPerm (1 : Equiv.Perm (Fin 1)) (Fin.revPerm : Equiv.Perm (Fin w))
  let eM := addPerm e1 (Fin.revPerm : Equiv.Perm (Fin w))
  have h0 : eM ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    change eM (Fin.castAdd w (Fin.castAdd w 0)) = Fin.castAdd w (Fin.castAdd w 0)
    dsimp only [eM, e1]; rw [addPerm_castAdd, addPerm_castAdd]; rfl
  have ha_rev : ∀ i : Fin w, eM ⟨1 + i.1, by omega⟩ = ⟨1 + i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.castAdd w (Fin.natAdd 1 i)) = Fin.castAdd w (Fin.natAdd 1 i.rev)
    dsimp only [eM, e1]; rw [addPerm_castAdd, addPerm_natAdd, Fin.revPerm_apply]
  have hb_rev : ∀ i : Fin w, eM ⟨1 + w + i.1, by omega⟩ = ⟨1 + w + i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.natAdd (1 + w) i) = Fin.natAdd (1 + w) i.rev
    dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
  have ha_bits : bitsToNatLSB (fun i : Fin w => x (eM ⟨1 + i.1, by omega⟩)) =
      bitsToNat (fun i : Fin w => x ⟨1 + i.1, by omega⟩) := by
    rw [show (fun i : Fin w => x (eM ⟨1 + i.1, by omega⟩)) =
      fun i : Fin w => (fun j : Fin w => x ⟨1 + j.1, by omega⟩) i.rev from funext fun i => by simp [ha_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨1 + j.1, by omega⟩)
  have hb_bits : bitsToNatLSB (fun i : Fin w => x (eM ⟨1 + w + i.1, by omega⟩)) =
      bitsToNat (fun i : Fin w => x ⟨1 + w + i.1, by omega⟩) := by
    rw [show (fun i : Fin w => x (eM ⟨1 + w + i.1, by omega⟩)) =
      fun i : Fin w => (fun j : Fin w => x ⟨1 + w + j.1, by omega⟩) i.rev from funext fun i => by simp [hb_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨1 + w + j.1, by omega⟩)
  funext u
  rw [Function.comp_apply]
  dsimp only [ctrlAddInPlaceMSBFn, ctrlAddInPlaceFn]
  rw [show addPerm (addPerm 1 (Fin.revPerm : Equiv.Perm (Fin w))) (Fin.revPerm : Equiv.Perm (Fin w)) = eM from rfl]
  simp only [Function.comp_apply, h0]
  cases hx0 : x ⟨0, by omega⟩ <;> simp only [Bool.false_eq_true, ↓reduceIte]
  refine Fin.addCases (fun ci => ?_) (fun i => ?_) u
  · refine Fin.addCases (fun z => ?_) (fun i => ?_) ci
    · have hz0 : z = 0 := Fin.ext (by omega); subst hz0
      have hca0 : (Fin.castAdd w (Fin.castAdd w (0 : Fin 1)) : Fin (1 + w + w)) = ⟨0, by omega⟩ := rfl
      rw [hca0, h0]
      have hne : ¬ (1 + w ≤ (⟨0, by omega⟩ : Fin (1 + w + w)).1) := by simp
      rw [dif_neg hne, dif_neg hne]
    · have hca : (Fin.castAdd w (Fin.natAdd 1 i) : Fin (1 + w + w)) = ⟨1 + i.1, by omega⟩ := rfl
      rw [hca, ha_rev]
      have hi1 := i.rev.isLt
      have hi2 := i.isLt
      have hne1 : ¬ (1 + w ≤ (⟨1 + i.rev.1, by omega⟩ : Fin (1 + w + w)).1) := by dsimp; omega
      have hne2 : ¬ (1 + w ≤ (⟨1 + i.1, by omega⟩ : Fin (1 + w + w)).1) := by dsimp; omega
      rw [dif_neg hne1, dif_neg hne2]
  · have hm : eM (Fin.natAdd (1 + w) i) = Fin.natAdd (1 + w) i.rev := by
      dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
    rw [hm]
    have hge1 : 1 + w ≤ (Fin.natAdd (1 + w) i.rev : Fin (1 + w + w)).1 := by simp [Fin.natAdd]
    have hge2 : 1 + w ≤ (Fin.natAdd (1 + w) i : Fin (1 + w + w)).1 := by simp [Fin.natAdd]
    rw [dif_pos hge1, dif_pos hge2]
    rw [ha_bits, hb_bits]
    have hidx1 : (⟨(Fin.natAdd (1 + w) i.rev : Fin (1 + w + w)).1 - (1 + w), by have := i.rev.isLt; simp [Fin.natAdd]; omega⟩ : Fin w) = i.rev :=
      Fin.ext (by simp [Fin.natAdd])
    have hidx2 : (⟨(Fin.natAdd (1 + w) i : Fin (1 + w + w)).1 - (1 + w), by simp [Fin.natAdd]⟩ : Fin w) = i :=
      Fin.ext (by simp [Fin.natAdd])
    rw [hidx1, hidx2, natToBits_eq_comp_revPerm, Fin.rev_rev]

theorem ctrlAddInPlaceMSBCircuit_implements (w : ℕ) :
    (ctrlAddInPlaceMSBCircuit w).ImplementsOnClean (permMat (ctrlAddInPlaceMSBFn w)) :=
  implementsOnClean_conjPerm (ctrlAddInPlaceCircuit w)
    (addPerm (addPerm 1 Fin.revPerm) Fin.revPerm) 1
    (ctrlAddInPlaceCircuit_implements w) (ctrlAddInPlaceMSB_conj w)

private lemma ctrlSubInPlaceMSB_conj (w : ℕ) (x : Qubits (1 + w + w)) :
    ctrlSubInPlaceMSBFn w x ∘ addPerm (addPerm 1 (Fin.revPerm : Equiv.Perm (Fin w))) (Fin.revPerm : Equiv.Perm (Fin w)) =
      ctrlSubInPlaceFn w (x ∘ addPerm (addPerm 1 (Fin.revPerm : Equiv.Perm (Fin w))) (Fin.revPerm : Equiv.Perm (Fin w))) := by
  let e1 := addPerm (1 : Equiv.Perm (Fin 1)) (Fin.revPerm : Equiv.Perm (Fin w))
  let eM := addPerm e1 (Fin.revPerm : Equiv.Perm (Fin w))
  have h0 : eM ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    change eM (Fin.castAdd w (Fin.castAdd w 0)) = Fin.castAdd w (Fin.castAdd w 0)
    dsimp only [eM, e1]; rw [addPerm_castAdd, addPerm_castAdd]; rfl
  have ha_rev : ∀ i : Fin w, eM ⟨1 + i.1, by omega⟩ = ⟨1 + i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.castAdd w (Fin.natAdd 1 i)) = Fin.castAdd w (Fin.natAdd 1 i.rev)
    dsimp only [eM, e1]; rw [addPerm_castAdd, addPerm_natAdd, Fin.revPerm_apply]
  have hb_rev : ∀ i : Fin w, eM ⟨1 + w + i.1, by omega⟩ = ⟨1 + w + i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.natAdd (1 + w) i) = Fin.natAdd (1 + w) i.rev
    dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
  have ha_bits : bitsToNatLSB (fun i : Fin w => x (eM ⟨1 + i.1, by omega⟩)) =
      bitsToNat (fun i : Fin w => x ⟨1 + i.1, by omega⟩) := by
    rw [show (fun i : Fin w => x (eM ⟨1 + i.1, by omega⟩)) =
      fun i : Fin w => (fun j : Fin w => x ⟨1 + j.1, by omega⟩) i.rev from funext fun i => by simp [ha_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨1 + j.1, by omega⟩)
  have hb_bits : bitsToNatLSB (fun i : Fin w => x (eM ⟨1 + w + i.1, by omega⟩)) =
      bitsToNat (fun i : Fin w => x ⟨1 + w + i.1, by omega⟩) := by
    rw [show (fun i : Fin w => x (eM ⟨1 + w + i.1, by omega⟩)) =
      fun i : Fin w => (fun j : Fin w => x ⟨1 + w + j.1, by omega⟩) i.rev from funext fun i => by simp [hb_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨1 + w + j.1, by omega⟩)
  funext u
  rw [Function.comp_apply]
  dsimp only [ctrlSubInPlaceMSBFn, ctrlSubInPlaceFn]
  rw [show addPerm (addPerm 1 (Fin.revPerm : Equiv.Perm (Fin w))) (Fin.revPerm : Equiv.Perm (Fin w)) = eM from rfl]
  simp only [Function.comp_apply, h0]
  cases hx0 : x ⟨0, by omega⟩ <;> simp only [Bool.false_eq_true, ↓reduceIte]
  refine Fin.addCases (fun ci => ?_) (fun i => ?_) u
  · refine Fin.addCases (fun z => ?_) (fun i => ?_) ci
    · have hz0 : z = 0 := Fin.ext (by omega); subst hz0
      have hca0 : (Fin.castAdd w (Fin.castAdd w (0 : Fin 1)) : Fin (1 + w + w)) = ⟨0, by omega⟩ := rfl
      rw [hca0, h0]
      have hne : ¬ (1 + w ≤ (⟨0, by omega⟩ : Fin (1 + w + w)).1) := by simp
      rw [dif_neg hne, dif_neg hne]
    · have hca : (Fin.castAdd w (Fin.natAdd 1 i) : Fin (1 + w + w)) = ⟨1 + i.1, by omega⟩ := rfl
      rw [hca, ha_rev]
      have hi1 := i.rev.isLt
      have hi2 := i.isLt
      have hne1 : ¬ (1 + w ≤ (⟨1 + i.rev.1, by omega⟩ : Fin (1 + w + w)).1) := by dsimp; omega
      have hne2 : ¬ (1 + w ≤ (⟨1 + i.1, by omega⟩ : Fin (1 + w + w)).1) := by dsimp; omega
      rw [dif_neg hne1, dif_neg hne2]
  · have hm : eM (Fin.natAdd (1 + w) i) = Fin.natAdd (1 + w) i.rev := by
      dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
    rw [hm]
    have hge1 : 1 + w ≤ (Fin.natAdd (1 + w) i.rev : Fin (1 + w + w)).1 := by simp [Fin.natAdd]
    have hge2 : 1 + w ≤ (Fin.natAdd (1 + w) i : Fin (1 + w + w)).1 := by simp [Fin.natAdd]
    rw [dif_pos hge1, dif_pos hge2]
    rw [ha_bits, hb_bits]
    have hidx1 : (⟨(Fin.natAdd (1 + w) i.rev : Fin (1 + w + w)).1 - (1 + w), by have := i.rev.isLt; simp [Fin.natAdd]; omega⟩ : Fin w) = i.rev :=
      Fin.ext (by simp [Fin.natAdd])
    have hidx2 : (⟨(Fin.natAdd (1 + w) i : Fin (1 + w + w)).1 - (1 + w), by simp [Fin.natAdd]⟩ : Fin w) = i :=
      Fin.ext (by simp [Fin.natAdd])
    rw [hidx1, hidx2, natToBits_eq_comp_revPerm, Fin.rev_rev]

theorem ctrlSubInPlaceMSBCircuit_implements (w : ℕ) :
    (ctrlSubInPlaceMSBCircuit w).ImplementsOnClean (permMat (ctrlSubInPlaceMSBFn w)) :=
  implementsOnClean_conjPerm (ctrlSubInPlaceCircuit w)
    (addPerm (addPerm 1 Fin.revPerm) Fin.revPerm) 1
    (ctrlSubInPlaceCircuit_implements w) (ctrlSubInPlaceMSB_conj w)

-- 10 & 11. ctrlAddConstInPlaceMSBCircuit & ctrlSubConstInPlaceMSBCircuit
noncomputable def ctrlAddConstInPlaceMSBCircuit (w c : ℕ) : LayeredCircuit ((1 + w) + (w + 1)) :=
  (ctrlAddConstInPlaceCircuit w c).mapWires (addPerm (addPerm 1 Fin.revPerm) 1).toEmbedding

lemma ctrlAddConstInPlaceMSBCircuit_size (w c : ℕ) : (ctrlAddConstInPlaceMSBCircuit w c).size ≤ 16 * w := by
  simpa [ctrlAddConstInPlaceMSBCircuit] using ctrlAddConstInPlaceCircuit_size w c

noncomputable def ctrlSubConstInPlaceMSBCircuit (w c : ℕ) : LayeredCircuit ((1 + w) + (w + 1)) :=
  (ctrlSubConstInPlaceCircuit w c).mapWires (addPerm (addPerm 1 Fin.revPerm) 1).toEmbedding

lemma ctrlSubConstInPlaceMSBCircuit_size (w c : ℕ) : (ctrlSubConstInPlaceMSBCircuit w c).size ≤ 16 * w := by
  simpa [ctrlSubConstInPlaceMSBCircuit] using ctrlSubConstInPlaceCircuit_size w c

theorem ctrlAddConstInPlaceMSBCircuit_implements (w c : ℕ) :
    (ctrlAddConstInPlaceMSBCircuit w c).ImplementsOnClean (permMat (ctrlAddConstInPlaceMSBFn w c)) := by
  let eM := addPerm (1 : Equiv.Perm (Fin 1)) (Fin.revPerm : Equiv.Perm (Fin w))
  refine implementsOnClean_conjPerm (ctrlAddConstInPlaceCircuit w c) eM 1
    (ctrlAddConstInPlaceCircuit_implements w c) fun x => ?_
  have h0 : eM ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    change eM (Fin.castAdd w 0) = Fin.castAdd w 0; dsimp only [eM]; rw [addPerm_castAdd]; rfl
  have hb_rev : ∀ i : Fin w, eM ⟨1 + i.1, by omega⟩ = ⟨1 + i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.natAdd 1 i) = Fin.natAdd 1 i.rev; dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
  have hb_bits : bitsToNatLSB (fun i : Fin w => x (eM ⟨1 + i.1, by omega⟩)) =
      bitsToNat (fun i : Fin w => x ⟨1 + i.1, by omega⟩) := by
    rw [show (fun i : Fin w => x (eM ⟨1 + i.1, by omega⟩)) =
      fun i : Fin w => (fun j : Fin w => x ⟨1 + j.1, by omega⟩) i.rev from funext fun i => by simp [hb_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨1 + j.1, by omega⟩)
  funext u
  rw [Function.comp_apply]
  dsimp only [ctrlAddConstInPlaceMSBFn, ctrlAddConstInPlaceFn]
  simp only [Function.comp_apply, h0]
  cases hx0 : x ⟨0, by omega⟩ <;> simp only [Bool.false_eq_true, ↓reduceIte]
  refine Fin.addCases (fun z => ?_) (fun i => ?_) u
  · have hz0 : z = 0 := Fin.ext (by omega); subst hz0
    have hnw : (Fin.castAdd w (0 : Fin 1) : Fin (1 + w)) = ⟨0, by omega⟩ := rfl
    have hlt : ¬ (1 ≤ (⟨0, by omega⟩ : Fin (1 + w)).1) := by simp
    rw [hnw, h0, dif_neg hlt, dif_neg hlt]
  · have hm : eM (Fin.natAdd 1 i) = Fin.natAdd 1 i.rev := by dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
    have h1a : 1 ≤ (Fin.natAdd 1 i.rev : Fin (1 + w)).1 := by simp [Fin.natAdd]
    have h1b : 1 ≤ (Fin.natAdd 1 i : Fin (1 + w)).1 := by simp [Fin.natAdd]
    rw [hm, dif_pos h1a, dif_pos h1b]
    rw [hb_bits]
    have hidx1 : (⟨(Fin.natAdd 1 i.rev : Fin (1 + w)).1 - 1, by have := i.rev.isLt; simp [Fin.natAdd]; omega⟩ : Fin w) = i.rev := Fin.ext (by simp [Fin.natAdd])
    have hidx2 : (⟨(Fin.natAdd 1 i : Fin (1 + w)).1 - 1, by simp [Fin.natAdd]⟩ : Fin w) = i := Fin.ext (by simp [Fin.natAdd])
    rw [hidx1, hidx2, natToBits_eq_comp_revPerm, Fin.rev_rev]

theorem ctrlSubConstInPlaceMSBCircuit_implements (w c : ℕ) :
    (ctrlSubConstInPlaceMSBCircuit w c).ImplementsOnClean (permMat (ctrlSubConstInPlaceMSBFn w c)) := by
  let eM := addPerm (1 : Equiv.Perm (Fin 1)) (Fin.revPerm : Equiv.Perm (Fin w))
  refine implementsOnClean_conjPerm (ctrlSubConstInPlaceCircuit w c) eM 1
    (ctrlSubConstInPlaceCircuit_implements w c) fun x => ?_
  have h0 : eM ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
    change eM (Fin.castAdd w 0) = Fin.castAdd w 0; dsimp only [eM]; rw [addPerm_castAdd]; rfl
  have hb_rev : ∀ i : Fin w, eM ⟨1 + i.1, by omega⟩ = ⟨1 + i.rev.1, by omega⟩ := fun i => by
    change eM (Fin.natAdd 1 i) = Fin.natAdd 1 i.rev; dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
  have hb_bits : bitsToNatLSB (fun i : Fin w => x (eM ⟨1 + i.1, by omega⟩)) =
      bitsToNat (fun i : Fin w => x ⟨1 + i.1, by omega⟩) := by
    rw [show (fun i : Fin w => x (eM ⟨1 + i.1, by omega⟩)) =
      fun i : Fin w => (fun j : Fin w => x ⟨1 + j.1, by omega⟩) i.rev from funext fun i => by simp [hb_rev]]
    exact bitsToNatLSB_rev (fun j : Fin w => x ⟨1 + j.1, by omega⟩)
  funext u
  rw [Function.comp_apply]
  dsimp only [ctrlSubConstInPlaceMSBFn, ctrlSubConstInPlaceFn]
  simp only [Function.comp_apply, h0]
  cases hx0 : x ⟨0, by omega⟩ <;> simp only [Bool.false_eq_true, ↓reduceIte]
  refine Fin.addCases (fun z => ?_) (fun i => ?_) u
  · have hz0 : z = 0 := Fin.ext (by omega); subst hz0
    have hnw : (Fin.castAdd w (0 : Fin 1) : Fin (1 + w)) = ⟨0, by omega⟩ := rfl
    have hlt : ¬ (1 ≤ (⟨0, by omega⟩ : Fin (1 + w)).1) := by simp
    rw [hnw, h0, dif_neg hlt, dif_neg hlt]
  · have hm : eM (Fin.natAdd 1 i) = Fin.natAdd 1 i.rev := by dsimp only [eM]; rw [addPerm_natAdd, Fin.revPerm_apply]
    have h1a : 1 ≤ (Fin.natAdd 1 i.rev : Fin (1 + w)).1 := by simp [Fin.natAdd]
    have h1b : 1 ≤ (Fin.natAdd 1 i : Fin (1 + w)).1 := by simp [Fin.natAdd]
    rw [hm, dif_pos h1a, dif_pos h1b]
    rw [hb_bits]
    have hidx1 : (⟨(Fin.natAdd 1 i.rev : Fin (1 + w)).1 - 1, by have := i.rev.isLt; simp [Fin.natAdd]; omega⟩ : Fin w) = i.rev := Fin.ext (by simp [Fin.natAdd])
    have hidx2 : (⟨(Fin.natAdd 1 i : Fin (1 + w)).1 - 1, by simp [Fin.natAdd]⟩ : Fin w) = i := Fin.ext (by simp [Fin.natAdd])
    rw [hidx1, hidx2, natToBits_eq_comp_revPerm, Fin.rev_rev]

end Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Aux_w54_arith

theorem solution : Nonempty LcgSym54ArithV2 := ⟨{
  permMat_id := @permMat_id
  permMat_mul := @permMat_mul
  seqClean_perm := @seqClean_perm
  adj_implementsOnClean_perm := @adj_implementsOnClean_perm
  implementsOnClean_id_perm := @implementsOnClean_id_perm
  act_mapWires_perm := act_mapWires_perm
  act_subReg_perm := act_subReg_perm
  copyRegCircuit := copyRegCircuit
  copyRegCircuit_size := copyRegCircuit_size
  copyRegCircuit_implements := copyRegCircuit_implements
  swapRegCircuit := swapRegCircuit
  swapRegCircuit_size := swapRegCircuit_size
  swapRegCircuit_implements := swapRegCircuit_implements
  cswapRegCircuit := cswapRegCircuit
  cswapRegCircuit_size := cswapRegCircuit_size
  cswapRegCircuit_implements := cswapRegCircuit_implements
  ctrlCopyRegCircuit := ctrlCopyRegCircuit
  ctrlCopyRegCircuit_size := ctrlCopyRegCircuit_size
  ctrlCopyRegCircuit_implements := ctrlCopyRegCircuit_implements
  eqRegCircuit := eqRegCircuit
  eqRegCircuit_size := eqRegCircuit_size
  eqRegCircuit_implements := eqRegCircuit_implements
  setConstMSBCircuit := setConstMSBCircuit
  setConstMSBCircuit_size := setConstMSBCircuit_size
  setConstMSBCircuit_implements := setConstMSBCircuit_implements
  ctrlConstXorMSBCircuit := ctrlConstXorMSBCircuit
  ctrlConstXorMSBCircuit_size := ctrlConstXorMSBCircuit_size
  ctrlConstXorMSBCircuit_implements := ctrlConstXorMSBCircuit_implements
  eqConstMSBCircuit := eqConstMSBCircuit
  eqConstMSBCircuit_size := eqConstMSBCircuit_size
  eqConstMSBCircuit_implements := eqConstMSBCircuit_implements
  ltConstMSBCircuit := ltConstMSBCircuit
  ltConstMSBCircuit_size := ltConstMSBCircuit_size
  ltConstMSBCircuit_implements := ltConstMSBCircuit_implements
  ltRegMSBCircuit := ltRegMSBCircuit
  ltRegMSBCircuit_size := ltRegMSBCircuit_size
  ltRegMSBCircuit_implements := ltRegMSBCircuit_implements
  addInPlaceMSBCircuit := addInPlaceMSBCircuit
  addInPlaceMSBCircuit_size := addInPlaceMSBCircuit_size
  addInPlaceMSBCircuit_implements := addInPlaceMSBCircuit_implements
  subInPlaceMSBCircuit := subInPlaceMSBCircuit
  subInPlaceMSBCircuit_size := subInPlaceMSBCircuit_size
  subInPlaceMSBCircuit_implements := subInPlaceMSBCircuit_implements
  ctrlAddInPlaceMSBCircuit := ctrlAddInPlaceMSBCircuit
  ctrlAddInPlaceMSBCircuit_size := ctrlAddInPlaceMSBCircuit_size
  ctrlAddInPlaceMSBCircuit_implements := ctrlAddInPlaceMSBCircuit_implements
  ctrlSubInPlaceMSBCircuit := ctrlSubInPlaceMSBCircuit
  ctrlSubInPlaceMSBCircuit_size := ctrlSubInPlaceMSBCircuit_size
  ctrlSubInPlaceMSBCircuit_implements := ctrlSubInPlaceMSBCircuit_implements
  ctrlAddConstInPlaceMSBCircuit := ctrlAddConstInPlaceMSBCircuit
  ctrlAddConstInPlaceMSBCircuit_size := ctrlAddConstInPlaceMSBCircuit_size
  ctrlAddConstInPlaceMSBCircuit_implements := ctrlAddConstInPlaceMSBCircuit_implements
  ctrlSubConstInPlaceMSBCircuit := ctrlSubConstInPlaceMSBCircuit
  ctrlSubConstInPlaceMSBCircuit_size := ctrlSubConstInPlaceMSBCircuit_size
  ctrlSubConstInPlaceMSBCircuit_implements := ctrlSubConstInPlaceMSBCircuit_implements
}⟩
