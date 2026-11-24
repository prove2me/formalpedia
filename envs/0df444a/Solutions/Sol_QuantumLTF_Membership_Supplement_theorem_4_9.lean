-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_4_9
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T04:37:45.181849+00:00
-- url     : https://prove2.me/submissions/beac1ba6-9b23-4e9f-8d6a-a9f6d662569a

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Supplement_majOracle
import Definitions.Def_QuantumLTF_Membership_Supplement_nonOracleDepth
import Theorems.Thm_QuantumLTF_Majority_krawtchouk_as_character_sum
import Theorems.Thm_QuantumLTF_Majority_krawtchouk_weighted_orthogonality
import Theorems.Thm_QuantumLTF_Majority_lemma_4_2_two_channel
import Theorems.Thm_QuantumLTF_Majority_normalized_intersection_sum
import Theorems.Thm_QuantumLTF_Majority_pointwise_correction_bound_to_log_energy

set_option autoImplicit false

namespace Thm49Primitives

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! ### 1. LSB Binary Encoding Helpers -/

def natToBitsLSB (ℓ val : ℕ) : Qubits ℓ := fun j => val.testBit j.val

def bitsToNatLSB {ℓ : ℕ} (v : Qubits ℓ) : ℕ :=
  ∑ j : Fin ℓ, if v j then 2 ^ j.val else 0

lemma bitsToNatLSB_lt (ℓ : ℕ) (v : Qubits ℓ) : bitsToNatLSB v < 2 ^ ℓ := by
  induction ℓ with
  | zero => simp [bitsToNatLSB]
  | succ ℓ ih =>
    simp only [bitsToNatLSB, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    have hinit : (∑ i : Fin ℓ, if v i.castSucc then 2 ^ i.val else 0) < 2 ^ ℓ :=
      ih (fun i => v i.castSucc)
    have hlast : (if v (Fin.last ℓ) then 2 ^ ℓ else 0) ≤ 2 ^ ℓ := by split_ifs <;> omega
    rw [pow_succ']
    omega

lemma natToBitsLSB_zero (ℓ : ℕ) : natToBitsLSB ℓ 0 = fun _ => false := by
  funext j
  simp [natToBitsLSB]

lemma natToBitsLSB_testBit1 {ℓ t : ℕ} (h1 : 1 < ℓ) :
    natToBitsLSB ℓ t ⟨1, h1⟩ = decide (t % 4 = 2 ∨ t % 4 = 3) := by
  simp only [natToBitsLSB]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h4 : t = 4 * (t / 4) + t % 4 := (Nat.div_add_mod t 4).symm
  have ht2 : t / 2 = 2 * (t / 4) + (t % 4) / 2 := by omega
  have hlt : t % 4 < 4 := Nat.mod_lt t (by norm_num)
  have hpow : (2 : ℕ) ^ 1 = 2 := by norm_num
  rw [hpow, ht2]
  rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3) with hr | hr | hr | hr <;>
  · rw [hr]; simp

lemma natToBitsLSB_bitsToNatLSB {ℓ : ℕ} (v : Qubits ℓ) :
    natToBitsLSB ℓ (bitsToNatLSB v) = v := by
  induction ℓ with
  | zero =>
    funext j
    exact Fin.elim0 j
  | succ ℓ ih =>
    funext j
    simp only [natToBitsLSB, bitsToNatLSB, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    set a := ∑ i : Fin ℓ, if v i.castSucc then 2 ^ i.val else 0
    have ha : a < 2 ^ ℓ := bitsToNatLSB_lt ℓ (fun i => v i.castSucc)
    refine Fin.lastCases ?_ ?_ j
    · simp only [Fin.val_last]
      rw [Nat.testBit_eq_decide_div_mod_eq]
      cases hv : v (Fin.last ℓ)
      · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        have hdiv : a / 2 ^ ℓ = 0 := Nat.div_eq_of_lt ha
        simp [hdiv]
      · simp only [↓reduceIte]
        have hdiv : (a + 2 ^ ℓ) / 2 ^ ℓ = 1 := by
          rw [Nat.add_div_right _ (Nat.two_pow_pos ℓ), Nat.div_eq_of_lt ha]
        simp [hdiv]
    · intro i
      simp only [Fin.val_castSucc]
      have hi : i.val < ℓ := i.isLt
      have hmod_add : (a + (if v (Fin.last ℓ) then 2 ^ ℓ else 0)) % 2 ^ ℓ = a := by
        split_ifs
        · rw [Nat.add_mod_right, Nat.mod_eq_of_lt ha]
        · rw [add_zero, Nat.mod_eq_of_lt ha]
      have htb_mod : ∀ x : ℕ, (x % 2 ^ ℓ).testBit i.val = x.testBit i.val := by
        intro x
        rw [Nat.testBit_mod_two_pow]
        simp [hi]
      rw [← htb_mod (a + (if v (Fin.last ℓ) then 2 ^ ℓ else 0)), hmod_add]
      exact congrFun (ih (fun k => v k.castSucc)) i

lemma bitsToNatLSB_natToBitsLSB {ℓ val : ℕ} (h : val < 2 ^ ℓ) :
    bitsToNatLSB (natToBitsLSB ℓ val) = val := by
  induction ℓ generalizing val with
  | zero =>
    simp only [pow_zero] at h
    have : val = 0 := by omega
    subst this
    simp [bitsToNatLSB]
  | succ ℓ ih =>
    simp only [bitsToNatLSB, natToBitsLSB, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    have hmod_lt : val % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt val (Nat.two_pow_pos ℓ)
    have hih := ih hmod_lt
    have hleft : (∑ i : Fin ℓ, if natToBitsLSB (ℓ + 1) val i.castSucc then 2 ^ i.val else 0) = val % 2 ^ ℓ := by
      rw [← hih]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : i.val < ℓ := i.isLt
      have htb : val.testBit i.val = (val % 2 ^ ℓ).testBit i.val := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi]
      simp only [natToBitsLSB, Fin.val_castSucc]
      by_cases hc : val.testBit i.val <;> simp [hc, htb.symm]
    change (∑ i : Fin ℓ, if natToBitsLSB (ℓ + 1) val i.castSucc then 2 ^ i.val else 0) +
      (if val.testBit ℓ then 2 ^ ℓ else 0) = val
    rw [hleft]
    have hdiv_lt : val / 2 ^ ℓ < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos ℓ)]
      simpa [pow_succ'] using h
    have hbit : val.testBit ℓ = decide (val / 2 ^ ℓ = 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have : (val / 2 ^ ℓ) % 2 = val / 2 ^ ℓ := Nat.mod_eq_of_lt hdiv_lt
      rw [this]
    rw [hbit]
    have hdecomp := (Nat.div_add_mod val (2 ^ ℓ)).symm
    by_cases h0 : val / 2 ^ ℓ = 0
    · simp only [h0, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [h0, mul_zero, zero_add] at hdecomp
      exact hdecomp.symm
    · have h1 : val / 2 ^ ℓ = 1 :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp hdiv_lt) (Nat.pos_of_ne_zero h0)
      simp only [h1, decide_true, ↓reduceIte]
      rw [h1, mul_one] at hdecomp
      linarith [hdecomp]

lemma natToBitsLSB_inj {ℓ a b : ℕ} (ha : a < 2 ^ ℓ) (hb : b < 2 ^ ℓ)
    (h : natToBitsLSB ℓ a = natToBitsLSB ℓ b) : a = b := by
  have := congrArg bitsToNatLSB h
  rwa [bitsToNatLSB_natToBitsLSB ha, bitsToNatLSB_natToBitsLSB hb] at this

/-! ### 2. `OracleCircuit` & `nonOracleDepth` Composition Lemmas -/

def stepWires {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ} :
    OracleStep S a m → Finset (Fin m)
  | .gate g => Finset.univ.image g.wires
  | .query _ _ ctl wires _ =>
      Finset.univ.image wires ∪ (match ctl with | none => ∅ | some c => {c})

def stepCost {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ} : OracleStep S a m → ℕ
  | .gate _ => 1
  | .query _ _ _ _ _ => 0

def stepTime {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (st : OracleStep S a m) (τ : Fin m → ℕ) : Fin m → ℕ :=
  let t := (stepWires st).sup τ + stepCost st
  fun j => if j ∈ stepWires st then t else τ j

def foldTimes {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) (τ₀ : Fin m → ℕ) : Fin m → ℕ :=
  c.foldl (fun τ st => stepTime st τ) τ₀

lemma nonOracleDepth_eq_sup_foldTimes {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) :
    nonOracleDepth c = Finset.univ.sup (foldTimes c (fun _ => 0)) := rfl

lemma foldTimes_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c1 c2 : OracleCircuit S a m) (τ₀ : Fin m → ℕ) :
    foldTimes (c1 ++ c2) τ₀ = foldTimes c2 (foldTimes c1 τ₀) := by
  simp [foldTimes, List.foldl_append]

lemma stepTime_mono {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (st : OracleStep S a m) {τ₁ τ₂ : Fin m → ℕ} (h : ∀ j, τ₁ j ≤ τ₂ j) :
    ∀ j, stepTime st τ₁ j ≤ stepTime st τ₂ j := by
  intro j
  simp only [stepTime]
  split_ifs
  · exact Nat.add_le_add_right (Finset.sup_mono_fun fun i _ => h i) _
  · exact h j

lemma stepTime_add_const {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (st : OracleStep S a m) (τ : Fin m → ℕ) (B : ℕ) :
    ∀ j, stepTime st (fun i => τ i + B) j ≤ stepTime st τ j + B := by
  intro j
  simp only [stepTime]
  split_ifs
  · have hsup : (stepWires st).sup (fun i => τ i + B) ≤ (stepWires st).sup τ + B := by
      apply Finset.sup_le
      intro i hi
      exact Nat.add_le_add_right (Finset.le_sup hi) B
    omega
  · exact le_rfl

lemma foldTimes_le_add {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) {τ₀ τ₁ : Fin m → ℕ} {B : ℕ}
    (h : ∀ j, τ₀ j ≤ τ₁ j + B) :
    ∀ j, foldTimes c τ₀ j ≤ foldTimes c τ₁ j + B := by
  induction c generalizing τ₀ τ₁ with
  | nil => exact h
  | cons st rest ih =>
    intro j
    simp only [foldTimes, List.foldl_cons]
    apply ih
    intro k
    calc stepTime st τ₀ k
        ≤ stepTime st (fun i => τ₁ i + B) k := stepTime_mono st h k
      _ ≤ stepTime st τ₁ k + B := stepTime_add_const st τ₁ B k

theorem nonOracleDepth_nil {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ} :
    nonOracleDepth ([] : OracleCircuit S a m) = 0 := by
  simp [nonOracleDepth]

theorem nonOracleDepth_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c1 c2 : OracleCircuit S a m) :
    nonOracleDepth (c1 ++ c2) ≤ nonOracleDepth c1 + nonOracleDepth c2 := by
  rw [nonOracleDepth_eq_sup_foldTimes, foldTimes_append]
  apply Finset.sup_le
  intro j _
  have hstart : ∀ i : Fin m, foldTimes c1 (fun _ => 0) i ≤ (fun _ => 0) i + nonOracleDepth c1 := by
    intro i
    rw [zero_add, nonOracleDepth_eq_sup_foldTimes]
    exact Finset.le_sup (Finset.mem_univ i)
  have hle := foldTimes_le_add c2 hstart j
  have hc2 : foldTimes c2 (fun _ => 0) j ≤ nonOracleDepth c2 := by
    rw [nonOracleDepth_eq_sup_foldTimes]
    exact Finset.le_sup (Finset.mem_univ j)
  omega

theorem nonOracleDepth_query_single {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (k : Fin r) (adj : Bool) (ctl : Option (Fin m)) (wires : Fin (a k) ↪ Fin m)
    (hc : ∀ c, ctl = some c → c ∉ Set.range wires) :
    nonOracleDepth ([OracleStep.query k adj ctl wires hc] : OracleCircuit S a m) = 0 := by
  simp [nonOracleDepth]

theorem nonOracleDepth_append_query {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) (k : Fin r) (adj : Bool) (ctl : Option (Fin m))
    (wires : Fin (a k) ↪ Fin m) (hc : ∀ c, ctl = some c → c ∉ Set.range wires) :
    nonOracleDepth (c ++ [OracleStep.query k adj ctl wires hc]) ≤ nonOracleDepth c := by
  calc nonOracleDepth (c ++ [OracleStep.query k adj ctl wires hc])
      ≤ nonOracleDepth c + nonOracleDepth [OracleStep.query k adj ctl wires hc] :=
        nonOracleDepth_append _ _
    _ = nonOracleDepth c := by rw [nonOracleDepth_query_single, add_zero]

def LayerDisjoint {S : Set Gate} {m : ℕ} (L : List (GateApp S m)) : Prop :=
  L.Pairwise fun g h => Disjoint (Set.range g.wires) (Set.range h.wires)

private lemma foldTimes_parallelLayer_le {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (L : List (GateApp S m)) (hL : LayerDisjoint L) (τ : Fin m → ℕ) (B : ℕ)
    (hτ : ∀ j, τ j ≤ B + 1)
    (hLτ : ∀ g ∈ L, ∀ j ∈ Finset.univ.image g.wires, τ j ≤ B) :
    ∀ j, foldTimes (L.map (OracleStep.gate (r := r) (a := a))) τ j ≤ B + 1 := by
  induction L generalizing τ with
  | nil => exact hτ
  | cons g rest ih =>
    rw [List.map_cons]
    simp only [foldTimes, List.foldl_cons]
    rw [LayerDisjoint, List.pairwise_cons] at hL
    apply ih hL.2
    · intro j
      by_cases hj : j ∈ Finset.univ.image g.wires
      · have hsup : (Finset.univ.image g.wires).sup τ ≤ B :=
          Finset.sup_le fun i hi => hLτ g List.mem_cons_self i hi
        simp only [stepTime, stepWires, stepCost, hj, ↓reduceIte]
        omega
      · simp only [stepTime, stepWires, hj, ↓reduceIte]
        exact hτ j
    · intro h hmem j hj
      have hdisj := hL.1 h hmem
      have hj_not : j ∉ Finset.univ.image g.wires := by
        intro hjg
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj hjg
        rcases hj with ⟨a1, rfl⟩
        rcases hjg with ⟨a2, ha2⟩
        exact Set.disjoint_left.mp hdisj ⟨a2, ha2⟩ ⟨a1, rfl⟩
      simp only [stepTime, stepWires, hj_not, ↓reduceIte]
      exact hLτ h (List.mem_cons_of_mem g hmem) j hj

theorem nonOracleDepth_parallelLayer {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (L : List (GateApp S m)) (hL : LayerDisjoint L) :
    nonOracleDepth (L.map (OracleStep.gate (r := r) (a := a))) ≤ 1 := by
  rw [nonOracleDepth_eq_sup_foldTimes]
  apply Finset.sup_le
  intro j _
  exact foldTimes_parallelLayer_le L hL (fun _ => 0) 0 (fun _ => Nat.le_add_left _ _)
    (fun _ _ _ _ => Nat.zero_le _) j

/-! ### 3. Circuit & OracleCircuit Algebraic Helpers -/

lemma circuit_unitary_nil {S : Set Gate} {n : ℕ} :
    Circuit.unitary ([] : Circuit S n) = 1 := by
  simp [Circuit.unitary]

lemma circuit_unitary_cons {S : Set Gate} {n : ℕ} (g : GateApp S n) (c : Circuit S n) :
    Circuit.unitary (g :: c) = Circuit.unitary c * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

lemma circuit_unitary_append {S : Set Gate} {n : ℕ} (c1 c2 : Circuit S n) :
    Circuit.unitary (c1 ++ c2) = Circuit.unitary c2 * Circuit.unitary c1 := by
  simp [Circuit.unitary]

lemma oracleCircuit_unitary_nil {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary ([] : OracleCircuit S a n) orc = 1 := by
  simp [OracleCircuit.unitary]

lemma oracleCircuit_unitary_cons {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (st : OracleStep S a n) (c : OracleCircuit S a n)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary (st :: c) orc = OracleCircuit.unitary c orc * OracleStep.mat orc st := by
  simp [OracleCircuit.unitary]

lemma oracleCircuit_unitary_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c1 c2 : OracleCircuit S a n) (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary (c1 ++ c2) orc =
      OracleCircuit.unitary c2 orc * OracleCircuit.unitary c1 orc := by
  simp [OracleCircuit.unitary]

lemma oracleCircuit_queryCount_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c1 c2 : OracleCircuit S a n) (k : Fin r) :
    (c1 ++ c2).queryCount k = c1.queryCount k + c2.queryCount k := by
  simp [OracleCircuit.queryCount, List.countP_append]

lemma oracleCircuit_gateCount_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c1 c2 : OracleCircuit S a n) :
    (c1 ++ c2).gateCount = c1.gateCount + c2.gateCount := by
  simp [OracleCircuit.gateCount, List.countP_append]

lemma oracleCircuit_map_gate_unitary {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : Circuit S n) (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary (c.map (OracleStep.gate (r := r) (a := a))) orc = c.unitary := by
  simp only [OracleCircuit.unitary, Circuit.unitary, List.map_map]
  rfl

lemma oracleCircuit_map_gate_queryCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : Circuit S n) (k : Fin r) :
    OracleCircuit.queryCount (c.map (OracleStep.gate (r := r) (a := a))) k = 0 := by
  induction c with
  | nil => simp [OracleCircuit.queryCount]
  | cons g rest ih =>
    simp only [List.map_cons, OracleCircuit.queryCount, List.countP_cons, OracleStep.IsQueryTo,
      Bool.false_eq_true, ↓reduceIte, add_zero] at ih ⊢
    exact ih

lemma oracleCircuit_map_gate_gateCount {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ}
    (c : Circuit S n) :
    OracleCircuit.gateCount (c.map (OracleStep.gate (r := r) (a := a))) = c.length := by
  induction c with
  | nil => simp [OracleCircuit.gateCount]
  | cons g rest ih =>
    simp only [List.map_cons, OracleCircuit.gateCount, List.countP_cons, List.length_cons] at ih ⊢
    exact congrArg (· + 1) ih

/-! ### 4. `embedOp` Algebra, Commutation & Action Helpers -/

lemma act_add {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act U (ψ + φ) = act U ψ + act U φ := by
  ext y; simp [act, Matrix.mulVec_add]

lemma act_sub {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act U (ψ - φ) = act U ψ - act U φ := by
  ext y; simp [act, Matrix.mulVec_sub]

lemma act_smul {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act U (c • ψ) = c • act U ψ := by
  ext y; simp [act, Matrix.mulVec_smul]

lemma act_sum {ι κ : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ ι) :
    act U (∑ x ∈ s, f x) = ∑ x ∈ s, act U (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext y; simp [act]
  | insert a s ha ih => rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext y; simp [act, Matrix.mulVec_mulVec]

lemma act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  simp [act]

lemma act_ket_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (z : ι) :
    act M (ket z) = ∑ y : ι, M y z • ket y := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single z, Finset.sum_eq_single y]
  · simp
  · intro x _ hx; simp [hx.symm]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

def permMat {ι : Type*} [DecidableEq ι] (f : ι → ι) : Matrix ι ι ℂ :=
  Matrix.of fun y z => if y = f z then 1 else 0

lemma act_permMat_ket {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ι) (z : ι) :
    act (permMat f) (ket z) = ket (f z) := by
  rw [act_ket_eq, Finset.sum_eq_single (f z)]
  · simp [permMat]
  · intro y _ hy; simp [permMat, hy]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma permMat_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ι} (hf : Function.Bijective f) :
    permMat f ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext x y
  simp only [Matrix.mul_apply, Matrix.star_apply, permMat, Matrix.of_apply, Matrix.one_apply]
  obtain ⟨u, hu⟩ := hf.surjective x
  rw [Finset.sum_eq_single u]
  · by_cases hxy : x = y
    · subst hxy; simp [hu]
    · have hne : y ≠ f u := fun h => hxy (hu.symm.trans h.symm)
      simp [hu, hxy, ne_comm.mp hxy]
  · intro z _ hz
    have hzx : x ≠ f z := fun h => hz (hf.injective (h.symm.trans hu.symm))
    simp [hzx]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma embedOp_star {k n : ℕ} (A : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (star A) w = star (embedOp A w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.star_apply]
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · have h' : ∀ a : Fin n, a ∉ Set.range w → z a = y a := fun a ha => (h a ha).symm
    rw [if_pos h, if_pos h']
  · have h' : ¬ ∀ a : Fin n, a ∉ Set.range w → z a = y a := fun hzy =>
      h (fun a ha => (hzy a ha).symm)
    rw [if_neg h, if_neg h', star_zero]

private noncomputable def splitQubits {k n : ℕ} (w : Fin k ↪ Fin n) (y₀ : Qubits n) :
    Qubits k ↪ Qubits n where
  toFun v a :=
    open Classical in
    if h : ∃ i, w i = a then v (Classical.choose h) else y₀ a
  inj' v1 v2 hv := by
    classical
    funext i
    have hi := congrFun hv (w i)
    have hmem : ∃ j, w j = w i := ⟨i, rfl⟩
    change (if h : ∃ j, w j = w i then v1 (Classical.choose h) else y₀ (w i)) =
      (if h : ∃ j, w j = w i then v2 (Classical.choose h) else y₀ (w i)) at hi
    rw [dif_pos hmem, dif_pos hmem, w.injective (Classical.choose_spec hmem)] at hi
    exact hi

private lemma splitQubits_comp {k n : ℕ} (w : Fin k ↪ Fin n) (y₀ : Qubits n) (v : Qubits k) :
    splitQubits w y₀ v ∘ w = v := by
  classical
  funext i
  have hmem : ∃ j, w j = w i := ⟨i, rfl⟩
  change (if h : ∃ j, w j = w i then v (Classical.choose h) else y₀ (w i)) = v i
  rw [dif_pos hmem, w.injective (Classical.choose_spec hmem)]

private lemma splitQubits_off {k n : ℕ} (w : Fin k ↪ Fin n) (y₀ : Qubits n) (v : Qubits k)
    {a : Fin n} (ha : a ∉ Set.range w) :
    splitQubits w y₀ v a = y₀ a := by
  classical
  have hnot : ¬ ∃ i, w i = a := ha
  change (if h : ∃ i, w i = a then v (Classical.choose h) else y₀ a) = y₀ a
  rw [dif_neg hnot]

private lemma eq_splitQubits_of_agree {k n : ℕ} (w : Fin k ↪ Fin n) {y₀ x : Qubits n}
    (hx : ∀ a : Fin n, a ∉ Set.range w → y₀ a = x a) :
    x = splitQubits w y₀ (x ∘ w) := by
  classical
  funext a
  by_cases ha : a ∈ Set.range w
  · have hmem : ∃ i, w i = a := ha
    change x a = if h : ∃ i, w i = a then (x ∘ w) (Classical.choose h) else y₀ a
    rw [dif_pos hmem, Function.comp_apply, Classical.choose_spec hmem]
  · rw [splitQubits_off w y₀ _ ha, hx a ha]

lemma embedOp_mul {k n : ℕ} (A B : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  classical
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    have hsum : (∑ x : Qubits n,
        (if ∀ a, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
        (if ∀ a, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0)) =
        ∑ x ∈ Finset.univ.image (splitQubits w y),
        (if ∀ a, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
        (if ∀ a, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro x _ hx
      by_cases hyx : ∀ a, a ∉ Set.range w → y a = x a
      · exfalso; apply hx
        rw [Finset.mem_image]
        exact ⟨x ∘ w, Finset.mem_univ _, (eq_splitQubits_of_agree w hyx).symm⟩
      · rw [if_neg hyx, zero_mul]
    rw [hsum, Finset.sum_image (fun v1 _ v2 _ h => (splitQubits w y).injective h)]
    refine Finset.sum_congr rfl fun v _ => ?_
    have h1 : ∀ a, a ∉ Set.range w → y a = splitQubits w y v a := fun a ha =>
      (splitQubits_off w y v ha).symm
    have h2 : ∀ a, a ∉ Set.range w → splitQubits w y v a = z a := fun a ha => by
      rw [splitQubits_off w y v ha, hyz a ha]
    rw [if_pos h1, if_pos h2, splitQubits_comp]
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : ∀ a, a ∉ Set.range w → y a = x a
    · have h2 : ¬ ∀ a, a ∉ Set.range w → x a = z a := fun hxz =>
        hyz fun a ha => (h1 a ha).trans (hxz a ha)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma embedOp_mem_unitaryGroup {k n : ℕ} {A : Matrix (Qubits k) (Qubits k) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp A w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, ← embedOp_star, ← embedOp_mul,
    Matrix.mem_unitaryGroup_iff.mp hA, embedOp_one]

lemma embedOp_embedOp {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w₁ : Fin k ↪ Fin m) (w₂ : Fin m ↪ Fin n) :
    embedOp (embedOp M w₁) w₂ = embedOp M (w₁.trans w₂) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range (w₁.trans w₂) → y a = z a) ↔
      (∀ a : Fin n, a ∉ Set.range w₂ → y a = z a) ∧
      (∀ b : Fin m, b ∉ Set.range w₁ → (y ∘ w₂) b = (z ∘ w₂) b) := by
    constructor
    · intro h
      refine ⟨fun a ha => h a ?_, fun b hb => h (w₂ b) ?_⟩
      · rintro ⟨i, rfl⟩; exact ha ⟨w₁ i, rfl⟩
      · rintro ⟨i, hi⟩; exact hb ⟨i, w₂.injective hi⟩
    · rintro ⟨h2, h1⟩ a ha
      by_cases ha2 : a ∈ Set.range w₂
      · rcases ha2 with ⟨b, rfl⟩
        apply h1 b
        rintro ⟨i, rfl⟩
        exact ha ⟨i, rfl⟩
      · exact h2 a ha2
  by_cases hall : ∀ a : Fin n, a ∉ Set.range (w₁.trans w₂) → y a = z a
  · rw [if_pos hall]
    obtain ⟨h2, h1⟩ := hiff.mp hall
    rw [if_pos h2, if_pos h1]
    rfl
  · rw [if_neg hall]
    by_cases h2 : ∀ a : Fin n, a ∉ Set.range w₂ → y a = z a
    · rw [if_pos h2]
      have h1 : ¬ ∀ b : Fin m, b ∉ Set.range w₁ → (y ∘ w₂) b = (z ∘ w₂) b := fun h1 =>
        hall (hiff.mpr ⟨h2, h1⟩)
      rw [if_neg h1]
    · rw [if_neg h2]

lemma embedOp_comm_of_disjoint {k₁ k₂ n : ℕ}
    (A : Matrix (Qubits k₁) (Qubits k₁) ℂ) (B : Matrix (Qubits k₂) (Qubits k₂) ℂ)
    (w₁ : Fin k₁ ↪ Fin n) (w₂ : Fin k₂ ↪ Fin n)
    (hdisj : Disjoint (Set.range w₁) (Set.range w₂)) :
    embedOp A w₁ * embedOp B w₂ = embedOp B w₂ * embedOp A w₁ := by
  classical
  ext y z
  simp only [Matrix.mul_apply, embedOp, Matrix.of_apply]
  by_cases hout : ∀ a : Fin n, a ∉ Set.range w₁ → a ∉ Set.range w₂ → y a = z a
  · let x₁ : Qubits n := fun a => if a ∈ Set.range w₁ then z a else y a
    let x₂ : Qubits n := fun a => if a ∈ Set.range w₂ then z a else y a
    have hx₁_w1 : x₁ ∘ w₁ = z ∘ w₁ := by
      funext i
      change (if w₁ i ∈ Set.range w₁ then z (w₁ i) else y (w₁ i)) = z (w₁ i)
      rw [if_pos ⟨i, rfl⟩]
    have hx₁_w2 : x₁ ∘ w₂ = y ∘ w₂ := by
      funext i
      have hnot : w₂ i ∉ Set.range w₁ := Set.disjoint_right.mp hdisj ⟨i, rfl⟩
      change (if w₂ i ∈ Set.range w₁ then z (w₂ i) else y (w₂ i)) = y (w₂ i)
      rw [if_neg hnot]
    have hx₂_w2 : x₂ ∘ w₂ = z ∘ w₂ := by
      funext i
      change (if w₂ i ∈ Set.range w₂ then z (w₂ i) else y (w₂ i)) = z (w₂ i)
      rw [if_pos ⟨i, rfl⟩]
    have hx₂_w1 : x₂ ∘ w₁ = y ∘ w₁ := by
      funext i
      have hnot : w₁ i ∉ Set.range w₂ := Set.disjoint_left.mp hdisj ⟨i, rfl⟩
      change (if w₁ i ∈ Set.range w₂ then z (w₁ i) else y (w₁ i)) = y (w₁ i)
      rw [if_neg hnot]
    have hL : (∑ x : Qubits n,
        (if ∀ a, a ∉ Set.range w₁ → y a = x a then A (y ∘ w₁) (x ∘ w₁) else 0) *
        (if ∀ a, a ∉ Set.range w₂ → x a = z a then B (x ∘ w₂) (z ∘ w₂) else 0)) =
        A (y ∘ w₁) (z ∘ w₁) * B (y ∘ w₂) (z ∘ w₂) := by
      rw [Finset.sum_eq_single x₁]
      · have h1 : ∀ a, a ∉ Set.range w₁ → y a = x₁ a := fun a ha => by
          change y a = if a ∈ Set.range w₁ then z a else y a
          rw [if_neg ha]
        have h2 : ∀ a, a ∉ Set.range w₂ → x₁ a = z a := fun a ha => by
          by_cases ha1 : a ∈ Set.range w₁
          · change (if a ∈ Set.range w₁ then z a else y a) = z a
            rw [if_pos ha1]
          · change (if a ∈ Set.range w₁ then z a else y a) = z a
            rw [if_neg ha1, hout a ha1 ha]
        rw [if_pos h1, if_pos h2, hx₁_w1, hx₁_w2]
      · intro x _ hx
        by_cases h1 : ∀ a, a ∉ Set.range w₁ → y a = x a
        · by_cases h2 : ∀ a, a ∉ Set.range w₂ → x a = z a
          · exfalso; apply hx
            funext a
            by_cases ha1 : a ∈ Set.range w₁
            · have ha2 : a ∉ Set.range w₂ := Set.disjoint_left.mp hdisj ha1
              change x a = if a ∈ Set.range w₁ then z a else y a
              rw [if_pos ha1, h2 a ha2]
            · change x a = if a ∈ Set.range w₁ then z a else y a
              rw [if_neg ha1, (h1 a ha1).symm]
          · rw [if_neg h2, mul_zero]
        · rw [if_neg h1, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR : (∑ x : Qubits n,
        (if ∀ a, a ∉ Set.range w₂ → y a = x a then B (y ∘ w₂) (x ∘ w₂) else 0) *
        (if ∀ a, a ∉ Set.range w₁ → x a = z a then A (x ∘ w₁) (z ∘ w₁) else 0)) =
        B (y ∘ w₂) (z ∘ w₂) * A (y ∘ w₁) (z ∘ w₁) := by
      rw [Finset.sum_eq_single x₂]
      · have h1 : ∀ a, a ∉ Set.range w₂ → y a = x₂ a := fun a ha => by
          change y a = if a ∈ Set.range w₂ then z a else y a
          rw [if_neg ha]
        have h2 : ∀ a, a ∉ Set.range w₁ → x₂ a = z a := fun a ha => by
          by_cases ha2 : a ∈ Set.range w₂
          · change (if a ∈ Set.range w₂ then z a else y a) = z a
            rw [if_pos ha2]
          · change (if a ∈ Set.range w₂ then z a else y a) = z a
            rw [if_neg ha2, hout a ha ha2]
        rw [if_pos h1, if_pos h2, hx₂_w2, hx₂_w1]
      · intro x _ hx
        by_cases h1 : ∀ a, a ∉ Set.range w₂ → y a = x a
        · by_cases h2 : ∀ a, a ∉ Set.range w₁ → x a = z a
          · exfalso; apply hx
            funext a
            by_cases ha2 : a ∈ Set.range w₂
            · have ha1 : a ∉ Set.range w₁ := Set.disjoint_right.mp hdisj ha2
              change x a = if a ∈ Set.range w₂ then z a else y a
              rw [if_pos ha2, h2 a ha1]
            · change x a = if a ∈ Set.range w₂ then z a else y a
              rw [if_neg ha2, (h1 a ha2).symm]
          · rw [if_neg h2, mul_zero]
        · rw [if_neg h1, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hL, hR, mul_comm]
  · push Not at hout
    rcases hout with ⟨a₀, ha1, ha2, hne⟩
    have hzero1 : (∑ x : Qubits n,
        (if ∀ a, a ∉ Set.range w₁ → y a = x a then A (y ∘ w₁) (x ∘ w₁) else 0) *
        (if ∀ a, a ∉ Set.range w₂ → x a = z a then B (x ∘ w₂) (z ∘ w₂) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases h1 : ∀ a, a ∉ Set.range w₁ → y a = x a
      · have h2 : ¬ ∀ a, a ∉ Set.range w₂ → x a = z a := fun hxz =>
          hne ((h1 a₀ ha1).trans (hxz a₀ ha2))
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    have hzero2 : (∑ x : Qubits n,
        (if ∀ a, a ∉ Set.range w₂ → y a = x a then B (y ∘ w₂) (x ∘ w₂) else 0) *
        (if ∀ a, a ∉ Set.range w₁ → x a = z a then A (x ∘ w₁) (z ∘ w₁) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases h1 : ∀ a, a ∉ Set.range w₂ → y a = x a
      · have h2 : ¬ ∀ a, a ∉ Set.range w₁ → x a = z a := fun hxz =>
          hne ((h1 a₀ ha2).trans (hxz a₀ ha1))
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [hzero1, hzero2]

/-! ### 5. `LayeredCircuit` & `ImplementsOnClean` -/

def GateApp.adj {m : ℕ} (g : GateApp gates12 m) : GateApp gates12 m where
  gate := ⟨g.gate.arity, star g.gate.mat⟩
  mem := by
    rcases g.mem with ⟨hu, h1, h2⟩
    refine ⟨?_, h1, h2⟩
    exact Unitary.star_mem hu
  wires := g.wires

def GateApp.mapWires {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (g : GateApp gates12 m₀) :
    GateApp gates12 m where
  gate := g.gate
  mem := g.mem
  wires := g.wires.trans emb

lemma GateApp.unitary_mem_unitaryGroup {m : ℕ} (g : GateApp gates12 m) :
    embedOp g.gate.mat g.wires ∈ Matrix.unitaryGroup (Qubits m) ℂ :=
  embedOp_mem_unitaryGroup g.mem.1 g.wires

lemma circuit_unitary_mem_unitaryGroup {m : ℕ} (c : Circuit gates12 m) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits m) ℂ := by
  induction c with
  | nil =>
    rw [circuit_unitary_nil]
    exact one_mem _
  | cons g rest ih =>
    rw [circuit_unitary_cons]
    exact mul_mem ih (GateApp.unitary_mem_unitaryGroup g)

structure LayeredCircuit (m : ℕ) where
  layers : List (List (GateApp gates12 m))
  disjoint : ∀ L ∈ layers, LayerDisjoint L

namespace LayeredCircuit

def toCircuit {m : ℕ} (lc : LayeredCircuit m) : Circuit gates12 m :=
  lc.layers.flatten

def size {m : ℕ} (lc : LayeredCircuit m) : ℕ :=
  lc.toCircuit.length

def depth {m : ℕ} (lc : LayeredCircuit m) : ℕ :=
  lc.layers.length

noncomputable def unitary {m : ℕ} (lc : LayeredCircuit m) : Matrix (Qubits m) (Qubits m) ℂ :=
  lc.toCircuit.unitary

def UsesOnly {m : ℕ} (lc : LayeredCircuit m) (S : Finset (Fin m)) : Prop :=
  ∀ L ∈ lc.layers, ∀ g ∈ L, ∀ i : Fin g.gate.arity, g.wires i ∈ S

lemma UsesOnly.mono {m : ℕ} {lc : LayeredCircuit m} {S₁ S₂ : Finset (Fin m)}
    (h : lc.UsesOnly S₁) (hsub : S₁ ⊆ S₂) : lc.UsesOnly S₂ :=
  fun L hL g hg i => hsub (h L hL g hg i)

lemma unitary_mem_unitaryGroup {m : ℕ} (lc : LayeredCircuit m) :
    lc.unitary ∈ Matrix.unitaryGroup (Qubits m) ℂ :=
  circuit_unitary_mem_unitaryGroup lc.toCircuit

lemma nonOracleDepth_le {r : ℕ} {a : Fin r → ℕ} {m : ℕ} (lc : LayeredCircuit m) :
    nonOracleDepth (lc.toCircuit.map (OracleStep.gate (r := r) (a := a))) ≤ lc.depth := by
  rcases lc with ⟨layers, hdisj⟩
  dsimp only [toCircuit, depth]
  induction layers with
  | nil => simp [nonOracleDepth_nil]
  | cons L rest ih =>
    simp only [List.flatten_cons, List.map_append, List.length_cons]
    have hL : nonOracleDepth (L.map (OracleStep.gate (r := r) (a := a))) ≤ 1 :=
      nonOracleDepth_parallelLayer L (hdisj L List.mem_cons_self)
    have hrest : nonOracleDepth (rest.flatten.map (OracleStep.gate (r := r) (a := a))) ≤ rest.length :=
      ih fun L' hL' => hdisj L' (List.mem_cons_of_mem L hL')
    calc nonOracleDepth (L.map OracleStep.gate ++ rest.flatten.map OracleStep.gate)
        ≤ nonOracleDepth (L.map OracleStep.gate) + nonOracleDepth (rest.flatten.map OracleStep.gate) :=
          nonOracleDepth_append _ _
      _ ≤ 1 + rest.length := Nat.add_le_add hL hrest
      _ = rest.length + 1 := Nat.add_comm _ _

def id (m : ℕ) : LayeredCircuit m where
  layers := []
  disjoint _ h := by contradiction

@[simp] lemma id_size {m : ℕ} : (id m).size = 0 := rfl
@[simp] lemma id_depth {m : ℕ} : (id m).depth = 0 := rfl
@[simp] lemma id_unitary {m : ℕ} : (id m).unitary = 1 := by
  simp [unitary, toCircuit, id, Circuit.unitary]
lemma id_usesOnly {m : ℕ} (S : Finset (Fin m)) : (id m).UsesOnly S := by
  intro L h; cases h

def single {m : ℕ} (g : GateApp gates12 m) : LayeredCircuit m where
  layers := [[g]]
  disjoint L h := by
    simp only [List.mem_singleton] at h
    subst h
    simp [LayerDisjoint]

@[simp] lemma single_size {m : ℕ} (g : GateApp gates12 m) : (single g).size = 1 := rfl
@[simp] lemma single_depth {m : ℕ} (g : GateApp gates12 m) : (single g).depth = 1 := rfl
@[simp] lemma single_unitary {m : ℕ} (g : GateApp gates12 m) :
    (single g).unitary = embedOp g.gate.mat g.wires := by
  simp [unitary, toCircuit, single, Circuit.unitary]
lemma single_usesOnly {m : ℕ} (g : GateApp gates12 m) {S : Finset (Fin m)}
    (h : ∀ i, g.wires i ∈ S) : (single g).UsesOnly S := by
  intro L hL g' hg'
  simp only [single, List.mem_singleton] at hL hg'
  subst hL
  rw [List.mem_singleton] at hg'
  subst hg'
  exact h

def ofLayer {m : ℕ} (L : List (GateApp gates12 m)) (hL : LayerDisjoint L) : LayeredCircuit m where
  layers := if L.isEmpty then [] else [L]
  disjoint L' hL' := by
    split_ifs at hL'
    · cases hL'
    · simp only [List.mem_singleton] at hL'
      subst hL'
      exact hL

lemma ofLayer_size {m : ℕ} (L : List (GateApp gates12 m)) (hL : LayerDisjoint L) :
    (ofLayer L hL).size = L.length := by
  dsimp [ofLayer, size, toCircuit]
  split_ifs with h
  · rw [List.isEmpty_iff] at h; subst h; rfl
  · simp

lemma ofLayer_depth {m : ℕ} (L : List (GateApp gates12 m)) (hL : LayerDisjoint L) :
    (ofLayer L hL).depth ≤ 1 := by
  dsimp [ofLayer, depth]
  split_ifs <;> simp

lemma ofLayer_unitary {m : ℕ} (L : List (GateApp gates12 m)) (hL : LayerDisjoint L) :
    (ofLayer L hL).unitary = Circuit.unitary L := by
  dsimp [ofLayer, unitary, toCircuit]
  split_ifs with h
  · rw [List.isEmpty_iff] at h; subst h; simp [Circuit.unitary]
  · simp [Circuit.unitary]

lemma ofLayer_usesOnly {m : ℕ} (L : List (GateApp gates12 m)) (hL : LayerDisjoint L)
    {S : Finset (Fin m)} (h : ∀ g ∈ L, ∀ i, g.wires i ∈ S) : (ofLayer L hL).UsesOnly S := by
  intro L' hL'
  dsimp [ofLayer] at hL'
  split_ifs at hL'
  · cases hL'
  · simp only [List.mem_singleton] at hL'
    subst hL'
    exact h

def seq {m : ℕ} (lc1 lc2 : LayeredCircuit m) : LayeredCircuit m where
  layers := lc1.layers ++ lc2.layers
  disjoint L hL := by
    rcases List.mem_append.mp hL with h1 | h2
    · exact lc1.disjoint L h1
    · exact lc2.disjoint L h2

@[simp] lemma seq_size {m : ℕ} (lc1 lc2 : LayeredCircuit m) :
    (lc1.seq lc2).size = lc1.size + lc2.size := by
  simp [seq, size, toCircuit]

@[simp] lemma seq_depth {m : ℕ} (lc1 lc2 : LayeredCircuit m) :
    (lc1.seq lc2).depth = lc1.depth + lc2.depth := by
  simp [seq, depth]

@[simp] lemma seq_unitary {m : ℕ} (lc1 lc2 : LayeredCircuit m) :
    (lc1.seq lc2).unitary = lc2.unitary * lc1.unitary := by
  simp [seq, unitary, toCircuit, circuit_unitary_append]

lemma seq_usesOnly {m : ℕ} {lc1 lc2 : LayeredCircuit m} {S : Finset (Fin m)}
    (h1 : lc1.UsesOnly S) (h2 : lc2.UsesOnly S) : (lc1.seq lc2).UsesOnly S := by
  intro L hL
  rcases List.mem_append.mp hL with hL1 | hL2
  · exact h1 L hL1
  · exact h2 L hL2

def seqList {m : ℕ} : List (LayeredCircuit m) → LayeredCircuit m
  | [] => id m
  | lc :: rest => lc.seq (seqList rest)

lemma seqList_size {m : ℕ} (lcs : List (LayeredCircuit m)) :
    (seqList lcs).size = (lcs.map size).sum := by
  induction lcs with
  | nil => simp [seqList]
  | cons lc rest ih => simp [seqList, ih]

lemma seqList_depth {m : ℕ} (lcs : List (LayeredCircuit m)) :
    (seqList lcs).depth = (lcs.map depth).sum := by
  induction lcs with
  | nil => simp [seqList]
  | cons lc rest ih => simp [seqList, ih]

lemma seqList_unitary {m : ℕ} (lcs : List (LayeredCircuit m)) :
    (seqList lcs).unitary = (lcs.map unitary).reverse.prod := by
  induction lcs with
  | nil => simp [seqList]
  | cons lc rest ih => simp [seqList, ih]

lemma seqList_usesOnly {m : ℕ} {lcs : List (LayeredCircuit m)} {S : Finset (Fin m)}
    (h : ∀ lc ∈ lcs, lc.UsesOnly S) : (seqList lcs).UsesOnly S := by
  induction lcs with
  | nil => exact id_usesOnly S
  | cons lc rest ih =>
    exact seq_usesOnly (h lc List.mem_cons_self) (ih fun lc' hlc' => h lc' (List.mem_cons_of_mem _ hlc'))

def mapWires {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (lc : LayeredCircuit m₀) : LayeredCircuit m where
  layers := lc.layers.map (List.map (GateApp.mapWires emb))
  disjoint L hL := by
    simp only [List.mem_map] at hL
    rcases hL with ⟨L₀, hL₀, rfl⟩
    have hdisj := lc.disjoint L₀ hL₀
    dsimp only [LayerDisjoint] at hdisj ⊢
    rw [List.pairwise_map]
    refine hdisj.imp fun {g1 g2} h => ?_
    rw [Set.disjoint_left]
    rintro x ⟨i1, hi1⟩ ⟨i2, hi2⟩
    change emb (g1.wires i1) = x at hi1
    change emb (g2.wires i2) = x at hi2
    have hweq : g1.wires i1 = g2.wires i2 := emb.injective (hi1.trans hi2.symm)
    exact Set.disjoint_left.mp h ⟨i1, rfl⟩ ⟨i2, hweq.symm⟩

@[simp] lemma mapWires_size {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (lc : LayeredCircuit m₀) :
    (lc.mapWires emb).size = lc.size := by
  simp only [mapWires, size, toCircuit, List.length_flatten, List.map_map, Function.comp_def,
    List.length_map]

@[simp] lemma mapWires_depth {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (lc : LayeredCircuit m₀) :
    (lc.mapWires emb).depth = lc.depth := by
  simp [mapWires, depth]

lemma mapWires_unitary {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (lc : LayeredCircuit m₀) :
    (lc.mapWires emb).unitary = embedOp lc.unitary emb := by
  rcases lc with ⟨layers, hdisj⟩
  dsimp only [mapWires, unitary, toCircuit]
  have hflat : (layers.map (List.map (GateApp.mapWires emb))).flatten =
      layers.flatten.map (GateApp.mapWires emb) := by
    induction layers with
    | nil => rfl
    | cons L rest ih => simp
  rw [hflat]
  generalize layers.flatten = c
  induction c with
  | nil => simp [Circuit.unitary, embedOp_one]
  | cons g rest ih =>
    simp only [List.map_cons, circuit_unitary_cons, ih]
    have hg : embedOp (GateApp.mapWires emb g).gate.mat (GateApp.mapWires emb g).wires =
        embedOp (embedOp g.gate.mat g.wires) emb :=
      (embedOp_embedOp g.gate.mat g.wires emb).symm
    rw [hg, ← embedOp_mul]

lemma mapWires_usesOnly {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (lc : LayeredCircuit m₀)
    {S₀ : Finset (Fin m₀)} (h : lc.UsesOnly S₀) :
    (lc.mapWires emb).UsesOnly (S₀.image emb) := by
  intro L hL g hg i
  simp only [mapWires, List.mem_map] at hL
  rcases hL with ⟨L₀, hL₀, rfl⟩
  simp only [List.mem_map] at hg
  rcases hg with ⟨g₀, hg₀, rfl⟩
  exact Finset.mem_image_of_mem emb (h L₀ hL₀ g₀ hg₀ i)

private lemma list_reverse_map_star_prod {α : Type*} [Monoid α] [StarMul α] (xs : List α) :
    star xs.reverse.prod = (xs.map star).prod := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      star_mul, List.map_cons, ih]

def adj {m : ℕ} (lc : LayeredCircuit m) : LayeredCircuit m where
  layers := (lc.layers.reverse).map (fun L => (L.map GateApp.adj).reverse)
  disjoint L hL := by
    simp only [List.mem_map, List.mem_reverse] at hL
    rcases hL with ⟨L₀, hL₀, rfl⟩
    have hdisj := lc.disjoint L₀ hL₀
    dsimp only [LayerDisjoint] at hdisj ⊢
    rw [List.pairwise_reverse, List.pairwise_map]
    exact hdisj.imp fun h => h.symm

@[simp] lemma adj_size {m : ℕ} (lc : LayeredCircuit m) : lc.adj.size = lc.size := by
  simp only [adj, size, toCircuit]
  generalize lc.layers = layers
  induction layers with
  | nil => rfl
  | cons L rest ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.length_append, List.length_reverse, List.length_map] at ih ⊢
    omega

@[simp] lemma adj_depth {m : ℕ} (lc : LayeredCircuit m) : lc.adj.depth = lc.depth := by
  simp [adj, depth]

lemma adj_unitary {m : ℕ} (lc : LayeredCircuit m) : lc.adj.unitary = star lc.unitary := by
  dsimp only [adj, unitary, toCircuit]
  generalize lc.layers = layers
  have hflat : ((layers.reverse).map (fun L => (L.map GateApp.adj).reverse)).flatten =
      (layers.flatten.map GateApp.adj).reverse := by
    induction layers with
    | nil => rfl
    | cons L rest ih =>
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.map_append]
      rw [ih, List.reverse_append]
  rw [hflat]
  generalize layers.flatten = c
  simp only [Circuit.unitary, List.map_reverse, List.reverse_reverse, list_reverse_map_star_prod]
  congr 1
  induction c with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.map_cons]
    rw [ih, GateApp.adj, embedOp_star]

lemma adj_usesOnly {m : ℕ} {lc : LayeredCircuit m} {S : Finset (Fin m)}
    (h : lc.UsesOnly S) : lc.adj.UsesOnly S := by
  intro L hL g hg i
  simp only [adj, List.mem_map, List.mem_reverse] at hL
  rcases hL with ⟨L₀, hL₀, rfl⟩
  simp only [List.mem_reverse, List.mem_map] at hg
  rcases hg with ⟨g₀, hg₀, rfl⟩
  exact h L₀ hL₀ g₀ hg₀ i

/-! ### 6. Parallel Merge of Disjoint `LayeredCircuit`s -/

private lemma layerDisjoint_append {m : ℕ} {L1 L2 : List (GateApp gates12 m)}
    (h1 : LayerDisjoint L1) (h2 : LayerDisjoint L2)
    (h12 : ∀ g1 ∈ L1, ∀ g2 ∈ L2, Disjoint (Set.range g1.wires) (Set.range g2.wires)) :
    LayerDisjoint (L1 ++ L2) := by
  exact List.pairwise_append.mpr ⟨h1, h2, h12⟩

lemma circuit_comm_of_disjoint {m : ℕ} (c1 c2 : Circuit gates12 m)
    (h : ∀ g1 ∈ c1, ∀ g2 ∈ c2, Disjoint (Set.range g1.wires) (Set.range g2.wires)) :
    Circuit.unitary c1 * Circuit.unitary c2 = Circuit.unitary c2 * Circuit.unitary c1 := by
  induction c1 with
  | nil => simp [circuit_unitary_nil]
  | cons g1 rest1 ih =>
    rw [circuit_unitary_cons]
    have hrest : Circuit.unitary rest1 * Circuit.unitary c2 =
        Circuit.unitary c2 * Circuit.unitary rest1 :=
      ih fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b hb
    have hg1 : embedOp g1.gate.mat g1.wires * Circuit.unitary c2 =
        Circuit.unitary c2 * embedOp g1.gate.mat g1.wires := by
      have h1_c2 : ∀ g2 ∈ c2, Disjoint (Set.range g1.wires) (Set.range g2.wires) :=
        fun g2 hg2 => h g1 List.mem_cons_self g2 hg2
      clear ih hrest h
      induction c2 with
      | nil => simp [circuit_unitary_nil]
      | cons g2 rest2 ih2 =>
        rw [circuit_unitary_cons]
        have h12 := embedOp_comm_of_disjoint g1.gate.mat g2.gate.mat g1.wires g2.wires
          (h1_c2 g2 List.mem_cons_self)
        have h1r := ih2 fun b hb => h1_c2 b (List.mem_cons_of_mem g2 hb)
        calc embedOp g1.gate.mat g1.wires * (Circuit.unitary rest2 * embedOp g2.gate.mat g2.wires)
            = (embedOp g1.gate.mat g1.wires * Circuit.unitary rest2) *
                embedOp g2.gate.mat g2.wires := by rw [Matrix.mul_assoc]
          _ = (Circuit.unitary rest2 * embedOp g1.gate.mat g1.wires) *
                embedOp g2.gate.mat g2.wires := by rw [h1r]
          _ = Circuit.unitary rest2 *
                (embedOp g1.gate.mat g1.wires * embedOp g2.gate.mat g2.wires) := by
              rw [Matrix.mul_assoc]
          _ = Circuit.unitary rest2 *
                (embedOp g2.gate.mat g2.wires * embedOp g1.gate.mat g1.wires) := by rw [h12]
          _ = (Circuit.unitary rest2 * embedOp g2.gate.mat g2.wires) *
                embedOp g1.gate.mat g1.wires := by rw [Matrix.mul_assoc]
    calc (Circuit.unitary rest1 * embedOp g1.gate.mat g1.wires) * Circuit.unitary c2
        = Circuit.unitary rest1 * (embedOp g1.gate.mat g1.wires * Circuit.unitary c2) :=
          Matrix.mul_assoc _ _ _
      _ = Circuit.unitary rest1 * (Circuit.unitary c2 * embedOp g1.gate.mat g1.wires) := by
          rw [hg1]
      _ = (Circuit.unitary rest1 * Circuit.unitary c2) * embedOp g1.gate.mat g1.wires :=
          (Matrix.mul_assoc _ _ _).symm
      _ = (Circuit.unitary c2 * Circuit.unitary rest1) * embedOp g1.gate.mat g1.wires := by
          rw [hrest]
      _ = Circuit.unitary c2 * (Circuit.unitary rest1 * embedOp g1.gate.mat g1.wires) :=
          Matrix.mul_assoc _ _ _

private def zipLayers {m : ℕ} :
    List (List (GateApp gates12 m)) → List (List (GateApp gates12 m)) →
      List (List (GateApp gates12 m))
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x ++ y) :: zipLayers xs ys

private lemma zipLayers_length {m : ℕ}
    (xs ys : List (List (GateApp gates12 m))) :
    (zipLayers xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [zipLayers]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipLayers]
    | cons y ys => simp [zipLayers, ih, Nat.succ_max_succ]

private lemma zipLayers_flatten_length {m : ℕ}
    (xs ys : List (List (GateApp gates12 m))) :
    (zipLayers xs ys).flatten.length = xs.flatten.length + ys.flatten.length := by
  induction xs generalizing ys with
  | nil => simp [zipLayers]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipLayers]
    | cons y ys =>
      simp only [zipLayers, List.flatten_cons, List.length_append, ih]
      omega

private lemma zipLayers_mem {m : ℕ}
    {xs ys : List (List (GateApp gates12 m))} {L : List (GateApp gates12 m)}
    (hL : L ∈ zipLayers xs ys) :
    L ∈ xs ∨ L ∈ ys ∨ ∃ x ∈ xs, ∃ y ∈ ys, L = x ++ y := by
  induction xs generalizing ys with
  | nil => exact Or.inr (Or.inl hL)
  | cons x xs ih =>
    cases ys with
    | nil => exact Or.inl hL
    | cons y ys =>
      simp only [zipLayers, List.mem_cons] at hL
      rcases hL with rfl | hrest
      · exact Or.inr (Or.inr ⟨x, List.mem_cons_self, y, List.mem_cons_self, rfl⟩)
      · rcases ih hrest with h1 | h2 | ⟨x', hx', y', hy', rfl⟩
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h2))
        · exact Or.inr (Or.inr ⟨x', List.mem_cons_of_mem _ hx', y', List.mem_cons_of_mem _ hy', rfl⟩)

private lemma zipLayers_unitary {m : ℕ}
    (xs ys : List (List (GateApp gates12 m)))
    (hdisj : ∀ L1 ∈ xs, ∀ g1 ∈ L1, ∀ L2 ∈ ys, ∀ g2 ∈ L2,
      Disjoint (Set.range g1.wires) (Set.range g2.wires)) :
    Circuit.unitary (zipLayers xs ys).flatten =
      Circuit.unitary ys.flatten * Circuit.unitary xs.flatten := by
  induction xs generalizing ys with
  | nil => simp [zipLayers, circuit_unitary_nil]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipLayers, circuit_unitary_nil]
    | cons y ys =>
      simp only [zipLayers, List.flatten_cons, circuit_unitary_append]
      have hih : Circuit.unitary (zipLayers xs ys).flatten =
          Circuit.unitary ys.flatten * Circuit.unitary xs.flatten :=
        ih ys fun L1 hL1 g1 hg1 L2 hL2 g2 hg2 =>
          hdisj L1 (List.mem_cons_of_mem _ hL1) g1 hg1 L2 (List.mem_cons_of_mem _ hL2) g2 hg2
      rw [hih]
      have h_xs_y : Circuit.unitary xs.flatten * Circuit.unitary y =
          Circuit.unitary y * Circuit.unitary xs.flatten :=
        circuit_comm_of_disjoint xs.flatten y fun g1 hg1 g2 hg2 => by
          rw [List.mem_flatten] at hg1
          rcases hg1 with ⟨L1, hL1, hg1⟩
          exact hdisj L1 (List.mem_cons_of_mem _ hL1) g1 hg1 y List.mem_cons_self g2 hg2
      calc (Circuit.unitary ys.flatten * Circuit.unitary xs.flatten) *
            (Circuit.unitary y * Circuit.unitary x)
          = Circuit.unitary ys.flatten * (Circuit.unitary xs.flatten * Circuit.unitary y) *
              Circuit.unitary x := by simp only [Matrix.mul_assoc]
        _ = Circuit.unitary ys.flatten * (Circuit.unitary y * Circuit.unitary xs.flatten) *
              Circuit.unitary x := by rw [h_xs_y]
        _ = (Circuit.unitary ys.flatten * Circuit.unitary y) *
              (Circuit.unitary xs.flatten * Circuit.unitary x) := by simp only [Matrix.mul_assoc]

def parMerge {m : ℕ} (lc1 lc2 : LayeredCircuit m) {S1 S2 : Finset (Fin m)}
    (h1 : lc1.UsesOnly S1) (h2 : lc2.UsesOnly S2) (hdisj : Disjoint S1 S2) :
    LayeredCircuit m where
  layers := zipLayers lc1.layers lc2.layers
  disjoint L hL := by
    rcases zipLayers_mem hL with hL1 | hL2 | ⟨x, hx, y, hy, rfl⟩
    · exact lc1.disjoint L hL1
    · exact lc2.disjoint L hL2
    · refine layerDisjoint_append (lc1.disjoint x hx) (lc2.disjoint y hy) ?_
      intro g1 hg1 g2 hg2
      rw [Set.disjoint_left]
      rintro w ⟨i1, rfl⟩ ⟨i2, hi2⟩
      have hw1 : g1.wires i1 ∈ S1 := h1 x hx g1 hg1 i1
      have hw2 : g2.wires i2 ∈ S2 := h2 y hy g2 hg2 i2
      rw [← hi2] at hw1
      exact Finset.disjoint_left.mp hdisj hw1 hw2

lemma parMerge_size {m : ℕ} (lc1 lc2 : LayeredCircuit m) {S1 S2 : Finset (Fin m)}
    (h1 : lc1.UsesOnly S1) (h2 : lc2.UsesOnly S2) (hdisj : Disjoint S1 S2) :
    (parMerge lc1 lc2 h1 h2 hdisj).size = lc1.size + lc2.size :=
  zipLayers_flatten_length lc1.layers lc2.layers

lemma parMerge_depth {m : ℕ} (lc1 lc2 : LayeredCircuit m) {S1 S2 : Finset (Fin m)}
    (h1 : lc1.UsesOnly S1) (h2 : lc2.UsesOnly S2) (hdisj : Disjoint S1 S2) :
    (parMerge lc1 lc2 h1 h2 hdisj).depth = max lc1.depth lc2.depth :=
  zipLayers_length lc1.layers lc2.layers

lemma parMerge_unitary {m : ℕ} (lc1 lc2 : LayeredCircuit m) {S1 S2 : Finset (Fin m)}
    (h1 : lc1.UsesOnly S1) (h2 : lc2.UsesOnly S2) (hdisj : Disjoint S1 S2) :
    (parMerge lc1 lc2 h1 h2 hdisj).unitary = lc2.unitary * lc1.unitary := by
  apply zipLayers_unitary
  intro L1 hL1 g1 hg1 L2 hL2 g2 hg2
  rw [Set.disjoint_left]
  rintro w ⟨i1, rfl⟩ ⟨i2, hi2⟩
  have hw1 : g1.wires i1 ∈ S1 := h1 L1 hL1 g1 hg1 i1
  have hw2 : g2.wires i2 ∈ S2 := h2 L2 hL2 g2 hg2 i2
  rw [← hi2] at hw1
  exact Finset.disjoint_left.mp hdisj hw1 hw2

lemma parMerge_usesOnly {m : ℕ} (lc1 lc2 : LayeredCircuit m) {S1 S2 : Finset (Fin m)}
    (h1 : lc1.UsesOnly S1) (h2 : lc2.UsesOnly S2) (hdisj : Disjoint S1 S2) :
    (parMerge lc1 lc2 h1 h2 hdisj).UsesOnly (S1 ∪ S2) := by
  intro L hL g hg i
  rcases zipLayers_mem hL with hL1 | hL2 | ⟨x, hx, y, hy, rfl⟩
  · exact Finset.mem_union_left S2 (h1 L hL1 g hg i)
  · exact Finset.mem_union_right S1 (h2 L hL2 g hg i)
  · rcases List.mem_append.mp hg with hgx | hgy
    · exact Finset.mem_union_left S2 (h1 x hx g hgx i)
    · exact Finset.mem_union_right S1 (h2 y hy g hgy i)

/-! ### 7. `ImplementsOnClean` Specification & Composition -/

def ImplementsOnClean {main anc : ℕ} (lc : LayeredCircuit (main + anc))
    (U : Matrix (Qubits main) (Qubits main) ℂ) : Prop :=
  ∀ y z : Qubits (main + anc),
    (∀ j : Fin anc, z (Fin.natAdd main j) = false) →
    lc.unitary y z =
      if ∀ j : Fin anc, y (Fin.natAdd main j) = false then
        U (fun i => y (Fin.castAdd anc i)) (fun i => z (Fin.castAdd anc i))
      else 0

end LayeredCircuit

/-! ### 8. Elementary 1- and 2-Qubit Gates in `gates12` -/

private def qubits1EquivBool : Qubits 1 ≃ Bool where
  toFun b := b 0
  invFun x _ := x
  left_inv b := funext fun i => by fin_cases i; rfl
  right_inv _ := rfl

private def qubits2EquivProd : Qubits 2 ≃ Bool × Bool where
  toFun b := (b 0, b 1)
  invFun p := ![p.1, p.2]
  left_inv b := funext fun i => by fin_cases i <;> rfl
  right_inv p := by ext <;> rfl

lemma ofMatrix1_mem_gates12 {U : Matrix Bool Bool ℂ}
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    Gate.ofMatrix1 U ∈ gates12 := by
  refine ⟨?_, by simp [Gate.ofMatrix1], by simp [Gate.ofMatrix1]⟩
  let M : Matrix (Qubits 1) (Qubits 1) ℂ := U.submatrix (fun b => b 0) (fun b => b 0)
  have hM : M ∈ Matrix.unitaryGroup (Qubits 1) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hU' := Matrix.mem_unitaryGroup_iff.mp hU
    ext y z
    simp only [M, Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, Matrix.one_apply]
    have hsum : (∑ x : Qubits 1, U (y 0) (x 0) * star (U (z 0) (x 0))) =
        ∑ x : Bool, U (y 0) x * star (U (z 0) x) :=
      Fintype.sum_equiv qubits1EquivBool _ (fun x : Bool => U (y 0) x * star (U (z 0) x))
        (fun _ => rfl)
    rw [hsum]
    have hent := congrFun (congrFun hU' (y 0)) (z 0)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at hent
    rw [hent]
    by_cases h : y 0 = z 0
    · have hyz : y = z := funext fun i => by fin_cases i; exact h
      subst hyz; simp
    · have hyz : y ≠ z := fun heq => h (congrFun heq 0)
      simp [h, hyz]
  exact hM

lemma ofMatrix2_mem_gates12 {U : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Gate.ofMatrix2 U ∈ gates12 := by
  refine ⟨?_, by simp [Gate.ofMatrix2], by simp [Gate.ofMatrix2]⟩
  let M : Matrix (Qubits 2) (Qubits 2) ℂ :=
    U.submatrix (fun b => (b 0, b 1)) (fun b => (b 0, b 1))
  have hM : M ∈ Matrix.unitaryGroup (Qubits 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hU' := Matrix.mem_unitaryGroup_iff.mp hU
    ext y z
    simp only [M, Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, Matrix.one_apply]
    have hsum : (∑ x : Qubits 2, U (y 0, y 1) (x 0, x 1) * star (U (z 0, z 1) (x 0, x 1))) =
        ∑ x : Bool × Bool, U (y 0, y 1) x * star (U (z 0, z 1) x) :=
      Fintype.sum_equiv qubits2EquivProd _
        (fun x : Bool × Bool => U (y 0, y 1) x * star (U (z 0, z 1) x)) (fun _ => rfl)
    rw [hsum]
    have hent := congrFun (congrFun hU' (y 0, y 1)) (z 0, z 1)
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at hent
    rw [hent]
    by_cases h : (y 0, y 1) = (z 0, z 1)
    · have hyz : y = z := funext fun i => by
        fin_cases i
        · exact congrArg Prod.fst h
        · exact congrArg Prod.snd h
      subst hyz; simp
    · have hyz : y ≠ z := fun heq => h (by subst heq; rfl)
      simp [h, hyz]
  exact hM

lemma controlled_mem_unitaryGroup {κ : Type*} [Fintype κ] [DecidableEq κ]
    {U : Matrix κ κ ℂ} (hU : U ∈ Matrix.unitaryGroup κ ℂ) :
    controlled U ∈ Matrix.unitaryGroup (Bool × κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hU' := Matrix.mem_unitaryGroup_iff.mp hU
  ext ⟨y0, y1⟩ ⟨z0, z1⟩
  simp only [Matrix.mul_apply, Matrix.star_apply, controlled, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  by_cases hyz : y0 = z0
  · subst hyz
    rw [Finset.sum_eq_single y0]
    · cases y0
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Finset.sum_eq_single z1]
        · by_cases h1 : y1 = z1 <;> simp [h1]
        · intro x _ hx; simp [hx.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp only [↓reduceIte]
        have hent := congrFun (congrFun hU' y1) z1
        simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using hent
    · intro b _ hb
      refine Finset.sum_eq_zero fun x _ => ?_
      simp [hb.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hpne : (y0, y1) ≠ (z0, z1) := fun h => hyz (congrArg Prod.fst h)
    rw [if_neg hpne]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun x _ => ?_
    by_cases hb : y0 = b
    · subst hb; simp [ne_comm.mp hyz]
    · simp [hb]

lemma pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, pauliX,
    Matrix.of_apply]
  cases a <;> cases b <;> norm_num

lemma pauliZ_mem_unitaryGroup : pauliZ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, pauliZ,
    Matrix.diagonal_apply]
  cases a <;> cases b <;> norm_num

lemma hadamard_mem_unitaryGroup : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  have hstar : star hadamard = hadamard := by
    ext a b
    cases a <;> cases b <;> simp [hadamard, Matrix.star_apply]
  rw [Matrix.mem_unitaryGroup_iff, hstar, hadamard_mul_self]

lemma cnot_mem_unitaryGroup : cnot ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Fintype.sum_bool, cnot, Matrix.of_apply]
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp

lemma swapGate_mem_unitaryGroup : swapGate ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Fintype.sum_bool, swapGate, Matrix.of_apply]
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp

def wire1Emb {m : ℕ} (w : Fin m) : Fin 1 ↪ Fin m where
  toFun _ := w
  inj' i j _ := Subsingleton.elim i j

def wire2Emb {m : ℕ} (w0 w1 : Fin m) (hne : w0 ≠ w1) : Fin 2 ↪ Fin m where
  toFun := ![w0, w1]
  inj' i j h := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h hne
    · exact absurd h.symm hne
    · rfl

lemma wire1Emb_mem {m : ℕ} (w : Fin m) (i : Fin 1) : wire1Emb w i = w := rfl

lemma wire2Emb_zero {m : ℕ} (w0 w1 : Fin m) (hne : w0 ≠ w1) : wire2Emb w0 w1 hne 0 = w0 := rfl

lemma wire2Emb_one {m : ℕ} (w0 w1 : Fin m) (hne : w0 ≠ w1) : wire2Emb w0 w1 hne 1 = w1 := rfl

def gate1App {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (w : Fin m) : GateApp gates12 m where
  gate := Gate.ofMatrix1 U
  mem := ofMatrix1_mem_gates12 hU
  wires := wire1Emb w

def gate2App {m : ℕ} (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) (w0 w1 : Fin m) (hne : w0 ≠ w1) :
    GateApp gates12 m where
  gate := Gate.ofMatrix2 U
  mem := ofMatrix2_mem_gates12 hU
  wires := wire2Emb w0 w1 hne

def ctrlGate1App {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) : GateApp gates12 m :=
  gate2App (controlled U) (controlled_mem_unitaryGroup hU) c t hne

def pauliXApp {m : ℕ} (w : Fin m) : GateApp gates12 m :=
  gate1App pauliX pauliX_mem_unitaryGroup w

def pauliZApp {m : ℕ} (w : Fin m) : GateApp gates12 m :=
  gate1App pauliZ pauliZ_mem_unitaryGroup w

noncomputable def hadamardApp {m : ℕ} (w : Fin m) : GateApp gates12 m :=
  gate1App hadamard hadamard_mem_unitaryGroup w

def cnotApp {m : ℕ} (c t : Fin m) (hne : c ≠ t) : GateApp gates12 m :=
  gate2App cnot cnot_mem_unitaryGroup c t hne

def swapApp {m : ℕ} (a b : Fin m) (hne : a ≠ b) : GateApp gates12 m :=
  gate2App swapGate swapGate_mem_unitaryGroup a b hne

def gate1 {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (w : Fin m) : LayeredCircuit m :=
  LayeredCircuit.single (gate1App U hU w)

def ctrlGate1 {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) : LayeredCircuit m :=
  LayeredCircuit.single (ctrlGate1App U hU c t hne)

def pauliXGate {m : ℕ} (w : Fin m) : LayeredCircuit m :=
  LayeredCircuit.single (pauliXApp w)

def pauliZGate {m : ℕ} (w : Fin m) : LayeredCircuit m :=
  LayeredCircuit.single (pauliZApp w)

noncomputable def hadamardGate {m : ℕ} (w : Fin m) : LayeredCircuit m :=
  LayeredCircuit.single (hadamardApp w)

def cnotGate {m : ℕ} (c t : Fin m) (hne : c ≠ t) : LayeredCircuit m :=
  LayeredCircuit.single (cnotApp c t hne)

@[simp] lemma gate1_size {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (w : Fin m) : (gate1 U hU w).size = 1 := rfl

@[simp] lemma gate1_depth {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (w : Fin m) : (gate1 U hU w).depth = 1 := rfl

lemma gate1_usesOnly {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (w : Fin m) : (gate1 U hU w).UsesOnly {w} :=
  LayeredCircuit.single_usesOnly _ fun _ => Finset.mem_singleton_self w

@[simp] lemma ctrlGate1_size {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) : (ctrlGate1 U hU c t hne).size = 1 := rfl

@[simp] lemma ctrlGate1_depth {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) : (ctrlGate1 U hU c t hne).depth = 1 := rfl

lemma ctrlGate1_usesOnly {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) : (ctrlGate1 U hU c t hne).UsesOnly {c, t} := by
  refine LayeredCircuit.single_usesOnly _ fun i => ?_
  dsimp only [ctrlGate1App, gate2App, Gate.ofMatrix2] at i ⊢
  rw [Finset.mem_insert, Finset.mem_singleton]
  rcases (by fin_cases i <;> decide : i = 0 ∨ i = 1) with rfl | rfl
  · left; rfl
  · right; rfl

@[simp] lemma pauliXGate_size {m : ℕ} (w : Fin m) : (pauliXGate w).size = 1 := rfl
@[simp] lemma pauliXGate_depth {m : ℕ} (w : Fin m) : (pauliXGate w).depth = 1 := rfl

lemma pauliXGate_usesOnly {m : ℕ} (w : Fin m) : (pauliXGate w).UsesOnly {w} :=
  gate1_usesOnly pauliX pauliX_mem_unitaryGroup w

@[simp] lemma pauliZGate_size {m : ℕ} (w : Fin m) : (pauliZGate w).size = 1 := rfl
@[simp] lemma pauliZGate_depth {m : ℕ} (w : Fin m) : (pauliZGate w).depth = 1 := rfl

@[simp] lemma hadamardGate_size {m : ℕ} (w : Fin m) : (hadamardGate w).size = 1 := rfl
@[simp] lemma hadamardGate_depth {m : ℕ} (w : Fin m) : (hadamardGate w).depth = 1 := rfl

@[simp] lemma cnotGate_size {m : ℕ} (c t : Fin m) (hne : c ≠ t) :
    (cnotGate c t hne).size = 1 := rfl

@[simp] lemma cnotGate_depth {m : ℕ} (c t : Fin m) (hne : c ≠ t) :
    (cnotGate c t hne).depth = 1 := rfl

lemma cnotGate_usesOnly {m : ℕ} (c t : Fin m) (hne : c ≠ t) :
    (cnotGate c t hne).UsesOnly {c, t} := by
  refine LayeredCircuit.single_usesOnly _ fun i => ?_
  dsimp only [cnotApp, gate2App, Gate.ofMatrix2] at i ⊢
  rw [Finset.mem_insert, Finset.mem_singleton]
  rcases (by fin_cases i <;> decide : i = 0 ∨ i = 1) with rfl | rfl
  · left; rfl
  · right; rfl

private lemma embedOp_ofMatrix1_entry {m : ℕ} (U : Matrix Bool Bool ℂ) (w : Fin m)
    (y z : Qubits m) :
    embedOp (U.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) (wire1Emb w) y z =
      if (∀ a : Fin m, a ≠ w → y a = z a) then U (y w) (z w) else 0 := by
  simp only [embedOp, Matrix.of_apply, Matrix.submatrix_apply]
  have hiff : (∀ a : Fin m, a ∉ Set.range (wire1Emb w) → y a = z a) ↔
      (∀ a : Fin m, a ≠ w → y a = z a) := by
    constructor
    · intro h a ha
      apply h a
      rintro ⟨i, hi⟩
      exact ha hi.symm
    · intro h a ha
      apply h a
      intro heq
      subst heq
      exact ha ⟨0, rfl⟩
  by_cases h : ∀ a : Fin m, a ≠ w → y a = z a
  · rw [if_pos (hiff.mpr h), if_pos h]; rfl
  · rw [if_neg (mt hiff.mp h), if_neg h]

lemma embedOp_gate1App_entry {m : ℕ} (U : Matrix Bool Bool ℂ) (w : Fin m)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (y z : Qubits m) :
    embedOp (gate1App U hU w).gate.mat (gate1App U hU w).wires y z =
      if (∀ a : Fin m, a ≠ w → y a = z a) then U (y w) (z w) else 0 :=
  embedOp_ofMatrix1_entry U w y z

private lemma embedOp_ofMatrix2_entry {m : ℕ} (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (w0 w1 : Fin m) (hne : w0 ≠ w1) (y z : Qubits m) :
    embedOp (U.submatrix (fun b : Qubits 2 => (b 0, b 1)) (fun b : Qubits 2 => (b 0, b 1)))
        (wire2Emb w0 w1 hne) y z =
      if (∀ a : Fin m, a ≠ w0 → a ≠ w1 → y a = z a) then U (y w0, y w1) (z w0, z w1) else 0 := by
  simp only [embedOp, Matrix.of_apply, Matrix.submatrix_apply]
  have hiff : (∀ a : Fin m, a ∉ Set.range (wire2Emb w0 w1 hne) → y a = z a) ↔
      (∀ a : Fin m, a ≠ w0 → a ≠ w1 → y a = z a) := by
    constructor
    · intro h a ha0 ha1
      apply h a
      rintro ⟨i, rfl⟩
      fin_cases i
      · exact ha0 rfl
      · exact ha1 rfl
    · intro h a ha
      apply h a
      · intro h0; subst h0; exact ha ⟨0, rfl⟩
      · intro h1; subst h1; exact ha ⟨1, rfl⟩
  by_cases h : ∀ a : Fin m, a ≠ w0 → a ≠ w1 → y a = z a
  · rw [if_pos (hiff.mpr h), if_pos h]; rfl
  · rw [if_neg (mt hiff.mp h), if_neg h]

lemma embedOp_gate2App_entry {m : ℕ} (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) (w0 w1 : Fin m) (hne : w0 ≠ w1)
    (y z : Qubits m) :
    embedOp (gate2App U hU w0 w1 hne).gate.mat (gate2App U hU w0 w1 hne).wires y z =
      if (∀ a : Fin m, a ≠ w0 → a ≠ w1 → y a = z a) then U (y w0, y w1) (z w0, z w1) else 0 :=
  embedOp_ofMatrix2_entry U w0 w1 hne y z

lemma act_pauliXGate_ket {m : ℕ} (w : Fin m) (x : Qubits m) :
    act (pauliXGate w).unitary (ket x) = ket (Function.update x w (!x w)) := by
  rw [pauliXGate, LayeredCircuit.single_unitary, act_ket_eq]
  rw [Finset.sum_eq_single (Function.update x w (!x w))]
  · rw [pauliXApp, embedOp_gate1App_entry]
    have hoff : ∀ a : Fin m, a ≠ w → Function.update x w (!x w) a = x a :=
      fun a ha => Function.update_of_ne ha _ _
    rw [if_pos hoff, Function.update_self]
    cases hx : x w <;> simp [pauliX]
  · intro y _ hy
    rw [pauliXApp, embedOp_gate1App_entry]
    by_cases hoff : ∀ a : Fin m, a ≠ w → y a = x a
    · rw [if_pos hoff]
      have hyw : y w = x w := by
        by_contra hne
        apply hy
        funext a
        by_cases haw : a = w
        · subst haw
          cases hxw : x a <;> cases hyw' : y a <;> simp_all
        · rw [hoff a haw, Function.update_of_ne haw]
      simp [pauliX, hyw]
    · rw [if_neg hoff, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma act_cnotGate_ket {m : ℕ} (c t : Fin m) (hne : c ≠ t) (x : Qubits m) :
    act (cnotGate c t hne).unitary (ket x) =
      ket (Function.update x t (xor (x t) (x c))) := by
  rw [cnotGate, LayeredCircuit.single_unitary, act_ket_eq]
  rw [Finset.sum_eq_single (Function.update x t (xor (x t) (x c)))]
  · rw [cnotApp, embedOp_gate2App_entry]
    have hoff : ∀ a : Fin m, a ≠ c → a ≠ t → Function.update x t (xor (x t) (x c)) a = x a :=
      fun a _ hat => Function.update_of_ne hat _ _
    rw [if_pos hoff, Function.update_of_ne hne, Function.update_self]
    simp [cnot]
  · intro y _ hy
    rw [cnotApp, embedOp_gate2App_entry]
    by_cases hoff : ∀ a : Fin m, a ≠ c → a ≠ t → y a = x a
    · rw [if_pos hoff]
      have hne_cnot : ¬ (y c = x c ∧ y t = xor (x t) (x c)) := by
        rintro ⟨hyc, hyt⟩
        apply hy
        funext a
        by_cases hac : a = c
        · subst hac; rw [hyc, Function.update_of_ne hne]
        · by_cases hat : a = t
          · subst hat; rw [hyt, Function.update_self]
          · rw [hoff a hac hat, Function.update_of_ne hat]
      simp [cnot, hne_cnot]
    · rw [if_neg hoff, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma act_ctrlGate1_ket {m : ℕ} (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c t : Fin m) (hne : c ≠ t) (x : Qubits m) :
    act (ctrlGate1 U hU c t hne).unitary (ket x) =
      ∑ b : Bool, (if x c then U b (x t) else if b = x t then 1 else 0) •
        ket (Function.update x t b) := by
  rw [ctrlGate1, LayeredCircuit.single_unitary, act_ket_eq]
  have hsum : (∑ y : Qubits m,
      embedOp (ctrlGate1App U hU c t hne).gate.mat (ctrlGate1App U hU c t hne).wires y x •
        ket y) =
      ∑ y ∈ Finset.univ.image (fun b : Bool => Function.update x t b),
      embedOp (ctrlGate1App U hU c t hne).gate.mat (ctrlGate1App U hU c t hne).wires y x •
        ket y := by
    rw [← Finset.sum_subset (Finset.subset_univ _)]
    intro y _ hy
    dsimp only [ctrlGate1App]
    rw [embedOp_gate2App_entry]
    by_cases hoff : ∀ a : Fin m, a ≠ c → a ≠ t → y a = x a
    · rw [if_pos hoff]
      by_cases hyc : y c = x c
      · exfalso; apply hy
        rw [Finset.mem_image]
        refine ⟨y t, Finset.mem_univ _, ?_⟩
        funext a
        by_cases hat : a = t
        · subst hat; simp
        · rw [Function.update_of_ne hat]
          by_cases hac : a = c
          · subst hac; exact hyc.symm
          · exact (hoff a hac hat).symm
      · simp [controlled, hyc]
    · rw [if_neg hoff, zero_smul]
  rw [hsum, Finset.sum_image]
  · refine Finset.sum_congr rfl fun b _ => ?_
    dsimp only [ctrlGate1App]
    rw [embedOp_gate2App_entry]
    have hoff : ∀ a : Fin m, a ≠ c → a ≠ t → Function.update x t b a = x a :=
      fun a _ hat => Function.update_of_ne hat _ _
    rw [if_pos hoff, Function.update_of_ne hne, Function.update_self]
    simp [controlled, Matrix.one_apply]
  · intro b1 _ b2 _ hb
    have := congrFun hb t
    simpa using this

/-! ### 9. Barenco 5-Gate Toffoli (`toffoli3`, `toffoliOn`) -/

noncomputable def sqrtX : Matrix Bool Bool ℂ :=
  ((1 - Complex.I) / 2) • (1 : Matrix Bool Bool ℂ) + ((1 + Complex.I) / 2) • pauliX

lemma sqrtX_mem_unitaryGroup : sqrtX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, sqrtX,
    pauliX, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  cases a <;> cases b <;> simp <;> ring_nf <;> norm_num

lemma sqrtX_mul_self : sqrtX * sqrtX = pauliX := by
  ext a b
  simp only [Matrix.mul_apply, Fintype.sum_bool, sqrtX, pauliX, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  cases a <;> cases b <;> simp <;> ring_nf <;> norm_num

def toffoliMat : Matrix (Qubits 3) (Qubits 3) ℂ :=
  permMat fun z => ![z 0, z 1, xor (z 2) (z 0 && z 1)]

lemma toffoliMat_mem_unitaryGroup : toffoliMat ∈ Matrix.unitaryGroup (Qubits 3) ℂ := by
  apply permMat_mem_unitaryGroup
  refine ⟨fun a b h => ?_, fun b => ⟨![b 0, b 1, xor (b 2) (b 0 && b 1)], ?_⟩⟩
  · have h0 : a 0 = b 0 := congrFun h 0
    have h1 : a 1 = b 1 := congrFun h 1
    have h2 : xor (a 2) (a 0 && a 1) = xor (b 2) (b 0 && b 1) := congrFun h 2
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · rw [h0, h1] at h2
      simpa using congrArg (fun x => xor x (b 0 && b 1)) h2
  · funext i
    fin_cases i <;> simp

noncomputable def toffoli3 : LayeredCircuit 3 :=
  (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 1 2 (by decide)).seq
    ((cnotGate 0 1 (by decide)).seq
      ((ctrlGate1 (star sqrtX) (Unitary.star_mem sqrtX_mem_unitaryGroup) 1 2 (by decide)).seq
        ((cnotGate 0 1 (by decide)).seq
          (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 0 2 (by decide)))))

@[simp] lemma toffoli3_size : toffoli3.size = 5 := rfl
@[simp] lemma toffoli3_depth : toffoli3.depth = 5 := rfl

private lemma block3_mul (M N : Bool → Bool → Matrix Bool Bool ℂ) :
    (Matrix.of fun y z : Qubits 3 =>
      if y 0 = z 0 ∧ y 1 = z 1 then M (y 0) (y 1) (y 2) (z 2) else 0) *
    (Matrix.of fun y z : Qubits 3 =>
      if y 0 = z 0 ∧ y 1 = z 1 then N (y 0) (y 1) (y 2) (z 2) else 0) =
    Matrix.of fun y z : Qubits 3 =>
      if y 0 = z 0 ∧ y 1 = z 1 then (M (y 0) (y 1) * N (y 0) (y 1)) (y 2) (z 2) else 0 := by
  classical
  ext y z
  simp only [Matrix.mul_apply, Matrix.of_apply]
  by_cases hyz : y 0 = z 0 ∧ y 1 = z 1
  · rw [if_pos hyz]
    have hsum : (∑ x : Qubits 3,
        (if y 0 = x 0 ∧ y 1 = x 1 then M (y 0) (y 1) (y 2) (x 2) else 0) *
        (if x 0 = z 0 ∧ x 1 = z 1 then N (x 0) (x 1) (x 2) (z 2) else 0)) =
        ∑ x ∈ Finset.univ.image (fun b : Bool => ![y 0, y 1, b]),
        (if y 0 = x 0 ∧ y 1 = x 1 then M (y 0) (y 1) (y 2) (x 2) else 0) *
        (if x 0 = z 0 ∧ x 1 = z 1 then N (x 0) (x 1) (x 2) (z 2) else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro x _ hx
      by_cases hyx : y 0 = x 0 ∧ y 1 = x 1
      · exfalso; apply hx
        rw [Finset.mem_image]
        refine ⟨x 2, Finset.mem_univ _, ?_⟩
        funext i; fin_cases i
        · exact hyx.1
        · exact hyx.2
        · rfl
      · rw [if_neg hyx, zero_mul]
    rw [hsum, Finset.sum_image]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hyz.1, hyz.2]
      have he0 : (![z 0, z 1, b] : Qubits 3) 0 = z 0 := rfl
      have he1 : (![z 0, z 1, b] : Qubits 3) 1 = z 1 := rfl
      have he2 : (![z 0, z 1, b] : Qubits 3) 2 = b := rfl
      simp only [he0, he1, he2, ↓reduceIte, true_and]
    · intro b1 _ b2 _ hb
      have := congrFun hb 2
      simpa using this
  · rw [if_neg hyz]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hyx : y 0 = x 0 ∧ y 1 = x 1
    · have hxz : ¬ (x 0 = z 0 ∧ x 1 = z 1) := fun h =>
        hyz ⟨hyx.1.trans h.1, hyx.2.trans h.2⟩
      rw [if_neg hxz, mul_zero]
    · rw [if_neg hyx, zero_mul]

lemma toffoli3_unitary : toffoli3.unitary = toffoliMat := by
  have h54321 : toffoli3.unitary =
      (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 0 2 (by decide)).unitary *
      (((cnotGate 0 1 (by decide)).unitary *
        ((ctrlGate1 (star sqrtX) (Unitary.star_mem sqrtX_mem_unitaryGroup) 1 2 (by decide)).unitary *
          (cnotGate 0 1 (by decide)).unitary)) *
      (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 1 2 (by decide)).unitary) := by
    simp only [toffoli3, LayeredCircuit.seq_unitary, Matrix.mul_assoc]
  rw [h54321]
  let flip1 : Qubits 3 → Qubits 3 := fun z => ![z 0, xor (z 1) (z 0), z 2]
  have hflip1_invol : ∀ z : Qubits 3, flip1 (flip1 z) = z := by
    intro z; funext i; fin_cases i <;> simp [flip1]
  have hcnot_entry : ∀ y z : Qubits 3,
      (cnotGate 0 1 (by decide)).unitary y z = if y = flip1 z then 1 else 0 := by
    intro y z
    rw [cnotGate, LayeredCircuit.single_unitary, cnotApp, embedOp_gate2App_entry]
    by_cases hoff : ∀ a : Fin 3, a ≠ 0 → a ≠ 1 → y a = z a
    · rw [if_pos hoff]
      by_cases hy : y = flip1 z
      · rw [if_pos hy, hy]; simp [flip1, cnot]
      · rw [if_neg hy]
        have hnot : ¬ (y 0 = z 0 ∧ y 1 = xor (z 1) (z 0)) := by
          rintro ⟨h0, h1⟩
          apply hy
          funext i; fin_cases i
          · exact h0
          · exact h1
          · exact hoff 2 (by decide) (by decide)
        simp [cnot, hnot]
    · rw [if_neg hoff]
      have hy : y ≠ flip1 z := by
        intro h
        apply hoff
        intro a ha0 ha1
        fin_cases a
        · exact absurd rfl ha0
        · exact absurd rfl ha1
        · rw [h]; rfl
      rw [if_neg hy]
  have hctrl_entry : ∀ (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
      (c : Fin 3) (hc2 : c ≠ 2) (y z : Qubits 3),
      (ctrlGate1 U hU c 2 hc2).unitary y z =
        if y 0 = z 0 ∧ y 1 = z 1 then (if y c then U (y 2) (z 2) else if y 2 = z 2 then 1 else 0)
        else 0 := by
    intro U hU c hc2 y z
    rw [ctrlGate1, LayeredCircuit.single_unitary]
    dsimp only [ctrlGate1App]
    rw [embedOp_gate2App_entry]
    rcases (by fin_cases c <;> decide : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
    · by_cases h1 : y 1 = z 1
      · have hoff : ∀ a : Fin 3, a ≠ 0 → a ≠ 2 → y a = z a := by
          intro a ha0 ha2; fin_cases a
          · exact absurd rfl ha0
          · exact h1
          · exact absurd rfl ha2
        rw [if_pos hoff]
        by_cases h0 : y 0 = z 0
        · rw [if_pos ⟨h0, h1⟩, controlled, Matrix.of_apply, if_pos h0]
          simp [Matrix.one_apply]
        · rw [if_neg (fun ⟨h0', _⟩ => h0 h0'), controlled, Matrix.of_apply, if_neg h0]
      · have hoff : ¬ ∀ a : Fin 3, a ≠ 0 → a ≠ 2 → y a = z a := fun h =>
          h1 (h 1 (by decide) (by decide))
        rw [if_neg hoff, if_neg (fun ⟨_, h1'⟩ => h1 h1')]
    · by_cases h0 : y 0 = z 0
      · have hoff : ∀ a : Fin 3, a ≠ 1 → a ≠ 2 → y a = z a := by
          intro a ha1 ha2; fin_cases a
          · exact h0
          · exact absurd rfl ha1
          · exact absurd rfl ha2
        rw [if_pos hoff]
        by_cases h1 : y 1 = z 1
        · rw [if_pos ⟨h0, h1⟩, controlled, Matrix.of_apply, if_pos h1]
          simp [Matrix.one_apply]
        · rw [if_neg (fun ⟨_, h1'⟩ => h1 h1'), controlled, Matrix.of_apply, if_neg h1]
      · have hoff : ¬ ∀ a : Fin 3, a ≠ 1 → a ≠ 2 → y a = z a := fun h =>
          h0 (h 0 (by decide) (by decide))
        rw [if_neg hoff, if_neg (fun ⟨h0', _⟩ => h0 h0')]
    · exact absurd rfl hc2
  let M1 : Bool → Bool → Matrix Bool Bool ℂ := fun _ b1 => if b1 then sqrtX else 1
  let M3 : Bool → Bool → Matrix Bool Bool ℂ := fun b0 b1 => if xor b1 b0 then star sqrtX else 1
  let M5 : Bool → Bool → Matrix Bool Bool ℂ := fun b0 _ => if b0 then sqrtX else 1
  have hG1 : (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 1 2 (by decide)).unitary =
      Matrix.of fun y z : Qubits 3 =>
        if y 0 = z 0 ∧ y 1 = z 1 then M1 (y 0) (y 1) (y 2) (z 2) else 0 := by
    ext y z
    rw [hctrl_entry _ _ 1 (by decide) y z, Matrix.of_apply]
    dsimp [M1]
    split_ifs with h1 h2 <;> simp [Matrix.one_apply, *]
  have hG5 : (ctrlGate1 sqrtX sqrtX_mem_unitaryGroup 0 2 (by decide)).unitary =
      Matrix.of fun y z : Qubits 3 =>
        if y 0 = z 0 ∧ y 1 = z 1 then M5 (y 0) (y 1) (y 2) (z 2) else 0 := by
    ext y z
    rw [hctrl_entry _ _ 0 (by decide) y z, Matrix.of_apply]
    dsimp [M5]
    split_ifs with h1 h2 <;> simp [Matrix.one_apply, *]
  have hG3 : ((cnotGate 0 1 (by decide)).unitary *
      ((ctrlGate1 (star sqrtX) (Unitary.star_mem sqrtX_mem_unitaryGroup) 1 2 (by decide)).unitary *
        (cnotGate 0 1 (by decide)).unitary)) =
      Matrix.of fun y z : Qubits 3 =>
        if y 0 = z 0 ∧ y 1 = z 1 then M3 (y 0) (y 1) (y 2) (z 2) else 0 := by
    ext y z
    simp only [Matrix.mul_apply, Matrix.of_apply]
    have hR : ∀ x : Qubits 3,
        (∑ w : Qubits 3,
          (ctrlGate1 (star sqrtX) (Unitary.star_mem sqrtX_mem_unitaryGroup) 1 2 (by decide)).unitary x w *
            (cnotGate 0 1 (by decide)).unitary w z) =
        (ctrlGate1 (star sqrtX) (Unitary.star_mem sqrtX_mem_unitaryGroup) 1 2 (by decide)).unitary
          x (flip1 z) := by
      intro x
      rw [Finset.sum_eq_single (flip1 z)]
      · rw [hcnot_entry, if_pos rfl, mul_one]
      · intro w _ hw; rw [hcnot_entry, if_neg hw, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hR]
    rw [Finset.sum_eq_single (flip1 y)]
    · rw [hcnot_entry, if_pos (hflip1_invol y).symm, one_mul, hctrl_entry _ _ 1 (by decide)]
      have hiff : flip1 y 0 = flip1 z 0 ∧ flip1 y 1 = flip1 z 1 ↔ y 0 = z 0 ∧ y 1 = z 1 := by
        simp only [flip1, Matrix.cons_val_zero, Matrix.cons_val_one]
        cases y 0 <;> cases z 0 <;> cases y 1 <;> cases z 1 <;> simp
      by_cases hyz : y 0 = z 0 ∧ y 1 = z 1
      · rw [if_pos (hiff.mpr hyz), if_pos hyz]
        have h1L : flip1 y 1 = xor (y 1) (y 0) := rfl
        have h2L : flip1 y 2 = y 2 := rfl
        have h2R : flip1 z 2 = z 2 := rfl
        rw [h1L, h2L, h2R]
        dsimp only [M3]
        cases h0 : y 0 <;> cases h1 : y 1 <;> simp [Matrix.one_apply]
      · rw [if_neg (mt hiff.mp hyz), if_neg hyz]
    · intro x _ hx
      have hne : y ≠ flip1 x := fun h => hx (by rw [h, hflip1_invol])
      rw [hcnot_entry, if_neg hne, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hG1, hG3, hG5, block3_mul M3 M1, block3_mul M5 (fun b0 b1 => M3 b0 b1 * M1 b0 b1)]
  ext y z
  simp only [Matrix.of_apply, toffoliMat, permMat]
  have hprod : ∀ b0 b1 : Bool, M5 b0 b1 * (M3 b0 b1 * M1 b0 b1) =
      if b0 && b1 then pauliX else 1 := by
    intro b0 b1
    have hstar : star sqrtX * sqrtX = 1 := by
      simpa using Matrix.mem_unitaryGroup_iff'.mp sqrtX_mem_unitaryGroup
    have hmul_star : sqrtX * star sqrtX = 1 := by
      simpa using Matrix.mem_unitaryGroup_iff.mp sqrtX_mem_unitaryGroup
    cases b0 <;> cases b1 <;> simp [M1, M3, M5, hstar, hmul_star, sqrtX_mul_self]
  have hboolX : ∀ (b y2 z2 : Bool),
      (if b then pauliX else (1 : Matrix Bool Bool ℂ)) y2 z2 =
        if y2 = xor z2 b then 1 else 0 := by
    intro b y2 z2
    cases b <;> cases y2 <;> cases z2 <;> simp [pauliX]
  by_cases hyz : y 0 = z 0 ∧ y 1 = z 1
  · rw [if_pos hyz, hprod (y 0) (y 1), hboolX (y 0 && y 1) (y 2) (z 2)]
    by_cases hy_eq : y = ![z 0, z 1, xor (z 2) (z 0 && z 1)]
    · rw [if_pos hy_eq]
      have hy2 : y 2 = xor (z 2) (y 0 && y 1) := by
        have := congrFun hy_eq 2
        simpa [hyz.1, hyz.2] using this
      rw [if_pos hy2]
    · rw [if_neg hy_eq]
      have hy2 : y 2 ≠ xor (z 2) (y 0 && y 1) := by
        intro h2
        apply hy_eq
        funext i; fin_cases i
        · exact hyz.1
        · exact hyz.2
        · simpa [hyz.1, hyz.2] using h2
      rw [if_neg hy2]
  · rw [if_neg hyz]
    have hy_ne : y ≠ ![z 0, z 1, xor (z 2) (z 0 && z 1)] := by
      intro h; apply hyz
      exact ⟨congrFun h 0, congrFun h 1⟩
    rw [if_neg hy_ne]

lemma act_toffoli3_ket (x : Qubits 3) :
    act toffoli3.unitary (ket x) = ket ![x 0, x 1, xor (x 2) (x 0 && x 1)] := by
  rw [toffoli3_unitary, toffoliMat, act_permMat_ket]

def wire3Emb {m : ℕ} (w0 w1 w2 : Fin m) (h01 : w0 ≠ w1) (h02 : w0 ≠ w2) (h12 : w1 ≠ w2) :
    Fin 3 ↪ Fin m where
  toFun := ![w0, w1, w2]
  inj' i j h := by
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] lemma wire3Emb_zero {m : ℕ} (w0 w1 w2 : Fin m) (h01 : w0 ≠ w1) (h02 : w0 ≠ w2)
    (h12 : w1 ≠ w2) : wire3Emb w0 w1 w2 h01 h02 h12 0 = w0 := rfl
@[simp] lemma wire3Emb_one {m : ℕ} (w0 w1 w2 : Fin m) (h01 : w0 ≠ w1) (h02 : w0 ≠ w2)
    (h12 : w1 ≠ w2) : wire3Emb w0 w1 w2 h01 h02 h12 1 = w1 := rfl
@[simp] lemma wire3Emb_two {m : ℕ} (w0 w1 w2 : Fin m) (h01 : w0 ≠ w1) (h02 : w0 ≠ w2)
    (h12 : w1 ≠ w2) : wire3Emb w0 w1 w2 h01 h02 h12 2 = w2 := rfl

noncomputable def toffoliOn {m : ℕ} (c1 c2 tgt : Fin m)
    (h12 : c1 ≠ c2) (h1t : c1 ≠ tgt) (h2t : c2 ≠ tgt) : LayeredCircuit m :=
  toffoli3.mapWires (wire3Emb c1 c2 tgt h12 h1t h2t)

@[simp] lemma toffoliOn_size {m : ℕ} (c1 c2 tgt : Fin m)
    (h12 : c1 ≠ c2) (h1t : c1 ≠ tgt) (h2t : c2 ≠ tgt) :
    (toffoliOn c1 c2 tgt h12 h1t h2t).size = 5 := by
  simp [toffoliOn]

@[simp] lemma toffoliOn_depth {m : ℕ} (c1 c2 tgt : Fin m)
    (h12 : c1 ≠ c2) (h1t : c1 ≠ tgt) (h2t : c2 ≠ tgt) :
    (toffoliOn c1 c2 tgt h12 h1t h2t).depth = 5 := by
  simp [toffoliOn]

lemma toffoliOn_usesOnly {m : ℕ} (c1 c2 tgt : Fin m)
    (h12 : c1 ≠ c2) (h1t : c1 ≠ tgt) (h2t : c2 ≠ tgt) :
    (toffoliOn c1 c2 tgt h12 h1t h2t).UsesOnly {c1, c2, tgt} := by
  have h3 : toffoli3.UsesOnly Finset.univ := fun _ _ _ _ _ => Finset.mem_univ _
  refine (LayeredCircuit.mapWires_usesOnly (wire3Emb c1 c2 tgt h12 h1t h2t) toffoli3 h3).mono ?_
  intro x hx
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with ⟨i, rfl⟩
  rcases (by fin_cases i <;> decide : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp

lemma act_toffoliOn_ket {m : ℕ} (c1 c2 tgt : Fin m)
    (h12 : c1 ≠ c2) (h1t : c1 ≠ tgt) (h2t : c2 ≠ tgt) (x : Qubits m) :
    act (toffoliOn c1 c2 tgt h12 h1t h2t).unitary (ket x) =
      ket (Function.update x tgt (xor (x tgt) (x c1 && x c2))) := by
  rw [toffoliOn, LayeredCircuit.mapWires_unitary, act_ket_eq, toffoli3_unitary]
  let x' := Function.update x tgt (xor (x tgt) (x c1 && x c2))
  rw [Finset.sum_eq_single x']
  · simp only [embedOp, Matrix.of_apply, toffoliMat, permMat]
    have hoff : ∀ a : Fin m, a ∉ Set.range (wire3Emb c1 c2 tgt h12 h1t h2t) → x' a = x a := by
      intro a ha
      have hat : a ≠ tgt := fun h => ha ⟨2, by simp [h]⟩
      exact Function.update_of_ne hat _ _
    rw [if_pos hoff]
    have heq : (x' ∘ wire3Emb c1 c2 tgt h12 h1t h2t) =
        ![(x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 0, (x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 1,
          xor ((x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 2)
            ((x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 0 && (x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 1)] := by
      funext i
      rcases (by fin_cases i <;> decide : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · change x' c1 = x c1; exact Function.update_of_ne h1t _ _
      · change x' c2 = x c2; exact Function.update_of_ne h2t _ _
      · change x' tgt = xor (x tgt) (x c1 && x c2); exact Function.update_self _ _ _
    rw [if_pos heq, one_smul]
  · intro y _ hy
    simp only [embedOp, Matrix.of_apply, toffoliMat, permMat]
    by_cases hoff : ∀ a : Fin m, a ∉ Set.range (wire3Emb c1 c2 tgt h12 h1t h2t) → y a = x a
    · rw [if_pos hoff]
      have hne : (y ∘ wire3Emb c1 c2 tgt h12 h1t h2t) ≠
          ![(x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 0, (x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 1,
            xor ((x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 2)
              ((x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 0 && (x ∘ wire3Emb c1 c2 tgt h12 h1t h2t) 1)] := by
        intro h
        apply hy
        funext a
        dsimp only [x']
        by_cases ha0 : a = c1
        · subst ha0; rw [Function.update_of_ne h1t]; simpa using congrFun h 0
        · by_cases ha1 : a = c2
          · subst ha1; rw [Function.update_of_ne h2t]; simpa using congrFun h 1
          · by_cases ha2 : a = tgt
            · subst ha2; rw [Function.update_self]; simpa using congrFun h 2
            · rw [Function.update_of_ne ha2]
              apply hoff a
              rintro ⟨i, rfl⟩
              rcases (by fin_cases i <;> decide : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
                simp at ha0 ha1 ha2
      rw [if_neg hne, zero_smul]
    · rw [if_neg hoff, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### 10. `Nat.clog 2` Helper Lemmas -/

lemma clog2_le_iff_le_pow {n k : ℕ} : Nat.clog 2 n ≤ k ↔ n ≤ 2 ^ k :=
  Nat.clog_le_iff_le_pow (by norm_num)

lemma clog2_rec {len : ℕ} (h : 2 ≤ len) :
    Nat.clog 2 ((len + 1) / 2) + 1 = Nat.clog 2 len := by
  apply le_antisymm
  · rw [← Nat.add_le_add_iff_right (n := 0), add_zero]
    have hlt : 0 < Nat.clog 2 len := by
      by_contra hz
      have h0 : Nat.clog 2 len = 0 := by omega
      have hle : len ≤ 2 ^ 0 := clog2_le_iff_le_pow.mp (le_of_eq h0)
      omega
    have hprev : len ≤ 2 ^ Nat.clog 2 len := Nat.le_pow_clog (by norm_num) len
    have hpow_eq : 2 ^ Nat.clog 2 len = 2 * 2 ^ (Nat.clog 2 len - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hlt, pow_succ']
    have hdiv_le : (len + 1) / 2 ≤ 2 ^ (Nat.clog 2 len - 1) := by omega
    have hclog_le : Nat.clog 2 ((len + 1) / 2) ≤ Nat.clog 2 len - 1 :=
      clog2_le_iff_le_pow.mpr hdiv_le
    omega
  · rw [clog2_le_iff_le_pow, pow_succ']
    have hdiv : (len + 1) / 2 ≤ 2 ^ Nat.clog 2 ((len + 1) / 2) :=
      Nat.le_pow_clog (by norm_num) _
    omega

lemma clog2_half_le {len : ℕ} : Nat.clog 2 (len / 2) ≤ Nat.clog 2 ((len + 1) / 2) :=
  Nat.clog_mono_right 2 (by omega)

lemma clog2_succ_le_real_log {n : ℕ} (hn : 1 ≤ n) :
    (Nat.clog 2 (n + 1) : ℝ) ≤ Real.log n / Real.log 2 + 1 := by
  set k := Nat.clog 2 (n + 1)
  have hk_pos : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hle : n + 1 ≤ 2 ^ 0 := clog2_le_iff_le_pow.mp (le_of_eq hk0)
    omega
  have hlt : 2 ^ (k - 1) < n + 1 := by
    by_contra hge
    have hle : n + 1 ≤ 2 ^ (k - 1) := by omega
    have hck : k ≤ k - 1 := clog2_le_iff_le_pow.mpr hle
    omega
  have hpow_le : (2 : ℝ) ^ (k - 1) ≤ n := by exact_mod_cast (by omega : 2 ^ (k - 1) ≤ n)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_le : Real.log ((2 : ℝ) ^ (k - 1)) ≤ Real.log n :=
    Real.log_le_log (by positivity) hpow_le
  rw [Real.log_pow] at hlog_le
  have hk_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk_pos, Nat.cast_one]
  rw [hk_cast] at hlog_le
  have hdiv : (k : ℝ) - 1 ≤ Real.log n / Real.log 2 := (le_div_iff₀ hlog2_pos).mpr hlog_le
  linarith

/-! ### 11. Parallel Hadamard Layer (`hadamardLayer`) & `ctrlHadamardN` -/

lemma hadamard_prod_eq_hadamardN {n : ℕ} (y z : Qubits n) :
    (∏ i : Fin n, hadamard (y i) (z i)) = hadamardN n y z := by
  have h00 : (false + false : Bool) = false := by decide
  have h01 : (false + true : Bool) = true := by decide
  have h10 : (true + false : Bool) = true := by decide
  have h11 : (true + true : Bool) = false := by decide
  have hprod_sign : ∀ s : Finset (Fin n),
      (∏ i ∈ s, (if y i && z i then (-1 : ℂ) else 1)) =
        if (∑ i ∈ s, (z i && y i)) then (-1 : ℂ) else 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      have hcomm : (y a && z a) = (z a && y a) := Bool.and_comm _ _
      rw [hcomm]
      cases (z a && y a) <;> cases (∑ i ∈ s, (z i && y i)) <;> simp [h00, h01, h10, h11]
  have hsplit : ∀ i : Fin n,
      hadamard (y i) (z i) = ((Real.sqrt 2)⁻¹ : ℂ) * (if y i && z i then (-1 : ℂ) else 1) := by
    intro i
    simp only [hadamard, Matrix.of_apply]
    split_ifs <;> ring
  simp_rw [hsplit, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    hprod_sign Finset.univ]
  simp only [hadamardN, Matrix.of_apply]
  change (((Real.sqrt 2)⁻¹ : ℂ) ^ n) * (if dotBits z y then (-1 : ℂ) else 1) = _
  have hpow : (((Real.sqrt 2)⁻¹ : ℂ) ^ n) = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hpow]
  cases dotBits z y <;> simp

private lemma circuit_prod_gate1_of_nodup {m : ℕ}
    (L : List (Fin m)) (hL : L.Nodup) (U : Fin m → Matrix Bool Bool ℂ)
    (hU : ∀ w, U w ∈ Matrix.unitaryGroup Bool ℂ) (y z : Qubits m) :
    Circuit.unitary (L.map fun w => gate1App (U w) (hU w) w) y z =
      if (∀ q : Fin m, q ∉ L → y q = z q) then ∏ w ∈ L.toFinset, U w (y w) (z w) else 0 := by
  classical
  induction L generalizing y z with
  | nil =>
    simp only [List.map_nil, circuit_unitary_nil, Matrix.one_apply, List.not_mem_nil,
      not_false_eq_true, forall_true_left, List.toFinset_nil, Finset.prod_empty]
    by_cases h : y = z
    · subst h; rw [if_pos rfl, if_pos (fun _ => rfl)]
    · rw [if_neg h]
      have hne : ¬ ∀ q : Fin m, y q = z q := fun hq => h (funext hq)
      rw [if_neg hne]
  | cons a rest ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, circuit_unitary_cons, Matrix.mul_apply]
    have hih := ih hL.2
    let x₀ : Qubits m := Function.update z a (y a)
    have hx₀_single : (∑ x : Qubits m,
        Circuit.unitary (rest.map fun w => gate1App (U w) (hU w) w) y x *
          embedOp (gate1App (U a) (hU a) a).gate.mat (gate1App (U a) (hU a) a).wires x z) =
        Circuit.unitary (rest.map fun w => gate1App (U w) (hU w) w) y x₀ *
          embedOp (gate1App (U a) (hU a) a).gate.mat (gate1App (U a) (hU a) a).wires x₀ z := by
      rw [Finset.sum_eq_single x₀]
      · intro x _ hx
        rw [embedOp_gate1App_entry]
        by_cases hoff : ∀ q : Fin m, q ≠ a → x q = z q
        · rw [if_pos hoff]
          by_cases hxa : x a = y a
          · exfalso; apply hx
            funext q
            by_cases hqa : q = a
            · subst hqa; simp [x₀, hxa]
            · simp [x₀, Function.update_of_ne hqa, hoff q hqa]
          · rw [hih y x]
            have hnot : ¬ ∀ q : Fin m, q ∉ rest → y q = x q := fun h => hxa (h a hL.1).symm
            rw [if_neg hnot, zero_mul]
        · rw [if_neg hoff, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hx₀_single, hih y x₀, embedOp_gate1App_entry]
    have hx₀_off : ∀ q : Fin m, q ≠ a → x₀ q = z q := fun q hq => Function.update_of_ne hq _ _
    rw [if_pos hx₀_off, show x₀ a = y a from Function.update_self _ _ _]
    have hiff : (∀ q : Fin m, q ∉ rest → y q = x₀ q) ↔ (∀ q : Fin m, q ∉ a :: rest → y q = z q) := by
      constructor
      · intro h q hq
        have hqa : q ≠ a := fun heq => hq (by simp [heq])
        have hqr : q ∉ rest := fun hr => hq (by simp [hr])
        rw [h q hqr, hx₀_off q hqa]
      · intro h q hqr
        by_cases hqa : q = a
        · subst hqa; simp [x₀]
        · have hq : q ∉ a :: rest := by simp [hqa, hqr]
          rw [h q hq, hx₀_off q hqa]
    by_cases hcond : ∀ q : Fin m, q ∉ a :: rest → y q = z q
    · rw [if_pos (hiff.mpr hcond), if_pos hcond, List.toFinset_cons]
      have ha_mem : a ∉ rest.toFinset := by simpa using hL.1
      rw [Finset.prod_insert ha_mem, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      have hwa : w ≠ a := by
        intro heq; subst heq; exact ha_mem hw
      rw [hx₀_off w hwa]
    · rw [if_neg (mt hiff.mp hcond), if_neg hcond, zero_mul]

noncomputable def hadamardLayer (n : ℕ) : LayeredCircuit n :=
  LayeredCircuit.ofLayer ((List.finRange n).map hadamardApp) (by
    dsimp only [LayerDisjoint]
    rw [List.pairwise_map]
    refine (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange n)).imp fun {i j} hij => ?_
    rw [Set.disjoint_left]
    rintro w ⟨a, rfl⟩ ⟨b, hb⟩
    exact hij (hb.symm))

lemma hadamardLayer_size (n : ℕ) : (hadamardLayer n).size = n := by
  simp [hadamardLayer, LayeredCircuit.ofLayer_size]

lemma hadamardLayer_depth (n : ℕ) : (hadamardLayer n).depth ≤ 1 :=
  LayeredCircuit.ofLayer_depth _ _

lemma hadamardLayer_unitary (n : ℕ) : (hadamardLayer n).unitary = hadamardN n := by
  rw [hadamardLayer, LayeredCircuit.ofLayer_unitary]
  ext y z
  have h := circuit_prod_gate1_of_nodup (List.finRange n) (List.nodup_finRange n)
    (fun _ => hadamard) (fun _ => hadamard_mem_unitaryGroup) y z
  have heq : (List.finRange n).map hadamardApp =
      (List.finRange n).map (fun w => gate1App hadamard hadamard_mem_unitaryGroup w) := rfl
  rw [heq, h]
  have hall : ∀ q : Fin n, q ∉ List.finRange n → y q = z q := fun q hq =>
    absurd (List.mem_finRange q) hq
  rw [if_pos hall]
  have hfin : (List.finRange n).toFinset = Finset.univ := by
    ext i; simp
  rw [hfin]
  exact hadamard_prod_eq_hadamardN y z

/-! ### 12. Balanced CNOT Fanout & `ctrlHadamardN` -/

private def ancSlice {m : ℕ} (base lo len : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun w => base + lo ≤ w.1 ∧ w.1 < base + lo + len

private lemma ancSlice_disjoint {m : ℕ} (base lo mid len : ℕ) :
    Disjoint (ancSlice (m := m) base lo mid) (ancSlice (m := m) base (lo + mid) (len - mid)) := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  simp only [ancSlice, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  omega

private lemma ancSlice_union_sub {m : ℕ} (base lo mid len : ℕ) (hmid : mid ≤ len) :
    ancSlice (m := m) base lo mid ∪ ancSlice (m := m) base (lo + mid) (len - mid) ⊆
      ancSlice (m := m) base lo len := by
  intro w hw
  simp only [Finset.mem_union, ancSlice, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  omega

private def fanoutRange (n lo len : ℕ) (_hlen : 1 ≤ len) (hb : lo + len ≤ n) :
    { lc : LayeredCircuit (1 + n + n) // lc.UsesOnly (ancSlice (1 + n) lo len) } :=
  if h2 : len < 2 then
    ⟨LayeredCircuit.id (1 + n + n), LayeredCircuit.id_usesOnly _⟩
  else
    let mid := len / 2
    have hmid1 : 1 ≤ mid := by omega
    have hrem1 : 1 ≤ len - mid := by omega
    have hbL : lo + mid ≤ n := by omega
    have hbR : lo + mid + (len - mid) ≤ n := by omega
    let L := fanoutRange n lo mid hmid1 hbL
    let R := fanoutRange n (lo + mid) (len - mid) hrem1 hbR
    let wL : Fin (1 + n + n) := ⟨1 + n + lo, by omega⟩
    let wR : Fin (1 + n + n) := ⟨1 + n + (lo + mid), by omega⟩
    have hne : wL ≠ wR := by
      intro h; have := congrArg Fin.val h; dsimp [wL, wR] at this; omega
    let step := cnotGate wL wR hne
    let merged := LayeredCircuit.parMerge L.1 R.1 L.2 R.2 (ancSlice_disjoint (1 + n) lo mid len)
    ⟨step.seq merged,
      LayeredCircuit.seq_usesOnly
        ((cnotGate_usesOnly wL wR hne).mono (by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · simp [ancSlice, wL]; omega
          · simp [ancSlice, wR]; omega))
        ((LayeredCircuit.parMerge_usesOnly L.1 R.1 L.2 R.2 _).mono
          (ancSlice_union_sub (1 + n) lo mid len (by omega)))⟩
termination_by len

private lemma fanoutRange_size (n lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ n) :
    (fanoutRange n lo len hlen hb).1.size = len - 1 := by
  induction len using Nat.strong_induction_on generalizing lo with
  | h len ih =>
    unfold fanoutRange
    split_ifs with h2
    · simp; omega
    · dsimp only
      have hsL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have hsR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      simp only [LayeredCircuit.seq_size, LayeredCircuit.parMerge_size, cnotGate_size]
      rw [hsL, hsR]
      omega

private lemma fanoutRange_depth (n lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ n) :
    (fanoutRange n lo len hlen hb).1.depth ≤ Nat.clog 2 len := by
  induction len using Nat.strong_induction_on generalizing lo with
  | h len ih =>
    unfold fanoutRange
    split_ifs with h2
    · simp
    · dsimp only
      have hlen2 : 2 ≤ len := by omega
      have hdL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have hdR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      have hL_le : (fanoutRange n lo (len / 2) (by omega) (by omega)).1.depth ≤
          Nat.clog 2 ((len + 1) / 2) :=
        le_trans hdL clog2_half_le
      have hclog_sub : Nat.clog 2 (len - len / 2) = Nat.clog 2 ((len + 1) / 2) := by
        congr 1; omega
      have hR_le : (fanoutRange n (lo + len / 2) (len - len / 2) (by omega) (by omega)).1.depth ≤
          Nat.clog 2 ((len + 1) / 2) := hclog_sub ▸ hdR
      simp only [LayeredCircuit.seq_depth, LayeredCircuit.parMerge_depth, cnotGate_depth]
      rw [← clog2_rec hlen2, Nat.add_comm 1]
      exact Nat.add_le_add_right (max_le hL_le hR_le) 1

private lemma act_fanoutRange_ket (n lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ n)
    (c : Bool) (x : Qubits (1 + n + n))
    (hroot : x ⟨1 + n + lo, by omega⟩ = c)
    (hclean : ∀ k : ℕ, lo < k → ∀ (_hk2 : k < lo + len), x ⟨1 + n + k, by omega⟩ = false) :
    act (fanoutRange n lo len hlen hb).1.unitary (ket x) =
      ket (fun w => if 1 + n + lo ≤ w.1 ∧ w.1 < 1 + n + lo + len then c else x w) := by
  induction len using Nat.strong_induction_on generalizing lo x with
  | h len ih =>
    unfold fanoutRange
    split_ifs with h2
    · have hlen1 : len = 1 := by omega
      subst hlen1
      simp only [LayeredCircuit.id_unitary, act_one]
      congr 1
      funext w
      split_ifs with hw
      · have hw_eq : w = ⟨1 + n + lo, by omega⟩ := Fin.ext (by simp; omega)
        rw [hw_eq, hroot]
      · rfl
    · dsimp only
      set mid := len / 2
      have hmid1 : 1 ≤ mid := by omega
      have hrem1 : 1 ≤ len - mid := by omega
      have hmid_lt : mid < len := by omega
      have hrem_lt : len - mid < len := by omega
      have hbL : lo + mid ≤ n := by omega
      have hbR : lo + mid + (len - mid) ≤ n := by omega
      let wL : Fin (1 + n + n) := ⟨1 + n + lo, by omega⟩
      let wR : Fin (1 + n + n) := ⟨1 + n + (lo + mid), by omega⟩
      have hne : wL ≠ wR := by
        intro h; have := congrArg Fin.val h; dsimp [wL, wR] at this; omega
      simp only [LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket,
        LayeredCircuit.parMerge_unitary]
      let x1 : Qubits (1 + n + n) := Function.update x wR (xor (x wR) (x wL))
      have hx1_wL : x1 wL = c := by
        dsimp only [x1]
        rw [Function.update_of_ne hne, hroot]
      have hx1_wR : x1 wR = c := by
        have hzero : x wR = false := hclean (lo + mid) (by omega) (by omega)
        dsimp only [x1]
        rw [Function.update_self, hzero]
        change xor false (x ⟨1 + n + lo, by omega⟩) = c
        rw [hroot, Bool.false_xor]
      have hx1_cleanL : ∀ k : ℕ, lo < k → ∀ (_hk2 : k < lo + mid), x1 ⟨1 + n + k, by omega⟩ = false := by
        intro k hk1 hk2
        have hneR : (⟨1 + n + k, by omega⟩ : Fin (1 + n + n)) ≠ wR := by
          intro h; have := congrArg Fin.val h; dsimp [wR] at this; omega
        dsimp only [x1]
        rw [Function.update_of_ne hneR]
        exact hclean k hk1 (by omega)
      have hx1_cleanR : ∀ k : ℕ, lo + mid < k → ∀ (_hk2 : k < lo + mid + (len - mid)),
          x1 ⟨1 + n + k, by omega⟩ = false := by
        intro k hk1 hk2
        have hneR : (⟨1 + n + k, by omega⟩ : Fin (1 + n + n)) ≠ wR := by
          intro h; have := congrArg Fin.val h; dsimp [wR] at this; omega
        dsimp only [x1]
        rw [Function.update_of_ne hneR]
        exact hclean k (by omega) (by omega)
      have hL_act := ih mid hmid_lt lo hmid1 hbL x1 hx1_wL hx1_cleanL
      let x2 : Qubits (1 + n + n) := fun w =>
        if 1 + n + lo ≤ w.1 ∧ w.1 < 1 + n + lo + mid then c else x1 w
      have hL_act' : act (fanoutRange n lo mid hmid1 hbL).1.unitary (ket x1) = ket x2 := hL_act
      rw [hL_act']
      have hx2_wR : x2 wR = c := by
        have hnot : ¬ (1 + n + lo ≤ wR.1 ∧ wR.1 < 1 + n + lo + mid) := by
          dsimp [wR]; omega
        dsimp only [x2]
        rw [if_neg hnot, hx1_wR]
      have hx2_cleanR : ∀ k : ℕ, lo + mid < k → ∀ (_hk2 : k < lo + mid + (len - mid)),
          x2 ⟨1 + n + k, by omega⟩ = false := by
        intro k hk1 hk2
        have hnot : ¬ (1 + n + lo ≤ 1 + n + k ∧ 1 + n + k < 1 + n + lo + mid) := by omega
        dsimp only [x2]
        rw [if_neg hnot]
        exact hx1_cleanR k hk1 hk2
      have hR_act := ih (len - mid) hrem_lt (lo + mid) hrem1 hbR x2 hx2_wR hx2_cleanR
      rw [hR_act]
      congr 1
      funext w
      dsimp only [x2, x1]
      by_cases hwR : 1 + n + (lo + mid) ≤ w.1 ∧ w.1 < 1 + n + (lo + mid) + (len - mid)
      · rw [if_pos hwR, if_pos (by omega)]
      · rw [if_neg hwR]
        by_cases hwL : 1 + n + lo ≤ w.1 ∧ w.1 < 1 + n + lo + mid
        · rw [if_pos hwL, if_pos (by omega)]
        · rw [if_neg hwL, if_neg (by omega)]
          have hneR : w ≠ wR := by
            intro h; apply hwR; rw [h]; dsimp [wR]; omega
          rw [Function.update_of_ne hneR]

private def fanoutTree (n : ℕ) (hn : 1 ≤ n) :
    { lc : LayeredCircuit (1 + n + n) //
      lc.UsesOnly ({0} ∪ ancSlice (1 + n) 0 n) ∧ lc.size = n ∧ lc.depth ≤ Nat.clog 2 n + 1 } :=
  let w0 : Fin (1 + n + n) := ⟨0, by omega⟩
  let a0 : Fin (1 + n + n) := ⟨1 + n, by omega⟩
  have hne : w0 ≠ a0 := by intro h; have := congrArg Fin.val h; dsimp [w0, a0] at this; omega
  let step0 := cnotGate w0 a0 hne
  let tree := fanoutRange n 0 n hn (by omega)
  ⟨step0.seq tree.1,
    LayeredCircuit.seq_usesOnly
      ((cnotGate_usesOnly w0 a0 hne).mono (by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          ancSlice, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rcases hw with rfl | rfl
        · left; exact Fin.ext rfl
        · right; dsimp [a0]; omega))
      (tree.2.mono Finset.subset_union_right),
    by simp only [step0, tree, LayeredCircuit.seq_size, cnotGate_size,
         fanoutRange_size n 0 n hn (by omega)]
       omega,
    by simp only [step0, tree, LayeredCircuit.seq_depth, cnotGate_depth]
       have hd := fanoutRange_depth n 0 n hn (by omega)
       omega⟩

private lemma act_fanoutTree_ket (n : ℕ) (hn : 1 ≤ n) (x : Qubits (1 + n + n))
    (hclean : ∀ j : Fin n, x ⟨1 + n + j.1, by have := j.isLt; omega⟩ = false) :
    act (fanoutTree n hn).1.unitary (ket x) =
      ket (fun w => if 1 + n ≤ w.1 then x 0 else x w) := by
  dsimp only [fanoutTree]
  simp only [LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket]
  let a0 : Fin (1 + n + n) := ⟨1 + n, by omega⟩
  let x1 : Qubits (1 + n + n) := Function.update x a0 (xor (x a0) (x ⟨0, by omega⟩))
  have hx1_a0 : x1 a0 = x 0 := by
    have h0 := hclean ⟨0, hn⟩
    dsimp only [x1]
    rw [Function.update_self]
    change xor (x ⟨1 + n, by omega⟩) (x 0) = x 0
    have h0' : x ⟨1 + n, by omega⟩ = false := h0
    rw [h0', Bool.false_xor]
  have hx1_clean : ∀ k : ℕ, 0 < k → ∀ (_hk2 : k < 0 + n), x1 ⟨1 + n + k, by omega⟩ = false := by
    intro k hk1 hk2
    have hne : (⟨1 + n + k, by omega⟩ : Fin (1 + n + n)) ≠ a0 := by
      intro h; have := congrArg Fin.val h; dsimp [a0] at this; omega
    dsimp only [x1]
    rw [Function.update_of_ne hne]
    exact hclean ⟨k, by omega⟩
  rw [act_fanoutRange_ket n 0 n hn (by omega) (x 0) x1 hx1_a0 hx1_clean]
  congr 1
  funext w
  have hw_iff : (1 + n + 0 ≤ w.1 ∧ w.1 < 1 + n + 0 + n) ↔ 1 + n ≤ w.1 := by
    have := w.isLt; constructor <;> intro <;> omega
  by_cases hw : 1 + n ≤ w.1
  · rw [if_pos (hw_iff.mpr hw), if_pos hw]
  · have hne : w ≠ a0 := fun h => hw (by rw [h])
    rw [if_neg (mt hw_iff.mp hw), if_neg hw]
    dsimp only [x1]
    rw [Function.update_of_ne hne]

private def ctrlHTgtWire (n : ℕ) (i : Fin n) : Fin (1 + n + n) :=
  ⟨1 + i.1, by have := i.isLt; omega⟩

private def ctrlHAncWire (n : ℕ) (i : Fin n) : Fin (1 + n + n) :=
  ⟨1 + n + i.1, by have := i.isLt; omega⟩

private lemma ctrlHAncWire_ne_tgtWire (n : ℕ) (i : Fin n) :
    ctrlHAncWire n i ≠ ctrlHTgtWire n i := by
  intro h; have := congrArg Fin.val h; dsimp [ctrlHAncWire, ctrlHTgtWire] at this; omega

private noncomputable def ctrlHApp (n : ℕ) (i : Fin n) : GateApp gates12 (1 + n + n) :=
  ctrlGate1App hadamard hadamard_mem_unitaryGroup
    (ctrlHAncWire n i) (ctrlHTgtWire n i) (ctrlHAncWire_ne_tgtWire n i)

private lemma ctrlHLayer_entry (n : ℕ) (L : List (Fin n)) (hL : L.Nodup)
    (y z : Qubits (1 + n + n)) :
    Circuit.unitary (L.map (ctrlHApp n)) y z =
      if (∀ w : Fin (1 + n + n), (∀ i ∈ L, w ≠ ctrlHTgtWire n i) → y w = z w) then
        ∏ i ∈ L.toFinset,
          (if z (ctrlHAncWire n i) then hadamard (y (ctrlHTgtWire n i)) (z (ctrlHTgtWire n i))
          else if y (ctrlHTgtWire n i) = z (ctrlHTgtWire n i) then 1 else 0)
      else 0 := by
  classical
  induction L generalizing y z with
  | nil =>
    simp only [List.map_nil, circuit_unitary_nil, Matrix.one_apply, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, true_implies, List.toFinset_nil, Finset.prod_empty]
    by_cases h : y = z
    · subst h; rw [if_pos rfl, if_pos (fun _ => rfl)]
    · rw [if_neg h]
      have hne : ¬ ∀ w : Fin (1 + n + n), y w = z w := fun hw => h (funext hw)
      rw [if_neg hne]
  | cons a rest ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, circuit_unitary_cons, Matrix.mul_apply]
    have hih := ih hL.2
    let ancA := ctrlHAncWire n a
    let tgtA := ctrlHTgtWire n a
    have hneA := ctrlHAncWire_ne_tgtWire n a
    let x₀ : Qubits (1 + n + n) := Function.update z tgtA (y tgtA)
    have hx₀_single : (∑ x : Qubits (1 + n + n),
        Circuit.unitary (rest.map (ctrlHApp n)) y x *
          embedOp (ctrlHApp n a).gate.mat (ctrlHApp n a).wires x z) =
        Circuit.unitary (rest.map (ctrlHApp n)) y x₀ *
          embedOp (ctrlHApp n a).gate.mat (ctrlHApp n a).wires x₀ z := by
      rw [Finset.sum_eq_single x₀]
      · intro x _ hx
        dsimp only [ctrlHApp, ctrlGate1App]
        rw [embedOp_gate2App_entry]
        by_cases hoff : ∀ q : Fin (1 + n + n), q ≠ ancA → q ≠ tgtA → x q = z q
        · rw [if_pos hoff]
          by_cases hxa : x ancA = z ancA
          · by_cases hxta : x tgtA = y tgtA
            · exfalso; apply hx
              funext q
              by_cases hqt : q = tgtA
              · subst hqt; simp [x₀, hxta]
              · by_cases hqa : q = ancA
                · subst hqa; dsimp [x₀]; rw [Function.update_of_ne hneA, hxa]
                · simp [x₀, Function.update_of_ne hqt, hoff q hqa hqt]
            · rw [hih y x]
              have hnot : ¬ ∀ w : Fin (1 + n + n),
                  (∀ i ∈ rest, w ≠ ctrlHTgtWire n i) → y w = x w := by
                intro h
                apply hxta
                refine (h tgtA ?_).symm
                intro i hi heq
                have hv := congrArg Fin.val heq
                dsimp [tgtA, ctrlHTgtWire] at hv
                exact hL.1 (by convert hi using 2; exact Fin.ext (by omega))
              rw [if_neg hnot, zero_mul]
          · dsimp only [controlled, Matrix.of_apply]
            rw [if_neg hxa, mul_zero]
        · rw [if_neg hoff, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hx₀_single, hih y x₀]
    dsimp only [ctrlHApp, ctrlGate1App]
    rw [embedOp_gate2App_entry]
    have hx₀_off : ∀ q : Fin (1 + n + n), q ≠ ancA → q ≠ tgtA → x₀ q = z q :=
      fun q _ hqt => Function.update_of_ne hqt _ _
    rw [if_pos hx₀_off]
    have hx₀_anc : x₀ ancA = z ancA := Function.update_of_ne hneA _ _
    have hx₀_tgt : x₀ tgtA = y tgtA := Function.update_self _ _ _
    dsimp only [controlled, Matrix.of_apply]
    rw [if_pos hx₀_anc, hx₀_anc, hx₀_tgt]
    simp only [Matrix.one_apply]
    have hiff : (∀ w : Fin (1 + n + n), (∀ i ∈ rest, w ≠ ctrlHTgtWire n i) → y w = x₀ w) ↔
        (∀ w : Fin (1 + n + n), (∀ i ∈ a :: rest, w ≠ ctrlHTgtWire n i) → y w = z w) := by
      constructor
      · intro h w hw
        have hwt : w ≠ tgtA := fun heq => hw a List.mem_cons_self heq
        have hwr : ∀ i ∈ rest, w ≠ ctrlHTgtWire n i := fun i hi =>
          hw i (List.mem_cons_of_mem _ hi)
        rw [h w hwr]
        dsimp only [x₀]
        exact Function.update_of_ne hwt _ _
      · intro h w hwr
        by_cases hwt : w = tgtA
        · subst hwt; simp [x₀]
        · have hw : ∀ i ∈ a :: rest, w ≠ ctrlHTgtWire n i := by
            intro i hi
            rcases List.mem_cons.mp hi with rfl | hr
            · exact hwt
            · exact hwr i hr
          rw [h w hw]
          dsimp only [x₀]
          exact (Function.update_of_ne hwt _ _).symm
    by_cases hcond : ∀ w : Fin (1 + n + n), (∀ i ∈ a :: rest, w ≠ ctrlHTgtWire n i) → y w = z w
    · rw [if_pos (hiff.mpr hcond), if_pos hcond, List.toFinset_cons]
      have ha_mem : a ∉ rest.toFinset := by simpa using hL.1
      rw [Finset.prod_insert ha_mem, mul_comm]
      have hprod_rest : (∏ i ∈ rest.toFinset,
            (if x₀ (ctrlHAncWire n i) then hadamard (y (ctrlHTgtWire n i)) (x₀ (ctrlHTgtWire n i))
             else if y (ctrlHTgtWire n i) = x₀ (ctrlHTgtWire n i) then 1 else 0)) =
          (∏ i ∈ rest.toFinset,
            (if z (ctrlHAncWire n i) then hadamard (y (ctrlHTgtWire n i)) (z (ctrlHTgtWire n i))
             else if y (ctrlHTgtWire n i) = z (ctrlHTgtWire n i) then 1 else 0)) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hia : i ≠ a := by intro heq; subst heq; exact ha_mem hi
        have hanc_ne : ctrlHAncWire n i ≠ tgtA := by
          intro h; have := congrArg Fin.val h
          dsimp [ctrlHAncWire, tgtA, ctrlHTgtWire] at this
          have := i.isLt; have := a.isLt; omega
        have htgt_ne : ctrlHTgtWire n i ≠ tgtA := by
          intro h; have := congrArg Fin.val h
          dsimp [ctrlHTgtWire, tgtA] at this
          exact hia (Fin.ext (by omega))
        dsimp only [x₀]
        simp_rw [Function.update_of_ne hanc_ne, Function.update_of_ne htgt_ne]
      rw [hprod_rest]
    · rw [if_neg (mt hiff.mp hcond), if_neg hcond, zero_mul]

private lemma ctrlHLayer_disjoint (n : ℕ) :
    LayerDisjoint ((List.finRange n).map (ctrlHApp n)) := by
  dsimp only [LayerDisjoint]
  rw [List.pairwise_map]
  refine (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange n)).imp fun {i j} hij => ?_
  rw [Set.disjoint_left]
  rintro w ⟨a, rfl⟩ ⟨b, hb⟩
  dsimp only [ctrlHApp, ctrlGate1App, gate2App, Gate.ofMatrix2] at a b hb ⊢
  have hi := i.isLt
  have hj := j.isLt
  have hval := congrArg Fin.val hb.symm
  rcases (by fin_cases a <;> decide : a = 0 ∨ a = 1) with rfl | rfl <;>
    rcases (by fin_cases b <;> decide : b = 0 ∨ b = 1) with rfl | rfl
  · change 1 + n + i.1 = 1 + n + j.1 at hval; exact hij (Fin.ext (by omega))
  · change 1 + n + i.1 = 1 + j.1 at hval; omega
  · change 1 + i.1 = 1 + n + j.1 at hval; omega
  · change 1 + i.1 = 1 + j.1 at hval; exact hij (Fin.ext (by omega))

noncomputable def ctrlHadamardMat (n : ℕ) : Matrix (Qubits (1 + n)) (Qubits (1 + n)) ℂ :=
  Matrix.of fun y z =>
    controlledQubits (hadamardN n)
      (fun i : Fin (n + 1) => y (i.cast (Nat.add_comm n 1)))
      (fun i : Fin (n + 1) => z (i.cast (Nat.add_comm n 1)))

noncomputable def ctrlHadamardN (n : ℕ) : LayeredCircuit (1 + n + n) :=
  if hn : 1 ≤ n then
    let fan := fanoutTree n hn
    let hLayer := LayeredCircuit.ofLayer ((List.finRange n).map (ctrlHApp n)) (ctrlHLayer_disjoint n)
    fan.1.seq (hLayer.seq fan.1.adj)
  else
    LayeredCircuit.id (1 + n + n)

lemma ctrlHadamardN_size (n : ℕ) : (ctrlHadamardN n).size ≤ 3 * n := by
  unfold ctrlHadamardN
  split_ifs with hn
  · simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, LayeredCircuit.ofLayer_size,
      List.length_map, List.length_finRange]
    have hfan := (fanoutTree n hn).2.2.1
    omega
  · simp

lemma ctrlHadamardN_depth (n : ℕ) : (ctrlHadamardN n).depth ≤ 2 * Nat.clog 2 (n + 1) + 3 := by
  unfold ctrlHadamardN
  split_ifs with hn
  · simp only [LayeredCircuit.seq_depth, LayeredCircuit.adj_depth]
    have hfan : (fanoutTree n hn).1.depth ≤ Nat.clog 2 n + 1 := (fanoutTree n hn).2.2.2
    have hclog : Nat.clog 2 n ≤ Nat.clog 2 (n + 1) := Nat.clog_mono_right 2 (by omega)
    have hlay := LayeredCircuit.ofLayer_depth ((List.finRange n).map (ctrlHApp n))
      (ctrlHLayer_disjoint n)
    omega
  · simp

lemma ctrlHadamardN_depth_real (n : ℕ) (hn : 2 ≤ n) :
    ((ctrlHadamardN n).depth : ℝ) ≤ (7 / Real.log 2) * Real.log n := by
  have h1 : 1 ≤ n := by omega
  have hd : ((ctrlHadamardN n).depth : ℝ) ≤ 2 * (Nat.clog 2 (n + 1) : ℝ) + 3 := by
    exact_mod_cast ctrlHadamardN_depth n
  have hclog := clog2_succ_le_real_log h1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ge : 1 ≤ Real.log n / Real.log 2 := by
    rw [one_le_div hlog2_pos]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  calc ((ctrlHadamardN n).depth : ℝ)
      ≤ 2 * (Real.log n / Real.log 2 + 1) + 3 := by linarith
    _ = 2 * (Real.log n / Real.log 2) + 5 := by ring
    _ ≤ 2 * (Real.log n / Real.log 2) + 5 * (Real.log n / Real.log 2) := by linarith
    _ = (7 / Real.log 2) * Real.log n := by ring

theorem ctrlHadamardN_implements (n : ℕ) :
    (ctrlHadamardN n).ImplementsOnClean (ctrlHadamardMat n) := by
  intro y z hz
  by_cases hn : 1 ≤ n
  · simp only [ctrlHadamardN, dif_pos hn]
    let fan := fanoutTree n hn
    let hLayer := LayeredCircuit.ofLayer ((List.finRange n).map (ctrlHApp n)) (ctrlHLayer_disjoint n)
    let withTgt : Qubits (1 + n + n) → Qubits n → Qubits (1 + n + n) := fun x t w =>
      if h : 1 ≤ w.1 ∧ w.1 < 1 + n then t ⟨w.1 - 1, by omega⟩ else x w
    let fanZ : Qubits (1 + n + n) → Qubits (1 + n + n) := fun x w =>
      if 1 + n ≤ w.1 then x 0 else x w
    let tgtPart : Qubits (1 + n + n) → Qubits n := fun x i => x (ctrlHTgtWire n i)
    have hfan_z : act fan.1.unitary (ket z) = ket (fanZ z) :=
      act_fanoutTree_ket n hn z fun j => hz j
    have hmid : act hLayer.unitary (ket (fanZ z)) =
        ∑ t : Qubits n,
          (if z 0 then hadamardN n t (tgtPart z) else if t = tgtPart z then 1 else 0) •
            ket (withTgt (fanZ z) t) := by
      rw [act_ket_eq]
      have hsum : (∑ w : Qubits (1 + n + n), hLayer.unitary w (fanZ z) • ket w) =
          ∑ w ∈ Finset.univ.image (withTgt (fanZ z)), hLayer.unitary w (fanZ z) • ket w := by
        rw [← Finset.sum_subset (Finset.subset_univ _)]
        intro w _ hw
        rw [LayeredCircuit.ofLayer_unitary, ctrlHLayer_entry n (List.finRange n) (List.nodup_finRange n)]
        by_cases hoff : ∀ q : Fin (1 + n + n), (∀ i ∈ List.finRange n, q ≠ ctrlHTgtWire n i) →
            w q = fanZ z q
        · exfalso; apply hw
          rw [Finset.mem_image]
          refine ⟨tgtPart w, Finset.mem_univ _, ?_⟩
          funext q
          dsimp only [withTgt, tgtPart, ctrlHTgtWire]
          split_ifs with hq
          · congr 1; apply Fin.ext; simp; omega
          · refine (hoff q ?_).symm
            intro i _ heq
            have hv := congrArg Fin.val heq
            dsimp [ctrlHTgtWire] at hv
            omega
        · rw [if_neg hoff, zero_smul]
      rw [hsum, Finset.sum_image]
      · refine Finset.sum_congr rfl fun t _ => ?_
        rw [LayeredCircuit.ofLayer_unitary, ctrlHLayer_entry n (List.finRange n) (List.nodup_finRange n)]
        have hoff : ∀ q : Fin (1 + n + n), (∀ i ∈ List.finRange n, q ≠ ctrlHTgtWire n i) →
            withTgt (fanZ z) t q = fanZ z q := by
          intro q hq
          dsimp only [withTgt]
          split_ifs with hq'
          · exfalso
            exact hq ⟨q.1 - 1, by omega⟩ (List.mem_finRange _)
              (Fin.ext (by dsimp [ctrlHTgtWire]; omega))
          · rfl
        rw [if_pos hoff]
        have hfin : (List.finRange n).toFinset = Finset.univ := by ext i; simp
        rw [hfin]
        have hfan_anc : ∀ i : Fin n, fanZ z (ctrlHAncWire n i) = z 0 := fun i => by
          dsimp only [fanZ, ctrlHAncWire]; rw [if_pos (by omega)]
        have hwt_tgt : ∀ i : Fin n, withTgt (fanZ z) t (ctrlHTgtWire n i) = t i := fun i => by
          dsimp only [withTgt, ctrlHTgtWire]
          have hi := i.isLt
          rw [dif_pos (by omega)]
          congr 1; exact Fin.ext (by simp)
        have hfz_tgt : ∀ i : Fin n, fanZ z (ctrlHTgtWire n i) = tgtPart z i := fun i => by
          dsimp only [fanZ, tgtPart, ctrlHTgtWire]
          have hi := i.isLt
          rw [if_neg (by omega)]
        simp_rw [hfan_anc, hwt_tgt, hfz_tgt]
        congr 1
        cases hz0 : z 0
        · simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases ht : t = tgtPart z
          · subst ht; simp
          · simp only [ht, ↓reduceIte]
            have hex : ∃ i : Fin n, t i ≠ tgtPart z i := by
              by_contra h; apply ht; funext i; by_contra hi; exact h ⟨i, hi⟩
            rcases hex with ⟨i₀, hi₀⟩
            exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])
        · simp only [↓reduceIte, hadamard_prod_eq_hadamardN]
      · intro t1 _ t2 _ ht
        funext i
        have hi := congrFun ht (ctrlHTgtWire n i)
        dsimp only [withTgt, ctrlHTgtWire] at hi
        have his := i.isLt
        rw [dif_pos (by omega), dif_pos (by omega)] at hi
        simpa using hi
    have hfan_adj : ∀ t : Qubits n,
        act fan.1.adj.unitary (ket (withTgt (fanZ z) t)) = ket (withTgt z t) := by
      intro t
      have hwith_clean : ∀ j : Fin n,
          withTgt z t ⟨1 + n + j.1, by have := j.isLt; omega⟩ = false := fun j => by
        dsimp only [withTgt]
        rw [dif_neg (by omega)]
        exact hz j
      have hfan_wt := act_fanoutTree_ket n hn (withTgt z t) hwith_clean
      have hfan_eq : (fun w => if 1 + n ≤ w.1 then withTgt z t 0 else withTgt z t w) =
          withTgt (fanZ z) t := by
        funext w
        by_cases h1 : 1 ≤ w.1 ∧ w.1 < 1 + n
        · dsimp only [withTgt]
          rw [if_neg (by omega), dif_pos h1, dif_pos h1]
        · dsimp only [withTgt, fanZ]
          rw [dif_neg h1]
          by_cases h2 : 1 + n ≤ w.1
          · rw [if_pos h2, if_pos h2, dif_neg (by simp), dif_neg h1]
          · rw [if_neg h2, if_neg h2, dif_neg h1]
      rw [hfan_eq] at hfan_wt
      rw [← hfan_wt, ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp fan.1.unitary_mem_unitaryGroup, act_one]
    have htot : act (fan.1.seq (hLayer.seq fan.1.adj)).unitary (ket z) =
        ∑ t : Qubits n,
          (if z 0 then hadamardN n t (tgtPart z) else if t = tgtPart z then 1 else 0) •
            ket (withTgt z t) := by
      simp only [LayeredCircuit.seq_unitary, act_mul, hfan_z, hmid, act_sum, act_smul, hfan_adj]
    have hentry : (fan.1.seq (hLayer.seq fan.1.adj)).unitary y z =
        inner ℂ (ket y) (act (fan.1.seq (hLayer.seq fan.1.adj)).unitary (ket z)) := by
      rw [act_ket_eq, inner_sum]
      simp [inner_smul_right, ket, EuclideanSpace.inner_single_left]
    rw [hentry, htot, inner_sum]
    simp only [inner_smul_right, ket, EuclideanSpace.inner_single_left, PiLp.single_apply,
      map_one, mul_ite, mul_one, mul_zero]
    by_cases hy : ∀ j : Fin n, y (Fin.natAdd (1 + n) j) = false
    · rw [if_pos hy]
      have h_off : ∀ (t : Qubits n), withTgt z t = y ↔ (y 0 = z 0 ∧ t = tgtPart y) := by
        intro t
        constructor
        · intro heq
          refine ⟨by rw [← heq]; simp [withTgt], ?_⟩
          funext i
          have his := i.isLt
          have := congrFun heq (ctrlHTgtWire n i)
          dsimp [withTgt, tgtPart, ctrlHTgtWire] at this ⊢
          rw [dif_pos (by omega)] at this
          simpa using this
        · rintro ⟨h0, rfl⟩
          funext w
          dsimp only [withTgt, tgtPart, ctrlHTgtWire]
          by_cases hw : 1 ≤ w.1 ∧ w.1 < 1 + n
          · rw [dif_pos hw]; congr 1; apply Fin.ext; simp; omega
          · rw [dif_neg hw]
            by_cases hw0 : w.1 = 0
            · have : w = ⟨0, by omega⟩ := Fin.ext hw0
              rw [this]; exact h0.symm
            · have hwlt := w.isLt
              have hj : ∃ j : Fin n, w = Fin.natAdd (1 + n) j :=
                ⟨⟨w.1 - (1 + n), by omega⟩, Fin.ext (by simp; omega)⟩
              rcases hj with ⟨j, rfl⟩
              rw [hz j, hy j]
      have hcast0_y : y (Fin.castAdd n ((0 : Fin (n + 1)).cast (Nat.add_comm n 1))) = y 0 := rfl
      have hcast0_z : z (Fin.castAdd n ((0 : Fin (n + 1)).cast (Nat.add_comm n 1))) = z 0 := rfl
      have htail_y : Fin.tail (fun i : Fin (n + 1) =>
          y (Fin.castAdd n (i.cast (Nat.add_comm n 1)))) = tgtPart y := by
        funext i; dsimp [Fin.tail, tgtPart, ctrlHTgtWire]; congr 1; exact Fin.ext (by simp; omega)
      have htail_z : Fin.tail (fun i : Fin (n + 1) =>
          z (Fin.castAdd n (i.cast (Nat.add_comm n 1)))) = tgtPart z := by
        funext i; dsimp [Fin.tail, tgtPart, ctrlHTgtWire]; congr 1; exact Fin.ext (by simp; omega)
      by_cases hy0 : y 0 = z 0
      · rw [Finset.sum_eq_single (tgtPart y)]
        · have heq : withTgt z (tgtPart y) = y := (h_off (tgtPart y)).mpr ⟨hy0, rfl⟩
          rw [if_pos heq.symm]
          simp only [ctrlHadamardMat, Matrix.of_apply, controlledQubits, controlled,
            Matrix.submatrix_apply, hcast0_y, hcast0_z, htail_y, htail_z, if_pos hy0]
          cases hz0 : z 0
          · have hyf : y 0 = false := hy0.trans hz0
            simp only [hyf, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply, htail_y, htail_z]
          · have hyt : y 0 = true := hy0.trans hz0
            simp only [hyt, ↓reduceIte]
        · intro t _ ht
          have hne : withTgt z t ≠ y := fun h => ht ((h_off t).mp h).2
          rw [if_neg hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have hzero_sum : (∑ t : Qubits n,
            (if y = withTgt z t then
              if z 0 then hadamardN n t (tgtPart z) else if t = tgtPart z then 1 else 0
            else 0)) = 0 := by
          refine Finset.sum_eq_zero fun t _ => ?_
          have hne : withTgt z t ≠ y := fun h => hy0 ((h_off t).mp h).1
          rw [if_neg hne.symm]
        rw [hzero_sum]
        simp only [ctrlHadamardMat, Matrix.of_apply, controlledQubits, controlled,
          Matrix.submatrix_apply, hcast0_y, hcast0_z, if_neg hy0]
    · rw [if_neg hy]
      refine Finset.sum_eq_zero fun t _ => ?_
      have hne : withTgt z t ≠ y := by
        intro h
        apply hy
        intro j
        rw [← h]
        dsimp only [withTgt]
        rw [dif_neg (by simp)]
        exact hz j
      rw [if_neg hne.symm]
  · simp only [ctrlHadamardN, dif_neg hn]
    have hn0 : n = 0 := by omega
    subst hn0
    have htru : ∀ j : Fin 0, y (Fin.natAdd (1 + 0) j) = false := fun j => Fin.elim0 j
    rw [if_pos htru]
    simp only [LayeredCircuit.id_unitary, Matrix.one_apply, ctrlHadamardMat, Matrix.of_apply,
      controlledQubits, controlled, Matrix.submatrix_apply]
    have hcast0 : ∀ x : Qubits 1, x (Fin.castAdd 0 ((0 : Fin 1).cast (Nat.add_comm 0 1))) = x 0 :=
      fun _ => rfl
    rw [hcast0 y, hcast0 z]
    by_cases h : y = z
    · subst h; rw [if_pos rfl, if_pos rfl]
      cases h0 : y 0
      · simp
      · simp [hadamardN, dotBits]
    · have h0_ne : y 0 ≠ z 0 := fun h0 => h (funext fun i => by fin_cases i; exact h0)
      rw [if_neg h, if_neg h0_ne]


/-! ### 13. Multi-Controlled Single-Qubit Unitary (`multiEqCtrl1`) -/

lemma circuit_preserves_wire {m : ℕ} (c : Circuit gates12 m) (t : Fin m)
    (ht : ∀ g ∈ c, t ∉ Set.range g.wires) (y z : Qubits m) (hne : y t ≠ z t) :
    Circuit.unitary c y z = 0 := by
  induction c generalizing y z with
  | nil =>
    rw [circuit_unitary_nil, Matrix.one_apply]
    have hyz : y ≠ z := fun h => hne (congrFun h t)
    rw [if_neg hyz]
  | cons g rest ih =>
    rw [circuit_unitary_cons, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hgt : t ∉ Set.range g.wires := ht g List.mem_cons_self
    have hrest : ∀ g' ∈ rest, t ∉ Set.range g'.wires := fun g' hg' =>
      ht g' (List.mem_cons_of_mem _ hg')
    by_cases hxt : x t = z t
    · have hyx : y t ≠ x t := fun h => hne (h.trans hxt)
      rw [ih hrest y x hyx, zero_mul]
    · have h0 : embedOp g.gate.mat g.wires x z = 0 := by
        simp only [embedOp, Matrix.of_apply]
        rw [if_neg (fun h => hxt (h t hgt))]
      rw [h0, mul_zero]

lemma act_ket_update_of_not_mem {m : ℕ} (lc : LayeredCircuit m) {S : Finset (Fin m)}
    (hS : lc.UsesOnly S) (t : Fin m) (ht : t ∉ S)
    {x x' : Qubits m} (hact : act lc.unitary (ket x) = ket x') (b : Bool) :
    act lc.unitary (ket (Function.update x t b)) = ket (Function.update x' t b) := by
  have hnot_wires : ∀ g ∈ lc.toCircuit, t ∉ Set.range g.wires := by
    intro g hg ⟨i, hi⟩
    rw [LayeredCircuit.toCircuit, List.mem_flatten] at hg
    rcases hg with ⟨L, hL, hgL⟩
    exact ht (hi ▸ hS L hL g hgL i)
  have hxt : x' t = x t := by
    by_contra hne
    have hzero := circuit_preserves_wire lc.toCircuit t hnot_wires x' x hne
    have hket : (act lc.unitary (ket x)) x' = 1 := by rw [hact]; simp [ket]
    have hket' : (act lc.unitary (ket x)) x' = lc.unitary x' x := by
      have hinner : (act lc.unitary (ket x)) x' = inner ℂ (ket x') (act lc.unitary (ket x)) := by
        simp [ket, EuclideanSpace.inner_single_left]
      rw [hinner, act_ket_eq, inner_sum]
      simp [inner_smul_right, ket, EuclideanSpace.inner_single_left]
    have h0' : lc.unitary x' x = 0 := hzero
    rw [hket', h0'] at hket
    exact one_ne_zero hket.symm
  have hcomm : lc.unitary * (pauliXGate t).unitary = (pauliXGate t).unitary * lc.unitary := by
    apply LayeredCircuit.circuit_comm_of_disjoint
    intro g1 hg1 g2 hg2
    simp only [pauliXGate, LayeredCircuit.single, LayeredCircuit.toCircuit, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.mem_singleton] at hg2
    subst hg2
    rw [Set.disjoint_left]
    rintro w hw1 ⟨i, hi⟩
    have hwt : w = t := by
      have : (pauliXApp t).wires i = t := rfl
      rw [← hi, this]
    subst hwt
    exact hnot_wires g1 hg1 hw1
  by_cases hb : b = x t
  · have hx_eq : Function.update x t b = x := by
      funext w
      by_cases hw : w = t
      · subst hw; simp [hb]
      · exact Function.update_of_ne hw _ _
    have hx'_eq : Function.update x' t b = x' := by
      funext w
      by_cases hw : w = t
      · subst hw; simp [hb, hxt]
      · exact Function.update_of_ne hw _ _
    rw [hx_eq, hx'_eq, hact]
  · have hbx : b = !x t := by
      revert hb; cases x t <;> cases b <;> decide
    have hbx' : b = !x' t := by rw [hbx, hxt]
    have hkx : ket (Function.update x t b) = act (pauliXGate t).unitary (ket x) := by
      rw [act_pauliXGate_ket, hbx]
    have hkx' : ket (Function.update x' t b) = act (pauliXGate t).unitary (ket x') := by
      rw [act_pauliXGate_ket, hbx']
    rw [hkx, ← act_mul, hcomm, act_mul, hact, ← hkx']

private lemma foldl_update_apply {m : ℕ} (L : List (Fin m)) (val f : Fin m → Bool) (w : Fin m) :
    L.foldl (fun g t => Function.update g t (val t)) f w = if w ∈ L then val w else f w := by
  induction L generalizing f with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases hr : w ∈ rest
    · simp [hr]
    · by_cases hwa : w = a
      · subst hwa; simp [hr]
      · simp [hr, hwa]

private lemma act_ket_updateList_of_not_mem {m : ℕ} (lc : LayeredCircuit m) {S : Finset (Fin m)}
    (hS : lc.UsesOnly S) {x x' : Qubits m} (hact : act lc.unitary (ket x) = ket x')
    (L : List (Fin m)) (hL : ∀ t ∈ L, t ∉ S) (val : Fin m → Bool) :
    act lc.unitary (ket (L.foldl (fun g t => Function.update g t (val t)) x)) =
      ket (L.foldl (fun g t => Function.update g t (val t)) x') := by
  induction L generalizing x x' with
  | nil => exact hact
  | cons a rest ih =>
    simp only [List.foldl_cons]
    exact ih
      (act_ket_update_of_not_mem lc hS a (hL a List.mem_cons_self) hact (val a))
      (fun t ht => hL t (List.mem_cons_of_mem _ ht))

lemma act_ket_agree_on_usesOnly {m : ℕ} (lc : LayeredCircuit m) {S : Finset (Fin m)}
    (hS : lc.UsesOnly S) {x₁ x₁' x₂ : Qubits m}
    (hact : act lc.unitary (ket x₁) = ket x₁')
    (hagree : ∀ w ∈ S, x₂ w = x₁ w) :
    act lc.unitary (ket x₂) = ket (fun w => if w ∈ S then x₁' w else x₂ w) := by
  classical
  let L : List (Fin m) := (Finset.univ.filter (fun w : Fin m => w ∉ S)).toList
  have hL : ∀ t ∈ L, t ∉ S := by
    intro t ht
    simpa [L] using ht
  have hx1 : L.foldl (fun g t => Function.update g t (x₂ t)) x₁ = x₂ := by
    funext w
    rw [foldl_update_apply]
    by_cases hw : w ∈ S
    · have hwL : w ∉ L := fun h => hL w h hw
      rw [if_neg hwL, hagree w hw]
    · have hwL : w ∈ L := by simp [L, hw]
      rw [if_pos hwL]
  have hx1' : L.foldl (fun g t => Function.update g t (x₂ t)) x₁' =
      (fun w => if w ∈ S then x₁' w else x₂ w) := by
    funext w
    rw [foldl_update_apply]
    by_cases hw : w ∈ S
    · have hwL : w ∉ L := fun h => hL w h hw
      rw [if_neg hwL, if_pos hw]
    · have hwL : w ∈ L := by simp [L, hw]
      rw [if_pos hwL, if_neg hw]
  have h := act_ket_updateList_of_not_mem lc hS hact L hL x₂
  rwa [hx1, hx1'] at h

def eqCtrlMat (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ) :
    Matrix (Qubits (L + 1)) (Qubits (L + 1)) ℂ :=
  Matrix.of fun y z =>
    if ∀ i : Fin L, y ⟨i.1, by omega⟩ = z ⟨i.1, by omega⟩ then
      if ∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i then U (y ⟨L, by omega⟩) (z ⟨L, by omega⟩)
      else if y ⟨L, by omega⟩ = z ⟨L, by omega⟩ then 1 else 0
    else 0

private def treeOut (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L) : Fin (L + 1 + L) :=
  if len = 1 then ⟨lo, by omega⟩ else ⟨L + 1 + (lo + len / 2 - 1), by omega⟩

private def treeSupport (L lo len : ℕ) : Finset (Fin (L + 1 + L)) :=
  Finset.univ.filter fun w =>
    (lo ≤ w.1 ∧ w.1 < lo + len) ∨ (L + 1 + lo ≤ w.1 ∧ w.1 + 1 < L + 1 + lo + len)

private lemma mem_treeSupport_iff {L lo len : ℕ} {w : Fin (L + 1 + L)} :
    w ∈ treeSupport L lo len ↔
      (lo ≤ w.1 ∧ w.1 < lo + len) ∨ (L + 1 + lo ≤ w.1 ∧ w.1 + 1 < L + 1 + lo + len) := by
  simp [treeSupport]

private lemma treeOut_mem_treeSupport (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L) :
    treeOut L lo len hlen hb ∈ treeSupport L lo len := by
  rw [mem_treeSupport_iff]
  unfold treeOut
  split_ifs with h1
  · left; simp; omega
  · right; simp; omega

private lemma treeSupport_disjoint (L lo len : ℕ) (hb : lo + len ≤ L) :
    Disjoint (treeSupport L lo (len / 2)) (treeSupport L (lo + len / 2) (len - len / 2)) := by
  rw [Finset.disjoint_left]
  intro w hwL hwR
  rw [mem_treeSupport_iff] at hwL hwR
  omega

private lemma treeSupport_left_subset (L lo len : ℕ) :
    treeSupport L lo (len / 2) ⊆ treeSupport L lo len := by
  intro w hw
  rw [mem_treeSupport_iff] at hw ⊢
  omega

private lemma treeSupport_right_subset (L lo len : ℕ) :
    treeSupport L (lo + len / 2) (len - len / 2) ⊆ treeSupport L lo len := by
  intro w hw
  rw [mem_treeSupport_iff] at hw ⊢
  omega

private lemma treeOut_not_mem_left (L lo len : ℕ) (hlen2 : 2 ≤ len) (hb : lo + len ≤ L) :
    treeOut L lo len (by omega) hb ∉ treeSupport L lo (len / 2) := by
  intro h
  rw [mem_treeSupport_iff] at h
  simp only [treeOut, show len ≠ 1 by omega, ↓reduceIte] at h
  omega

private lemma treeOut_not_mem_right (L lo len : ℕ) (hlen2 : 2 ≤ len) (hb : lo + len ≤ L) :
    treeOut L lo len (by omega) hb ∉ treeSupport L (lo + len / 2) (len - len / 2) := by
  intro h
  rw [mem_treeSupport_iff] at h
  simp only [treeOut, show len ≠ 1 by omega, ↓reduceIte] at h
  omega

private noncomputable def andTree (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L) :
    { lc : LayeredCircuit (L + 1 + L) // lc.UsesOnly (treeSupport L lo len) } :=
  if h2 : len < 2 then
    ⟨LayeredCircuit.id (L + 1 + L), LayeredCircuit.id_usesOnly _⟩
  else
    let mid := len / 2
    have hlen2 : 2 ≤ len := by omega
    have hmid1 : 1 ≤ mid := by omega
    have hrem1 : 1 ≤ len - mid := by omega
    have hbL : lo + mid ≤ L := by omega
    have hbR : lo + mid + (len - mid) ≤ L := by omega
    let lcL := andTree L lo mid hmid1 hbL
    let lcR := andTree L (lo + mid) (len - mid) hrem1 hbR
    let merged := LayeredCircuit.parMerge lcL.1 lcR.1 lcL.2 lcR.2
      (treeSupport_disjoint L lo len hb)
    let outL := treeOut L lo mid hmid1 hbL
    let outR := treeOut L (lo + mid) (len - mid) hrem1 hbR
    let out := treeOut L lo len hlen hb
    have hLR : outL ≠ outR := by
      intro heq
      have h1 := treeOut_mem_treeSupport L lo mid hmid1 hbL
      have h2' := treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR
      change outL ∈ treeSupport L lo mid at h1
      rw [heq] at h1
      exact Finset.disjoint_left.mp (treeSupport_disjoint L lo len hb) h1 h2'
    have hLo : outL ≠ out := by
      intro heq
      have h1 := treeOut_mem_treeSupport L lo mid hmid1 hbL
      change outL ∈ treeSupport L lo mid at h1
      rw [heq] at h1
      exact treeOut_not_mem_left L lo len hlen2 hb h1
    have hRo : outR ≠ out := by
      intro heq
      have h2' := treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR
      change outR ∈ treeSupport L (lo + mid) (len - mid) at h2'
      rw [heq] at h2'
      exact treeOut_not_mem_right L lo len hlen2 hb h2'
    let tof := toffoliOn outL outR out hLR hLo hRo
    have hmerged_uses : merged.UsesOnly (treeSupport L lo len) :=
      (LayeredCircuit.parMerge_usesOnly lcL.1 lcR.1 lcL.2 lcR.2 _).mono
        (Finset.union_subset (treeSupport_left_subset L lo len) (treeSupport_right_subset L lo len))
    have htof_uses : tof.UsesOnly (treeSupport L lo len) := by
      refine (toffoliOn_usesOnly outL outR out hLR hLo hRo).mono ?_
      rw [Finset.insert_subset_iff, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨treeSupport_left_subset L lo len (treeOut_mem_treeSupport L lo mid hmid1 hbL),
        treeSupport_right_subset L lo len (treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR),
        treeOut_mem_treeSupport L lo len hlen hb⟩
    ⟨merged.seq tof, LayeredCircuit.seq_usesOnly hmerged_uses htof_uses⟩
termination_by len
decreasing_by all_goals omega

private lemma andTree_size (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L) :
    (andTree L lo len hlen hb).1.size = 5 * (len - 1) := by
  induction len using Nat.strong_induction_on generalizing lo with
  | h len ih =>
    unfold andTree
    split_ifs with h2
    · simp; omega
    · dsimp only
      have hsL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have hsR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      simp only [LayeredCircuit.seq_size, LayeredCircuit.parMerge_size, toffoliOn_size]
      rw [hsL, hsR]
      omega

private lemma andTree_depth (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L) :
    (andTree L lo len hlen hb).1.depth ≤ 5 * Nat.clog 2 len := by
  induction len using Nat.strong_induction_on generalizing lo with
  | h len ih =>
    unfold andTree
    split_ifs with h2
    · simp
    · dsimp only
      have hlen2 : 2 ≤ len := by omega
      have hdL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have hdR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      have hL_le : (andTree L lo (len / 2) (by omega) (by omega)).1.depth ≤
          5 * Nat.clog 2 ((len + 1) / 2) :=
        le_trans hdL (Nat.mul_le_mul_left 5 clog2_half_le)
      have hclog_sub : Nat.clog 2 (len - len / 2) = Nat.clog 2 ((len + 1) / 2) := by
        congr 1; omega
      have hR_le : (andTree L (lo + len / 2) (len - len / 2) (by omega) (by omega)).1.depth ≤
          5 * Nat.clog 2 ((len + 1) / 2) := by
        have := hdR; rw [hclog_sub] at this; exact this
      have hrec := clog2_rec hlen2
      simp only [LayeredCircuit.seq_depth, LayeredCircuit.parMerge_depth, toffoliOn_depth]
      have hmax := max_le hL_le hR_le
      omega

private lemma andTree_ket (L lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ L)
    (z : Qubits (L + 1 + L))
    (hclean : ∀ w ∈ treeSupport L lo len, L + 1 ≤ w.1 → z w = false) :
    ∃ z' : Qubits (L + 1 + L),
      act (andTree L lo len hlen hb).1.unitary (ket z) = ket z' ∧
      (∀ w, w ∉ treeSupport L lo len → z' w = z w) ∧
      (∀ (k : ℕ), lo ≤ k → ∀ (_hk2 : k < lo + len), z' ⟨k, by omega⟩ = z ⟨k, by omega⟩) ∧
      z' (treeOut L lo len hlen hb) =
        decide (∀ i : Fin L, lo ≤ i.1 → i.1 < lo + len →
          z ⟨i.1, by have := i.isLt; omega⟩ = true) := by
  induction len using Nat.strong_induction_on generalizing lo z with
  | h len ih =>
    unfold andTree
    split_ifs with h2
    · have hlen1 : len = 1 := by omega
      subst hlen1
      refine ⟨z, by simp only [LayeredCircuit.id_unitary, act_one], fun _ _ => rfl,
        fun _ _ _ => rfl, ?_⟩
      simp only [treeOut, ↓reduceIte]
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      cases hz : z ⟨lo, by omega⟩
      · simp only [Bool.false_eq_true, false_iff, not_forall]
        exact ⟨⟨lo, by omega⟩, le_rfl, Nat.lt_succ_self lo, by simp [hz]⟩
      · simp only [true_iff]
        intro i hi1 hi2
        have hk : i.1 = lo := by omega
        have heq : (⟨i.1, by have := i.isLt; omega⟩ : Fin (L + 1 + L)) = ⟨lo, by omega⟩ :=
          Fin.ext hk
        rw [heq, hz]
    · dsimp only
      set mid := len / 2
      have hlen2 : 2 ≤ len := by omega
      have hmid1 : 1 ≤ mid := by omega
      have hrem1 : 1 ≤ len - mid := by omega
      have hmid_lt : mid < len := by omega
      have hrem_lt : len - mid < len := by omega
      have hbL : lo + mid ≤ L := by omega
      have hbR : lo + mid + (len - mid) ≤ L := by omega
      let lcL := andTree L lo mid hmid1 hbL
      let lcR := andTree L (lo + mid) (len - mid) hrem1 hbR
      let outL := treeOut L lo mid hmid1 hbL
      let outR := treeOut L (lo + mid) (len - mid) hrem1 hbR
      let out := treeOut L lo len hlen hb
      have hcleanL : ∀ w ∈ treeSupport L lo mid, L + 1 ≤ w.1 → z w = false := fun w hw =>
        hclean w (treeSupport_left_subset L lo len hw)
      rcases ih mid hmid_lt lo hmid1 hbL z hcleanL with
        ⟨zL, hactL, houtL, haddrL, hresL⟩
      have hcleanR_z : ∀ w ∈ treeSupport L (lo + mid) (len - mid), L + 1 ≤ w.1 → z w = false :=
        fun w hw => hclean w (treeSupport_right_subset L lo len hw)
      rcases ih (len - mid) hrem_lt (lo + mid) hrem1 hbR z hcleanR_z with
        ⟨zR0, hactR0, houtR0, haddrR0, hresR0⟩
      let z2 : Qubits (L + 1 + L) := fun w =>
        if w ∈ treeSupport L (lo + mid) (len - mid) then zR0 w else zL w
      have hagreeR : ∀ w ∈ treeSupport L (lo + mid) (len - mid), zL w = z w := fun w hw =>
        houtL w (Finset.disjoint_right.mp (treeSupport_disjoint L lo len hb) hw)
      have hactR : act lcR.1.unitary (ket zL) = ket z2 :=
        act_ket_agree_on_usesOnly lcR.1 lcR.2 hactR0 hagreeR
      have hmerged_act : act (LayeredCircuit.parMerge lcL.1 lcR.1 lcL.2 lcR.2
          (treeSupport_disjoint L lo len hb)).unitary (ket z) = ket z2 := by
        rw [LayeredCircuit.parMerge_unitary, act_mul, hactL, hactR]
      have hLR : outL ≠ outR := by
        intro heq
        have h1 := treeOut_mem_treeSupport L lo mid hmid1 hbL
        have h2' := treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR
        change outL ∈ treeSupport L lo mid at h1
        rw [heq] at h1
        exact Finset.disjoint_left.mp (treeSupport_disjoint L lo len hb) h1 h2'
      have hLo : outL ≠ out := by
        intro heq
        have h1 := treeOut_mem_treeSupport L lo mid hmid1 hbL
        change outL ∈ treeSupport L lo mid at h1
        rw [heq] at h1
        exact treeOut_not_mem_left L lo len hlen2 hb h1
      have hRo : outR ≠ out := by
        intro heq
        have h2' := treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR
        change outR ∈ treeSupport L (lo + mid) (len - mid) at h2'
        rw [heq] at h2'
        exact treeOut_not_mem_right L lo len hlen2 hb h2'
      let tof := toffoliOn outL outR out hLR hLo hRo
      let z' : Qubits (L + 1 + L) :=
        Function.update z2 out (xor (z2 out) (z2 outL && z2 outR))
      have htot_act : act ((LayeredCircuit.parMerge lcL.1 lcR.1 lcL.2 lcR.2
          (treeSupport_disjoint L lo len hb)).seq tof).unitary (ket z) = ket z' := by
        rw [LayeredCircuit.seq_unitary, act_mul, hmerged_act]
        exact act_toffoliOn_ket outL outR out hLR hLo hRo z2
      refine ⟨z', htot_act, ?_, ?_, ?_⟩
      · intro w hw
        have hwL : w ∉ treeSupport L lo mid := fun h => hw (treeSupport_left_subset L lo len h)
        have hwR : w ∉ treeSupport L (lo + mid) (len - mid) :=
          fun h => hw (treeSupport_right_subset L lo len h)
        have hw_out : w ≠ out := fun h => hw (h ▸ treeOut_mem_treeSupport L lo len hlen hb)
        dsimp only [z', z2]
        rw [Function.update_of_ne hw_out, if_neg hwR, houtL w hwL]
      · intro k hk1 hk2
        have hk_out : (⟨k, by omega⟩ : Fin (L + 1 + L)) ≠ out := by
          intro h
          have := congrArg Fin.val h
          simp only [out, treeOut, show len ≠ 1 by omega, ↓reduceIte] at this
          omega
        dsimp only [z', z2]
        rw [Function.update_of_ne hk_out]
        by_cases hkL : k < lo + mid
        · have hkR : (⟨k, by omega⟩ : Fin (L + 1 + L)) ∉ treeSupport L (lo + mid) (len - mid) := by
            rw [mem_treeSupport_iff]; simp; omega
          rw [if_neg hkR]
          exact haddrL k hk1 hkL
        · have hkR : (⟨k, by omega⟩ : Fin (L + 1 + L)) ∈ treeSupport L (lo + mid) (len - mid) := by
            rw [mem_treeSupport_iff]; left; simp; omega
          rw [if_pos hkR]
          exact haddrR0 k (by omega) (by omega)
      · dsimp only [z']
        rw [Function.update_self]
        have hout_clean : z2 out = false := by
          have hout_notL := treeOut_not_mem_left L lo len hlen2 hb
          have hout_notR := treeOut_not_mem_right L lo len hlen2 hb
          dsimp only [z2]
          rw [if_neg hout_notR, houtL out hout_notL]
          exact hclean out (treeOut_mem_treeSupport L lo len hlen hb) (by
            simp [out, treeOut, show len ≠ 1 by omega])
        have hz2_outL : z2 outL = zL outL := by
          have hnotR : outL ∉ treeSupport L (lo + mid) (len - mid) :=
            Finset.disjoint_left.mp (treeSupport_disjoint L lo len hb)
              (treeOut_mem_treeSupport L lo mid hmid1 hbL)
          dsimp only [z2]; rw [if_neg hnotR]
        have hz2_outR : z2 outR = zR0 outR := by
          have hinR := treeOut_mem_treeSupport L (lo + mid) (len - mid) hrem1 hbR
          dsimp only [z2]; rw [if_pos hinR]
        rw [hout_clean, hz2_outL, hz2_outR, hresL, hresR0, Bool.false_xor]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨hL_all, hR_all⟩ i hi1 hi2
          by_cases hk : i.1 < lo + mid
          · exact hL_all i hi1 hk
          · exact hR_all i (by omega) (by omega)
        · intro h_all
          exact ⟨fun i hi1 hi2 => h_all i hi1 (by omega),
            fun i hi1 hi2 => h_all i (by omega) (by omega)⟩

private def flipPatLayer (L : ℕ) (pat : Qubits L) :
    { lc : LayeredCircuit (L + 1 + L) //
      lc.UsesOnly (Finset.univ.filter fun w : Fin (L + 1 + L) => w.1 < L) ∧
      lc.size ≤ L ∧
      lc.depth ≤ 1 } :=
  let idxs : List (Fin L) := (List.finRange L).filter fun i => !pat i
  let apps : List (GateApp gates12 (L + 1 + L)) :=
    idxs.map fun i => pauliXApp ⟨i.1, by have := i.isLt; omega⟩
  have hnodup : idxs.Nodup := (List.nodup_finRange L).filter _
  have hdisj : LayerDisjoint apps := by
    dsimp only [LayerDisjoint, apps]
    rw [List.pairwise_map]
    refine (List.nodup_iff_pairwise_ne.mp hnodup).imp fun {i j} hij => ?_
    rw [Set.disjoint_left]
    rintro w ⟨a, rfl⟩ ⟨b, hb⟩
    have hi := i.isLt
    have hj := j.isLt
    have hval : (wire1Emb (⟨i.1, by omega⟩ : Fin (L + 1 + L)) a).1 =
        (wire1Emb (⟨j.1, by omega⟩ : Fin (L + 1 + L)) b).1 := congrArg Fin.val hb.symm
    simp [wire1Emb] at hval
    exact hij (Fin.ext hval)
  let lc := LayeredCircuit.ofLayer apps hdisj
  have huses : lc.UsesOnly (Finset.univ.filter fun w : Fin (L + 1 + L) => w.1 < L) := by
    apply LayeredCircuit.ofLayer_usesOnly
    intro g hg a
    simp only [apps, List.mem_map] at hg
    rcases hg with ⟨i, _, rfl⟩
    simp [pauliXApp, gate1App, wire1Emb]
    exact i.isLt
  have hsize : lc.size ≤ L := by
    simp only [lc, LayeredCircuit.ofLayer_size, apps, List.length_map, idxs]
    calc ((List.finRange L).filter fun i => !pat i).length
        ≤ (List.finRange L).length := List.length_filter_le _ _
      _ = L := List.length_finRange
  have hdepth : lc.depth ≤ 1 := by
    simpa only [lc] using LayeredCircuit.ofLayer_depth apps hdisj
  ⟨lc, huses, hsize, hdepth⟩

private lemma act_flipPatLayer_ket (L : ℕ) (pat : Qubits L) (x : Qubits (L + 1 + L)) :
    act (flipPatLayer L pat).1.unitary (ket x) =
      ket (fun w => if hw : w.1 < L then (if pat ⟨w.1, hw⟩ then x w else !x w) else x w) := by
  classical
  dsimp only [flipPatLayer]
  rw [LayeredCircuit.ofLayer_unitary, act_ket_eq]
  let idxs : List (Fin L) := (List.finRange L).filter fun i => !pat i
  let ws : List (Fin (L + 1 + L)) := idxs.map fun i => ⟨i.1, by have := i.isLt; omega⟩
  have hws_nodup : ws.Nodup :=
    ((List.nodup_finRange L).filter _).map fun a b hab => Fin.ext (by
      have := congrArg Fin.val hab; simpa using this)
  have happs_eq : (idxs.map fun i : Fin L => pauliXApp (⟨i.1, by have := i.isLt; omega⟩ : Fin (L + 1 + L))) =
      ws.map fun w => gate1App pauliX pauliX_mem_unitaryGroup w := by
    simp [ws, pauliXApp]
  rw [happs_eq]
  let x' : Qubits (L + 1 + L) :=
    fun w => if hw : w.1 < L then (if pat ⟨w.1, hw⟩ then x w else !x w) else x w
  have hx'_mem : ∀ w : Fin (L + 1 + L), w ∈ ws ↔ (∃ hw : w.1 < L, pat ⟨w.1, hw⟩ = false) := by
    intro w
    simp only [ws, idxs, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i.isLt, ?_⟩
      cases hpi : pat i <;> simp_all
    · rintro ⟨hw, hpat⟩
      exact ⟨⟨w.1, hw⟩, by simp [hpat], Fin.ext rfl⟩
  rw [Finset.sum_eq_single x']
  · rw [circuit_prod_gate1_of_nodup ws hws_nodup _ _ x' x]
    have hoff : ∀ q : Fin (L + 1 + L), q ∉ ws → x' q = x q := by
      intro q hq
      dsimp only [x']
      split_ifs with hql hpat
      · rfl
      · exfalso; exact hq ((hx'_mem q).mpr ⟨hql, by cases hpat_q : pat ⟨q.1, hql⟩ <;> simp_all⟩)
      · rfl
    rw [if_pos hoff]
    have hprod : (∏ w ∈ ws.toFinset, pauliX (x' w) (x w)) = 1 := by
      refine Finset.prod_eq_one fun w hw => ?_
      have hw_ws : w ∈ ws := List.mem_toFinset.mp hw
      rcases (hx'_mem w).mp hw_ws with ⟨hw_lt, hpat⟩
      have hxw : x' w = !x w := by simp [x', hw_lt, hpat]
      rw [hxw]
      cases x w <;> simp [pauliX]
    rw [hprod, one_smul]
  · intro y _ hy
    rw [circuit_prod_gate1_of_nodup ws hws_nodup _ _ y x]
    by_cases hoff : ∀ q : Fin (L + 1 + L), q ∉ ws → y q = x q
    · rw [if_pos hoff]
      by_cases hprod0 : ∃ w ∈ ws.toFinset, pauliX (y w) (x w) = 0
      · rcases hprod0 with ⟨w, hw, h0⟩
        rw [Finset.prod_eq_zero hw h0, zero_smul]
      · push Not at hprod0
        exfalso; apply hy
        funext w
        by_cases hw : w ∈ ws
        · have hne0 := hprod0 w (List.mem_toFinset.mpr hw)
          rcases (hx'_mem w).mp hw with ⟨hw_lt, hpat⟩
          have hyw : y w = !x w := by
            revert hne0; cases y w <;> cases x w <;> simp [pauliX]
          simp [x', hw_lt, hpat, hyw]
        · rw [hoff w hw]
          dsimp only [x']
          split_ifs with hw_lt hpat
          · rfl
          · exfalso; exact hw ((hx'_mem w).mpr ⟨hw_lt, by cases hpat_w : pat ⟨w.1, hw_lt⟩ <;> simp_all⟩)
          · rfl
    · rw [if_neg hoff, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def multiEqCtrl1 (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) : LayeredCircuit (L + 1 + L) :=
  if hL : 1 ≤ L then
    let flip := flipPatLayer L pat
    let tree := andTree L 0 L hL (by omega)
    let out := treeOut L 0 L hL (by omega)
    let tgt : Fin (L + 1 + L) := ⟨L, by omega⟩
    have hne : out ≠ tgt := by
      intro h
      have hv := congrArg Fin.val h
      dsimp only [out, treeOut, tgt] at hv
      split_ifs at hv <;> simp at hv <;> omega
    let ctrl := ctrlGate1 U hU out tgt hne
    flip.1.seq (tree.1.seq (ctrl.seq (tree.1.adj.seq flip.1)))
  else
    gate1 U hU ⟨L, by omega⟩

lemma multiEqCtrl1_size (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    (multiEqCtrl1 L pat U hU).size ≤ 12 * (L + 1) := by
  unfold multiEqCtrl1
  split_ifs with hL
  · simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, ctrlGate1_size]
    have h1 := (flipPatLayer L pat).2.2.1
    have h2 := andTree_size L 0 L hL (by omega)
    omega
  · simp; omega

lemma multiEqCtrl1_depth (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    (multiEqCtrl1 L pat U hU).depth ≤ 10 * Nat.clog 2 (L + 1) + 3 := by
  unfold multiEqCtrl1
  split_ifs with hL
  · simp only [LayeredCircuit.seq_depth, LayeredCircuit.adj_depth, ctrlGate1_depth]
    have h1 := (flipPatLayer L pat).2.2.2
    have h2 := andTree_depth L 0 L hL (by omega)
    have hclog : Nat.clog 2 L ≤ Nat.clog 2 (L + 1) := Nat.clog_mono_right 2 (by omega)
    omega
  · simp

theorem multiEqCtrl1_implements (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    (multiEqCtrl1 L pat U hU).ImplementsOnClean (eqCtrlMat L pat U) := by
  intro y z hz
  by_cases hL : 1 ≤ L
  · simp only [multiEqCtrl1, dif_pos hL]
    let flip := flipPatLayer L pat
    let tree := andTree L 0 L hL (by omega)
    let out := treeOut L 0 L hL (by omega)
    let tgt : Fin (L + 1 + L) := ⟨L, by omega⟩
    have hne : out ≠ tgt := by
      intro h
      have hv := congrArg Fin.val h
      dsimp only [out, treeOut, tgt] at hv
      split_ifs at hv <;> simp at hv <;> omega
    let ctrl := ctrlGate1 U hU out tgt hne
    let z1 : Qubits (L + 1 + L) :=
      fun w => if hw : w.1 < L then (if pat ⟨w.1, hw⟩ then z w else !z w) else z w
    have hflip_z : act flip.1.unitary (ket z) = ket z1 := act_flipPatLayer_ket L pat z
    have hclean_z1 : ∀ w ∈ treeSupport L 0 L, L + 1 ≤ w.1 → z1 w = false := by
      intro w _ hw_ge
      have hnot_lt : ¬ w.1 < L := by omega
      dsimp only [z1]
      rw [dif_neg hnot_lt]
      have hw_lt := w.isLt
      have hj : ∃ j : Fin L, w = ⟨L + 1 + j.1, by omega⟩ :=
        ⟨⟨w.1 - (L + 1), by omega⟩, Fin.ext (by simp; omega)⟩
      rcases hj with ⟨j, hw_eq⟩
      rw [hw_eq]
      exact hz j
    rcases andTree_ket L 0 L hL (by omega) z1 hclean_z1 with
      ⟨z', htree_fwd, hout_tree, _, hres_tree⟩
    have htgt_not_tree : tgt ∉ treeSupport L 0 L := by
      rw [mem_treeSupport_iff]; simp [tgt]
    have hz'_tgt : z' tgt = z tgt := by
      rw [hout_tree tgt htgt_not_tree]
      dsimp only [z1, tgt]
      rw [dif_neg (by omega)]
    have hz'_out : z' out = decide (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i) := by
      rw [hres_tree]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro h i
        have hi := h i (Nat.zero_le _) (by have := i.isLt; omega)
        dsimp only [z1] at hi
        rw [dif_pos i.isLt] at hi
        cases hzi : z ⟨i.1, by omega⟩ <;> cases hpi : pat i <;>
          simp [hzi, hpi] at hi ⊢
      · intro h i _ _
        dsimp only [z1]
        rw [dif_pos i.isLt]
        have hi := h i
        cases hzi : z ⟨i.1, by omega⟩ <;> cases hpi : pat i <;>
          simp [hzi, hpi] at hi ⊢
    have htree_adj : ∀ b : Bool,
        act tree.1.adj.unitary (ket (Function.update z' tgt b)) =
          ket (Function.update z1 tgt b) := by
      intro b
      have hfwd_b := act_ket_update_of_not_mem tree.1 tree.2 tgt htgt_not_tree htree_fwd b
      rw [← hfwd_b, ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp tree.1.unitary_mem_unitaryGroup, act_one]
    have hflip_inv : ∀ b : Bool,
        act flip.1.unitary (ket (Function.update z1 tgt b)) =
          ket (Function.update z tgt b) := by
      intro b
      rw [act_flipPatLayer_ket]
      congr 1
      funext w
      by_cases hw : w.1 < L
      · have hw_ne : w ≠ tgt := by intro h; have := congrArg Fin.val h; simp [tgt] at this; omega
        rw [dif_pos hw, Function.update_of_ne hw_ne, Function.update_of_ne hw_ne]
        dsimp only [z1]
        rw [dif_pos hw]
        cases pat ⟨w.1, hw⟩ <;> simp
      · rw [dif_neg hw]
        by_cases hwt : w = tgt
        · subst hwt; simp
        · rw [Function.update_of_ne hwt, Function.update_of_ne hwt]
          dsimp only [z1]; rw [dif_neg hw]
    have htot : act (flip.1.seq (tree.1.seq (ctrl.seq (tree.1.adj.seq flip.1)))).unitary (ket z) =
        ∑ b : Bool,
          (if (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i) then U b (z tgt)
           else if b = z tgt then 1 else 0) •
            ket (Function.update z tgt b) := by
      simp only [LayeredCircuit.seq_unitary, act_mul, hflip_z]
      rw [htree_fwd]
      dsimp only [ctrl]
      rw [act_ctrlGate1_ket, act_sum, act_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [act_smul, htree_adj, hflip_inv, hz'_tgt, hz'_out]
      by_cases hpat : ∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i
      · simp [hpat]
      · simp [hpat]
    have hentry : (flip.1.seq (tree.1.seq (ctrl.seq (tree.1.adj.seq flip.1)))).unitary y z =
        inner ℂ (ket y)
          (act (flip.1.seq (tree.1.seq (ctrl.seq (tree.1.adj.seq flip.1)))).unitary (ket z)) := by
      rw [act_ket_eq, inner_sum]
      simp [inner_smul_right, ket, EuclideanSpace.inner_single_left]
    rw [hentry, htot, inner_sum]
    simp only [inner_smul_right, ket, EuclideanSpace.inner_single_left, PiLp.single_apply,
      map_one, mul_ite, mul_one, mul_zero]
    by_cases hy : ∀ j : Fin L, y (Fin.natAdd (L + 1) j) = false
    · rw [if_pos hy]
      have hoff : ∀ b : Bool, Function.update z tgt b = y ↔
          ((∀ i : Fin L, y ⟨i.1, by omega⟩ = z ⟨i.1, by omega⟩) ∧ y tgt = b) := by
        intro b
        constructor
        · intro heq
          refine ⟨fun i => ?_, by rw [← heq, Function.update_self]⟩
          rw [← heq, Function.update_of_ne]
          intro h; have := congrArg Fin.val h; dsimp [tgt] at this; omega
        · rintro ⟨haddr, rfl⟩
          funext w
          by_cases hwt : w = tgt
          · subst hwt; simp
          · rw [Function.update_of_ne hwt]
            by_cases hw_lt : w.1 < L
            · exact (haddr ⟨w.1, hw_lt⟩).symm
            · have hw_isLt := w.isLt
              have hw_ne_L : w.1 ≠ L := fun h => hwt (Fin.ext h)
              have hj : ∃ j : Fin L, w = Fin.natAdd (L + 1) j :=
                ⟨⟨w.1 - (L + 1), by omega⟩, Fin.ext (by simp; omega)⟩
              rcases hj with ⟨j, rfl⟩
              rw [hz j, hy j]
      by_cases haddr : ∀ i : Fin L, y ⟨i.1, by omega⟩ = z ⟨i.1, by omega⟩
      · rw [Finset.sum_eq_single (y tgt)]
        · have heq : Function.update z tgt (y tgt) = y := (hoff (y tgt)).mpr ⟨haddr, rfl⟩
          rw [if_pos heq.symm]
          simp only [eqCtrlMat, Matrix.of_apply]
          have haddr_cast : ∀ i : Fin L, y (Fin.castAdd L ⟨i.1, by omega⟩) =
              z (Fin.castAdd L ⟨i.1, by omega⟩) := haddr
          rw [if_pos haddr_cast]
          rfl
        · intro b _ hb
          have hne_upd : Function.update z tgt b ≠ y := fun h => hb ((hoff b).mp h).2.symm
          rw [if_neg hne_upd.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have hzero : (∑ b : Bool,
            (if y = Function.update z tgt b then
              if (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i) then U b (z tgt)
              else if b = z tgt then 1 else 0
            else 0)) = 0 := by
          refine Finset.sum_eq_zero fun b _ => ?_
          have hne_upd : Function.update z tgt b ≠ y := fun h => haddr ((hoff b).mp h).1
          rw [if_neg hne_upd.symm]
        rw [hzero]
        simp only [eqCtrlMat, Matrix.of_apply]
        have hnot : ¬ ∀ i : Fin L, y (Fin.castAdd L ⟨i.1, by omega⟩) =
            z (Fin.castAdd L ⟨i.1, by omega⟩) := haddr
        rw [if_neg hnot]
    · rw [if_neg hy]
      refine Finset.sum_eq_zero fun b _ => ?_
      have hne_upd : Function.update z tgt b ≠ y := by
        intro h
        apply hy
        intro j
        have hj_lt := j.isLt
        have hjn : Fin.natAdd (L + 1) j ≠ tgt := by
          intro heq; have := congrArg Fin.val heq; simp [tgt] at this; omega
        rw [← h, Function.update_of_ne hjn]
        exact hz j
      rw [if_neg hne_upd.symm]
  · simp only [multiEqCtrl1, dif_neg hL]
    have hL0 : L = 0 := by omega
    subst hL0
    have hy0 : ∀ j : Fin 0, y (Fin.natAdd (0 + 1) j) = false := fun j => Fin.elim0 j
    rw [if_pos hy0]
    simp only [gate1, LayeredCircuit.single_unitary, embedOp_gate1App_entry, eqCtrlMat,
      Matrix.of_apply]
    have hoff : ∀ a : Fin 1, a ≠ ⟨0, by omega⟩ → y a = z a := by
      intro a ha; fin_cases a; exact absurd rfl ha
    rw [if_pos hoff, if_pos (fun i => Fin.elim0 i), if_pos (fun i => Fin.elim0 i)]
    rfl

/-! ### 14. Parallel Carry-Save Hamming Weight Counter (`hammingCounter`) -/

lemma act_ket_usesOnly_outside {m : ℕ} {lc : LayeredCircuit m} {S : Finset (Fin m)}
    (hS : lc.UsesOnly S) {z z' : Qubits m} (hact : act lc.unitary (ket z) = ket z')
    {w : Fin m} (hw : w ∉ S) : z' w = z w := by
  by_contra hne
  have hnot_wires : ∀ g ∈ lc.toCircuit, w ∉ Set.range g.wires := by
    intro g hg ⟨i, hi⟩
    rw [LayeredCircuit.toCircuit, List.mem_flatten] at hg
    rcases hg with ⟨L, hL, hgL⟩
    exact hw (hi ▸ hS L hL g hgL i)
  have hzero := circuit_preserves_wire lc.toCircuit w hnot_wires z' z hne
  have h1 : (act lc.unitary (ket z)) z' = 1 := by rw [hact]; simp [ket]
  have h2 : (act lc.unitary (ket z)) z' = lc.unitary z' z := by
    have hinner : (act lc.unitary (ket z)) z' = inner ℂ (ket z') (act lc.unitary (ket z)) := by
      simp [ket, EuclideanSpace.inner_single_left]
    rw [hinner, act_ket_eq, inner_sum]
    simp [inner_smul_right, ket, EuclideanSpace.inner_single_left]
  rw [h2, (show lc.unitary z' z = 0 from hzero)] at h1
  exact one_ne_zero h1.symm

private lemma foldr_disjoint_of_pairwise {m : ℕ} {S : Finset (Fin m)}
    {rest : List (LayeredCircuit m × Finset (Fin m))}
    (hhd : ∀ q ∈ rest, Disjoint S q.2) :
    Disjoint S (rest.foldr (fun p acc => p.2 ∪ acc) ∅) := by
  induction rest with
  | nil => simp
  | cons p rp ihr =>
    simp only [List.foldr_cons, Finset.disjoint_union_right]
    exact ⟨hhd p List.mem_cons_self, ihr fun q hq => hhd q (List.mem_cons_of_mem _ hq)⟩

private def parMergeAux {m : ℕ} :
    (xs : List (LayeredCircuit m × Finset (Fin m))) →
    (∀ p ∈ xs, p.1.UsesOnly p.2) →
    xs.Pairwise (fun p q => Disjoint p.2 q.2) →
    { lc : LayeredCircuit m //
      lc.UsesOnly (xs.foldr (fun p acc => p.2 ∪ acc) ∅) ∧
      lc.size = (xs.map (fun p => p.1.size)).sum ∧
      lc.depth ≤ xs.foldr (fun p acc => max p.1.depth acc) 0 }
  | [], _, _ => ⟨LayeredCircuit.id m, LayeredCircuit.id_usesOnly _, rfl, le_rfl⟩
  | (lc, S) :: rest, huses, hpw =>
    have huses_rest : ∀ p ∈ rest, p.1.UsesOnly p.2 := fun p hp =>
      huses p (List.mem_cons_of_mem _ hp)
    have hpw_rest : rest.Pairwise (fun p q => Disjoint p.2 q.2) :=
      (List.pairwise_cons.mp hpw).2
    let ih := parMergeAux rest huses_rest hpw_rest
    have hdisj : Disjoint S (rest.foldr (fun p acc => p.2 ∪ acc) ∅) :=
      foldr_disjoint_of_pairwise (List.pairwise_cons.mp hpw).1
    let merged := LayeredCircuit.parMerge lc ih.1 (huses _ List.mem_cons_self) ih.2.1 hdisj
    ⟨merged,
      LayeredCircuit.parMerge_usesOnly lc ih.1 (huses _ List.mem_cons_self) ih.2.1 hdisj,
      by simp [merged, LayeredCircuit.parMerge_size, ih.2.2.1],
      by
        simp only [merged, LayeredCircuit.parMerge_depth, List.foldr_cons]
        exact max_le_max_left _ ih.2.2.2⟩

private lemma foldr_max_le {m : ℕ} (xs : List (LayeredCircuit m × Finset (Fin m)))
    (B : ℕ) (hB : ∀ p ∈ xs, p.1.depth ≤ B) :
    xs.foldr (fun p acc => max p.1.depth acc) 0 ≤ B := by
  induction xs with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldr_cons]
    exact max_le (hB p List.mem_cons_self) (ih fun q hq => hB q (List.mem_cons_of_mem _ hq))

private lemma act_parMergeAux_ket {m : ℕ}
    (xs : List (LayeredCircuit m × Finset (Fin m)))
    (huses : ∀ p ∈ xs, p.1.UsesOnly p.2)
    (hpw : xs.Pairwise (fun p q => Disjoint p.2 q.2))
    (z z_next : Qubits m)
    (hact : ∀ p ∈ xs, ∃ x' : Qubits m,
      act p.1.unitary (ket z) = ket x' ∧ ∀ w ∈ p.2, x' w = z_next w) :
    act (parMergeAux xs huses hpw).1.unitary (ket z) =
      ket (fun w => if w ∈ xs.foldr (fun p acc => p.2 ∪ acc) ∅ then z_next w else z w) := by
  induction xs with
  | nil => simp [parMergeAux, LayeredCircuit.id_unitary, act_one]
  | cons p rest ih =>
    rcases p with ⟨lc, S⟩
    dsimp only [parMergeAux]
    rw [LayeredCircuit.parMerge_unitary, act_mul]
    have huses_lc : lc.UsesOnly S := huses (lc, S) List.mem_cons_self
    rcases hact (lc, S) List.mem_cons_self with ⟨x', hx'_act, hx'_in⟩
    rw [hx'_act]
    have hih := ih (fun q hq => huses q (List.mem_cons_of_mem _ hq))
      (List.pairwise_cons.mp hpw).2 (fun q hq => hact q (List.mem_cons_of_mem _ hq))
    have huses_rest : ∀ q ∈ rest, q.1.UsesOnly q.2 := fun q hq =>
      huses q (List.mem_cons_of_mem _ hq)
    let ihRes := parMergeAux rest huses_rest (List.pairwise_cons.mp hpw).2
    let S_rest : Finset (Fin m) := rest.foldr (fun q acc => q.2 ∪ acc) ∅
    have hdisj : Disjoint S S_rest :=
      foldr_disjoint_of_pairwise (List.pairwise_cons.mp hpw).1
    have hx'_out : ∀ w, w ∉ S → x' w = z w := fun w hw =>
      act_ket_usesOnly_outside huses_lc hx'_act hw
    have hagree : ∀ w ∈ S_rest, x' w = z w := fun w hw =>
      hx'_out w (Finset.disjoint_right.mp hdisj hw)
    have hstep := act_ket_agree_on_usesOnly ihRes.1 ihRes.2.1 hih hagree
    rw [hstep]
    congr 1
    funext w
    simp only [List.foldr_cons, Finset.mem_union]
    by_cases hwR : w ∈ S_rest
    · rw [if_pos hwR, if_pos hwR, if_pos (Or.inr hwR)]
    · by_cases hwS : w ∈ S
      · rw [if_neg hwR, hx'_in w hwS, if_pos (Or.inl hwS)]
      · rw [if_neg hwR, hx'_out w hwS, if_neg (not_or.mpr ⟨hwS, hwR⟩)]

noncomputable def halfAdder4 {m : ℕ} (a b s c : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (hac : a ≠ c) (hbs : b ≠ s) (hbc : b ≠ c) :
    LayeredCircuit m :=
  (cnotGate a s has).seq ((cnotGate b s hbs).seq (toffoliOn a b c hab hac hbc))

@[simp] lemma halfAdder4_size {m : ℕ} (a b s c : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (hac : a ≠ c) (hbs : b ≠ s) (hbc : b ≠ c) :
    (halfAdder4 a b s c hab has hac hbs hbc).size = 7 := by
  simp [halfAdder4]

@[simp] lemma halfAdder4_depth {m : ℕ} (a b s c : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (hac : a ≠ c) (hbs : b ≠ s) (hbc : b ≠ c) :
    (halfAdder4 a b s c hab has hac hbs hbc).depth = 7 := by
  simp [halfAdder4]

lemma halfAdder4_usesOnly {m : ℕ} (a b s c : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (hac : a ≠ c) (hbs : b ≠ s) (hbc : b ≠ c) :
    (halfAdder4 a b s c hab has hac hbs hbc).UsesOnly {a, b, s, c} := by
  refine LayeredCircuit.seq_usesOnly ?_ (LayeredCircuit.seq_usesOnly ?_ ?_)
  · exact (cnotGate_usesOnly a s has).mono (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> simp)
  · exact (cnotGate_usesOnly b s hbs).mono (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> simp)
  · exact (toffoliOn_usesOnly a b c hab hac hbc).mono
      (by intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> simp)

lemma act_halfAdder4_ket {m : ℕ} (a b s c : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (hac : a ≠ c) (hbs : b ≠ s) (hbc : b ≠ c) (hsc : s ≠ c)
    (x : Qubits m) (hxs : x s = false) (hxc : x c = false) :
    act (halfAdder4 a b s c hab has hac hbs hbc).unitary (ket x) =
      ket (fun w => if w = s then xor (x a) (x b) else if w = c then x a && x b else x w) := by
  simp only [halfAdder4, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  congr 1
  funext w
  by_cases hws : w = s
  · subst hws
    simp only [Function.update_self, Function.update_of_ne hsc, Function.update_of_ne has,
      Function.update_of_ne hbs, hxs, Bool.false_xor, ite_true]
  · by_cases hwc : w = c
    · subst hwc
      simp only [Function.update_self, Function.update_of_ne hsc.symm, Function.update_of_ne has,
        Function.update_of_ne hbs, hxc, Bool.false_xor, if_neg hws, ite_true]
    · simp only [Function.update_of_ne hwc, Function.update_of_ne hws, if_neg hws, if_neg hwc]

lemma bool_halfAdder_arith (va vb : Bool) :
    (if xor va vb then 1 else 0) + 2 * (if va && vb then 1 else 0) =
      (if va then 1 else 0) + (if vb then 1 else 0) := by
  cases va <;> cases vb <;> decide

noncomputable def fullAdder5 {m : ℕ} (a b c s cout : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (haco : a ≠ cout)
    (hbs : b ≠ s) (hbco : b ≠ cout)
    (hcs : c ≠ s) (hcco : c ≠ cout) (hsco : s ≠ cout) : LayeredCircuit m :=
  (cnotGate a s has).seq
    ((cnotGate b s hbs).seq
      ((toffoliOn a b cout hab haco hbco).seq
        ((toffoliOn s c cout hcs.symm hsco hcco).seq
          (cnotGate c s hcs))))

@[simp] lemma fullAdder5_size {m : ℕ} (a b c s cout : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (haco : a ≠ cout)
    (hbs : b ≠ s) (hbco : b ≠ cout)
    (hcs : c ≠ s) (hcco : c ≠ cout) (hsco : s ≠ cout) :
    (fullAdder5 a b c s cout hab has haco hbs hbco hcs hcco hsco).size = 13 := by
  simp [fullAdder5]

@[simp] lemma fullAdder5_depth {m : ℕ} (a b c s cout : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (haco : a ≠ cout)
    (hbs : b ≠ s) (hbco : b ≠ cout)
    (hcs : c ≠ s) (hcco : c ≠ cout) (hsco : s ≠ cout) :
    (fullAdder5 a b c s cout hab has haco hbs hbco hcs hcco hsco).depth = 13 := by
  simp [fullAdder5]

lemma fullAdder5_usesOnly {m : ℕ} (a b c s cout : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (haco : a ≠ cout)
    (hbs : b ≠ s) (hbco : b ≠ cout)
    (hcs : c ≠ s) (hcco : c ≠ cout) (hsco : s ≠ cout) :
    (fullAdder5 a b c s cout hab has haco hbs hbco hcs hcco hsco).UsesOnly
      {a, b, c, s, cout} := by
  refine LayeredCircuit.seq_usesOnly ?_
    (LayeredCircuit.seq_usesOnly ?_
      (LayeredCircuit.seq_usesOnly ?_
        (LayeredCircuit.seq_usesOnly ?_ ?_)))
  · exact (cnotGate_usesOnly a s has).mono (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> simp)
  · exact (cnotGate_usesOnly b s hbs).mono (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> simp)
  · exact (toffoliOn_usesOnly a b cout hab haco hbco).mono
      (by intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> simp)
  · exact (toffoliOn_usesOnly s c cout hcs.symm hsco hcco).mono
      (by intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> simp)
  · exact (cnotGate_usesOnly c s hcs).mono (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> simp)

lemma act_fullAdder5_ket {m : ℕ} (a b c s cout : Fin m)
    (hab : a ≠ b) (has : a ≠ s) (haco : a ≠ cout)
    (hbs : b ≠ s) (hbco : b ≠ cout)
    (hcs : c ≠ s) (hcco : c ≠ cout) (hsco : s ≠ cout)
    (x : Qubits m) (hxs : x s = false) (hxco : x cout = false) :
    act (fullAdder5 a b c s cout hab has haco hbs hbco hcs hcco hsco).unitary (ket x) =
      ket (fun w =>
        if w = s then xor (xor (x a) (x b)) (x c)
        else if w = cout then xor (x a && x b) (xor (x a) (x b) && x c)
        else x w) := by
  simp only [fullAdder5, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  congr 1
  funext w
  by_cases hws : w = s
  · subst hws
    simp only [Function.update_self, Function.update_of_ne hsco, Function.update_of_ne hcs,
      Function.update_of_ne hcco, Function.update_of_ne has, Function.update_of_ne hbs,
      hxs, Bool.false_xor, ite_true]
  · by_cases hwco : w = cout
    · subst hwco
      simp only [Function.update_self, Function.update_of_ne hsco.symm, Function.update_of_ne hsco,
        Function.update_of_ne hcco, Function.update_of_ne hcs, Function.update_of_ne has,
        Function.update_of_ne hbs, hxs, hxco, Bool.false_xor, if_neg hws, ite_true]
    · simp only [Function.update_of_ne hws, Function.update_of_ne hwco, if_neg hws, if_neg hwco]

lemma bool_fullAdder_arith (va vb vc : Bool) :
    (if xor (xor va vb) vc then 1 else 0) +
      2 * (if xor (va && vb) (xor va vb && vc) then 1 else 0) =
      (if va then 1 else 0) + (if vb then 1 else 0) + (if vc then 1 else 0) := by
  cases va <;> cases vb <;> cases vc <;> decide

private def takeTriples {α : Type*} : List α → List (α × α × α) × List α
  | a :: b :: c :: rest =>
    let res := takeTriples rest
    ((a, b, c) :: res.1, res.2)
  | rem => ([], rem)

private lemma takeTriples_ind {α : Type*} (P : List α → Prop)
    (h0 : P []) (h1 : ∀ a, P [a]) (h2 : ∀ a b, P [a, b])
    (h3 : ∀ a b c rest, P rest → P (a :: b :: c :: rest)) (L : List α) : P L := by
  match L with
  | [] => exact h0
  | [a] => exact h1 a
  | [a, b] => exact h2 a b
  | a :: b :: c :: rest => exact h3 a b c rest (takeTriples_ind P h0 h1 h2 h3 rest)
termination_by L.length

private lemma takeTriples_fst_length {α : Type*} (L : List α) :
    (takeTriples L).1.length = L.length / 3 := by
  refine takeTriples_ind (fun L => (takeTriples L).1.length = L.length / 3)
    (by simp [takeTriples]) (fun a => by simp [takeTriples])
    (fun a b => by simp [takeTriples]) (fun a b c rest ih => ?_) L
  change ((a, b, c) :: (takeTriples rest).1).length = (rest.length + 3) / 3
  simp only [List.length_cons, ih]
  omega

private lemma takeTriples_snd_length {α : Type*} (L : List α) :
    (takeTriples L).2.length = L.length % 3 := by
  refine takeTriples_ind (fun L => (takeTriples L).2.length = L.length % 3)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih => ?_) L
  change (takeTriples rest).2.length = (rest.length + 3) % 3
  simp only [ih]
  omega

private lemma takeTriples_mem_snd {α : Type*} {L : List α} {x : α} (hx : x ∈ (takeTriples L).2) :
    x ∈ L := by
  revert hx
  refine takeTriples_ind (fun L => x ∈ (takeTriples L).2 → x ∈ L)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih h => by
      change x ∈ (takeTriples rest).2 at h
      simp [ih h]) L

private lemma takeTriples_mem_fst {α : Type*} {L : List α} {t : α × α × α}
    (ht : t ∈ (takeTriples L).1) : t.1 ∈ L ∧ t.2.1 ∈ L ∧ t.2.2 ∈ L := by
  revert ht
  refine takeTriples_ind (fun L => t ∈ (takeTriples L).1 → t.1 ∈ L ∧ t.2.1 ∈ L ∧ t.2.2 ∈ L)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih h => by
      change t ∈ (a, b, c) :: (takeTriples rest).1 at h
      rw [List.mem_cons] at h
      rcases h with rfl | hrest
      · simp
      · have h' := ih hrest
        simp [h'.1, h'.2.1, h'.2.2]) L

private lemma takeTriples_nodup_snd {α : Type*} {L : List α} (hL : L.Nodup) :
    (takeTriples L).2.Nodup := by
  revert hL
  refine takeTriples_ind (fun L => L.Nodup → (takeTriples L).2.Nodup)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih h => by
      change (takeTriples rest).2.Nodup
      rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at h
      exact ih h.2.2.2) L

private lemma takeTriples_triples_disjoint {α : Type*} [DecidableEq α] {L : List α}
    (hL : L.Nodup) :
    (takeTriples L).1.Pairwise (fun t1 t2 =>
      Disjoint ({t1.1, t1.2.1, t1.2.2} : Finset α) ({t2.1, t2.2.1, t2.2.2} : Finset α)) ∧
    ∀ t ∈ (takeTriples L).1, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
  revert hL
  refine takeTriples_ind (fun L => L.Nodup →
      ((takeTriples L).1.Pairwise fun t1 t2 =>
        Disjoint ({t1.1, t1.2.1, t1.2.2} : Finset α) ({t2.1, t2.2.1, t2.2.2} : Finset α)) ∧
      ∀ t ∈ (takeTriples L).1, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih h => by
      have ha : a ≠ b ∧ a ≠ c ∧ a ∉ rest := by
        rw [List.nodup_cons] at h; simp at h; exact ⟨h.1.1, h.1.2.1, h.1.2.2⟩
      have hb : b ≠ c ∧ b ∉ rest := by
        rw [List.nodup_cons, List.nodup_cons] at h; simp at h; exact ⟨h.2.1.1, h.2.1.2⟩
      have hc : c ∉ rest := by
        rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at h; exact h.2.2.1
      have hrest_nd : rest.Nodup := by
        rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at h; exact h.2.2.2
      rcases ih hrest_nd with ⟨hpw_rest, hdistinct_rest⟩
      change ((a, b, c) :: (takeTriples rest).1).Pairwise _ ∧
        ∀ t ∈ (a, b, c) :: (takeTriples rest).1, _
      refine ⟨List.pairwise_cons.mpr ⟨?_, hpw_rest⟩, ?_⟩
      · intro t ht
        have hm := takeTriples_mem_fst ht
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
        have hw_rest : w ∈ rest := by rcases hw2 with rfl | rfl | rfl <;> tauto
        rcases hw1 with rfl | rfl | rfl
        · exact ha.2.2 hw_rest
        · exact hb.2 hw_rest
        · exact hc hw_rest
      · intro t ht
        rw [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ⟨ha.1, ha.2.1, hb.1⟩
        · exact hdistinct_rest t ht) L

private lemma takeTriples_countP {α : Type*} (L : List α) (p : α → Bool) :
    L.countP p =
      ((takeTriples L).1.map (fun t =>
        (if p t.1 then 1 else 0) + (if p t.2.1 then 1 else 0) +
          (if p t.2.2 then 1 else 0))).sum +
      (takeTriples L).2.countP p := by
  refine takeTriples_ind (fun L => L.countP p =
      ((takeTriples L).1.map (fun t =>
        (if p t.1 then 1 else 0) + (if p t.2.1 then 1 else 0) +
          (if p t.2.2 then 1 else 0))).sum +
      (takeTriples L).2.countP p)
    (by simp [takeTriples]) (fun a => by simp [takeTriples]) (fun a b => by simp [takeTriples])
    (fun a b c rest ih => by
      change (a :: b :: c :: rest).countP p =
        ((if p a then 1 else 0) + (if p b then 1 else 0) + (if p c then 1 else 0) +
          ((takeTriples rest).1.map _).sum) + (takeTriples rest).2.countP p
      simp only [List.countP_cons, ih]
      split_ifs <;> omega) L

private def numberItems {α : Type*} (start : ℕ) : List α → List (α × ℕ)
  | [] => []
  | x :: xs => (x, start) :: numberItems (start + 1) xs

private lemma numberItems_map_fst {α : Type*} (start : ℕ) (xs : List α) :
    (numberItems start xs).map Prod.fst = xs := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp [numberItems, ih]

private lemma mem_numberItems_bounds {α : Type*} {start : ℕ} {xs : List α} {p : α × ℕ}
    (hp : p ∈ numberItems start xs) :
    start ≤ p.2 ∧ p.2 < start + xs.length ∧ p.1 ∈ xs := by
  induction xs generalizing start with
  | nil => cases hp
  | cons x xs ih =>
    simp only [numberItems, List.mem_cons] at hp
    rcases hp with rfl | hrest
    · simp
    · rcases ih hrest with ⟨h1, h2, h3⟩
      simp only [List.length_cons, List.mem_cons]
      exact ⟨by omega, by omega, Or.inr h3⟩

private lemma numberItems_pairwise_ne {α : Type*} (start : ℕ) (xs : List α) :
    (numberItems start xs).Pairwise (fun p q => p.2 ≠ q.2) := by
  induction xs generalizing start with
  | nil => simp [numberItems]
  | cons x xs ih =>
    simp only [numberItems, List.pairwise_cons]
    refine ⟨fun q hq heq => ?_, ih (start + 1)⟩
    have hlt := (mem_numberItems_bounds hq).1
    omega

private lemma numberItems_length {α : Type*} (start : ℕ) (xs : List α) :
    (numberItems start xs).length = xs.length := by
  induction xs generalizing start with
  | nil => simp [numberItems]
  | cons x xs ih => simp [numberItems, ih]

private lemma numberItems_filter_length {α : Type*} (start : ℕ) (xs : List α) (P : α → Bool) :
    ((numberItems start xs).filter fun p => P p.1).length = (xs.filter P).length := by
  induction xs generalizing start with
  | nil => simp [numberItems]
  | cons x xs ih =>
    simp only [numberItems, List.filter_cons]
    cases P x <;> simp [ih]

private lemma nodup_map_of_pairwise {α β : Type*} {xs : List α} {f : α → β}
    (hpw : xs.Pairwise (fun a b => f a ≠ f b)) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, ih hpw.2⟩
    rw [List.mem_map] at h
    rcases h with ⟨b, hb, heq⟩
    exact hpw.1 b hb heq.symm

private lemma pairwise_eq_of_snd {α β : Type*} {xs : List (α × β)}
    (hpw : xs.Pairwise (fun p q => p.2 ≠ q.2))
    {p q : α × β} (hp : p ∈ xs) (hq : q ∈ xs) (hsnd : p.2 = q.2) : p = q := by
  induction xs with
  | nil => cases hp
  | cons a rest ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.mem_cons] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · exact absurd hsnd (hpw.1 q hq)
    · exact absurd hsnd.symm (hpw.1 p hp)
    · exact ih hpw.2 hp hq

private lemma sum_map_finRange {k : ℕ} (f : Fin k → ℕ) :
    ((List.finRange k).map f).sum = ∑ b : Fin k, f b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, Fin.sum_univ_succ]
    exact congrArg (f 0 + ·) (ih (f ∘ Fin.succ))

private lemma nodup_flatMap_of {α β : Type*} {xs : List α} {f : α → List β}
    (hxs : xs.Nodup) (hnd : ∀ a ∈ xs, (f a).Nodup)
    (hdisj : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → ∀ w, w ∈ f a → w ∉ f b) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    rw [List.nodup_cons] at hxs
    simp only [List.flatMap_cons, List.nodup_append]
    refine ⟨hnd a List.mem_cons_self, ih hxs.2 (fun b hb => hnd b (List.mem_cons_of_mem _ hb))
      (fun b hb c hc hne w hwb => hdisj b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc) hne w hwb), ?_⟩
    intro w hwa w' hwr heq
    subst heq
    rw [List.mem_flatMap] at hwr
    rcases hwr with ⟨b, hb, hwb⟩
    have hab : a ≠ b := fun h => hxs.1 (h ▸ hb)
    exact hdisj a List.mem_cons_self b (List.mem_cons_of_mem _ hb) hab w hwa hwb

private lemma countP_flatMap {α β : Type*} (xs : List α) (f : α → List β) (p : β → Bool) :
    (xs.flatMap f).countP p = (xs.map fun a => (f a).countP p).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih => simp [List.flatMap_cons, List.countP_append, ih]

abbrev hcEll (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

abbrev hammingAnc (n : ℕ) : ℕ := 2 * n + 2 * hcEll n + 1

abbrev hcWires (n : ℕ) : ℕ := (n + hcEll n) + hammingAnc n

lemma hcEll_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ hcEll n := by
  by_contra h
  have h0 : hcEll n = 0 := by omega
  have hle : n + 1 ≤ 2 ^ 0 := clog2_le_iff_le_pow.mp (le_of_eq h0)
  omega

lemma hcEll_le_self (n : ℕ) : hcEll n ≤ n := by
  rw [hcEll, clog2_le_iff_le_pow]
  induction n with
  | zero => decide
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · decide
    · rw [pow_succ']; omega

lemma lt_two_pow_hcEll (n : ℕ) : n < 2 ^ hcEll n := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (n + 1)
  change n + 1 ≤ 2 ^ hcEll n at h
  omega

def hcQWire (n : ℕ) (i : Fin n) : Fin (hcWires n) :=
  ⟨i.1, by dsimp only [hcWires, hammingAnc]; have := i.isLt; omega⟩

def hcOutWire (n : ℕ) (b : Fin (hcEll n)) : Fin (hcWires n) :=
  ⟨n + b.1, by dsimp only [hcWires, hammingAnc]; have := b.isLt; omega⟩

def hcPoolWire (n : ℕ) (k : ℕ) (hk : k < 2 * n) : Fin (hcWires n) :=
  ⟨n + hcEll n + k, by dsimp only [hcWires, hammingAnc]; omega⟩

def hcSumWire (n : ℕ) (b : Fin (hcEll n)) : Fin (hcWires n) :=
  ⟨n + hcEll n + 2 * n + b.1, by dsimp only [hcWires, hammingAnc]; have := b.isLt; omega⟩

def hcCarryWire (n : ℕ) (b : ℕ) (hb : b ≤ hcEll n) : Fin (hcWires n) :=
  ⟨n + hcEll n + 2 * n + hcEll n + b, by dsimp only [hcWires, hammingAnc]; omega⟩

private def fwdSupport (n : ℕ) : Finset (Fin (hcWires n)) :=
  Finset.univ.filter fun w => w.1 < n ∨ n + hcEll n ≤ w.1

private lemma mem_fwdSupport_iff {n : ℕ} {w : Fin (hcWires n)} :
    w ∈ fwdSupport n ↔ w.1 < n ∨ n + hcEll n ≤ w.1 := by
  simp [fwdSupport]

private def csRawSum (n : ℕ) (idx : ℕ) : Fin (hcWires n) :=
  ⟨(n + hcEll n + 2 * idx) % hcWires n,
    Nat.mod_lt _ (by dsimp only [hcWires, hammingAnc]; omega)⟩

private def csRawCarry (n : ℕ) (idx : ℕ) : Fin (hcWires n) :=
  ⟨(n + hcEll n + 2 * idx + 1) % hcWires n,
    Nat.mod_lt _ (by dsimp only [hcWires, hammingAnc]; omega)⟩

private lemma csRawSum_val {n : ℕ} {idx : ℕ} (hidx : idx < n) :
    (csRawSum n idx).1 = n + hcEll n + 2 * idx := by
  dsimp [csRawSum]
  exact Nat.mod_eq_of_lt (by dsimp only [hcWires, hammingAnc]; omega)

private lemma csRawCarry_val {n : ℕ} {idx : ℕ} (hidx : idx < n) :
    (csRawCarry n idx).1 = n + hcEll n + 2 * idx + 1 := by
  dsimp [csRawCarry]
  exact Nat.mod_eq_of_lt (by dsimp only [hcWires, hammingAnc]; omega)

private structure CSState (n : ℕ) where
  cols : Fin (hcEll n) → List (Fin (hcWires n))
  nextPair : ℕ

private def csInit (n : ℕ) : CSState n where
  cols b := if b.1 = 0 then (List.finRange n).map (hcQWire n) else []
  nextPair := 0

private def csAllTriples (n : ℕ) (st : CSState n) :
    List (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) :=
  (List.finRange (hcEll n)).flatMap fun b =>
    (takeTriples (st.cols b)).1.map fun t => (b, t)

private lemma csAllTriples_length (n : ℕ) (st : CSState n) :
    (csAllTriples n st).length = ∑ b : Fin (hcEll n), (st.cols b).length / 3 := by
  simp only [csAllTriples, List.length_flatMap, List.length_map, takeTriples_fst_length]
  exact sum_map_finRange (fun b => (st.cols b).length / 3)

private lemma csAllTriples_filter_fst_length (n : ℕ) (st : CSState n) (b : Fin (hcEll n)) :
    ((csAllTriples n st).filter fun p => decide (p.1 = b)).length = (st.cols b).length / 3 := by
  rw [← takeTriples_fst_length (st.cols b)]
  dsimp only [csAllTriples]
  have hf : ∀ bs : List (Fin (hcEll n)), bs.Nodup →
      ((bs.flatMap fun b' => (takeTriples (st.cols b')).1.map fun t => (b', t)).filter
        fun p => decide (p.1 = b)).length =
      if b ∈ bs then (takeTriples (st.cols b)).1.length else 0 := by
    intro bs hbs
    induction bs with
    | nil => simp
    | cons a rest ih =>
      rw [List.nodup_cons] at hbs
      simp only [List.flatMap_cons, List.filter_append, List.length_append, ih hbs.2, List.mem_cons]
      have hcur : (((takeTriples (st.cols a)).1.map fun t => (a, t)).filter
          fun p => decide (p.1 = b)).length =
          if a = b then (takeTriples (st.cols a)).1.length else 0 := by
        by_cases hab : a = b
        · subst hab
          have hself : ((takeTriples (st.cols a)).1.map fun t => (a, t)).filter
              (fun p => decide (p.1 = a)) = (takeTriples (st.cols a)).1.map fun t => (a, t) := by
            rw [List.filter_eq_self]
            intro p hp
            simp only [List.mem_map] at hp
            rcases hp with ⟨t, _, rfl⟩
            simp
          rw [hself, List.length_map, if_pos rfl]
        · have hnil : ((takeTriples (st.cols a)).1.map fun t => (a, t)).filter
              (fun p => decide (p.1 = b)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro p hp
            simp only [List.mem_map] at hp
            rcases hp with ⟨t, _, rfl⟩
            simp [hab]
          rw [hnil, List.length_nil, if_neg hab]
      rw [hcur]
      by_cases hab : a = b
      · subst hab; simp [hbs.1]
      · simp [hab, ne_comm.mp hab]
  rw [hf (List.finRange (hcEll n)) (List.nodup_finRange _)]
  simp

private lemma csAllTriples_filter_pred_length (n : ℕ) (st : CSState n) (b : Fin (hcEll n)) :
    ((csAllTriples n st).filter fun p => decide (p.1.1 + 1 = b.1)).length =
      if h : 0 < b.1 then (st.cols ⟨b.1 - 1, by have := b.isLt; omega⟩).length / 3 else 0 := by
  by_cases hb : 0 < b.1
  · rw [dif_pos hb]
    let prev : Fin (hcEll n) := ⟨b.1 - 1, by have := b.isLt; omega⟩
    have hpred : (fun p : Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n)) =>
        decide (p.1.1 + 1 = b.1)) =
        (fun p => decide (p.1 = prev)) := by
      funext p
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Fin.ext_iff, prev]
      omega
    rw [hpred, csAllTriples_filter_fst_length]
  · rw [dif_neg hb]
    have hnil : ((csAllTriples n st).filter fun p => decide (p.1.1 + 1 = b.1)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro p _ h
      simp only [decide_eq_true_eq] at h
      omega
    rw [hnil, List.length_nil]

private def csStep (n : ℕ) (st : CSState n) : CSState n :=
  let ann := numberItems st.nextPair (csAllTriples n st)
  { cols := fun b =>
      (takeTriples (st.cols b)).2 ++
      ((ann.filter fun p => decide (p.1.1 = b)).map fun p => csRawSum n p.2) ++
      ((ann.filter fun p => decide (p.1.1.1 + 1 = b.1)).map fun p => csRawCarry n p.2)
    nextPair := st.nextPair + (csAllTriples n st).length }

private def csStateAt (n : ℕ) : ℕ → CSState n
  | 0 => csInit n
  | r + 1 => csStep n (csStateAt n r)

private lemma csStep_col_length (n : ℕ) (st : CSState n) (b : Fin (hcEll n)) :
    ((csStep n st).cols b).length =
      (st.cols b).length % 3 + (st.cols b).length / 3 +
        if h : 0 < b.1 then (st.cols ⟨b.1 - 1, by have := b.isLt; omega⟩).length / 3 else 0 := by
  dsimp only [csStep]
  rw [List.length_append, List.length_append, List.length_map, List.length_map,
    takeTriples_snd_length,
    numberItems_filter_length st.nextPair (csAllTriples n st) (fun q => decide (q.1 = b)),
    numberItems_filter_length st.nextPair (csAllTriples n st) (fun q => decide (q.1.1 + 1 = b.1)),
    csAllTriples_filter_fst_length, csAllTriples_filter_pred_length]

private lemma cs_step_num_bound (x y M : ℕ) (hx : x ≤ M) (hy : y ≤ M) :
    3 * (x % 3 + x / 3 + y / 3) ≤ 2 * M + 3 := by
  omega

private lemma nat_mul_sup_le {ι : Type*} (s : Finset ι) (c : ℕ) (f : ι → ℕ) (B : ℕ) :
    c * s.sup f ≤ B ↔ ∀ x ∈ s, c * f x ≤ B := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  · constructor
    · intro h x hx
      exact le_trans (Nat.mul_le_mul_left c (Finset.le_sup hx)) h
    · intro h
      have hdiv : ∀ x ∈ s, f x ≤ B / c := fun x hx =>
        (Nat.le_div_iff_mul_le hc).mpr (by rw [mul_comm]; exact h x hx)
      exact (Nat.mul_le_mul_left c (Finset.sup_le hdiv)).trans (Nat.mul_div_le B c)

private def maxColLen (n : ℕ) (st : CSState n) : ℕ :=
  Finset.univ.sup fun b : Fin (hcEll n) => (st.cols b).length

private lemma maxColLen_step_le (n : ℕ) (st : CSState n) :
    3 * (maxColLen n (csStep n st) - 3) ≤ 2 * (maxColLen n st - 3) := by
  have h1 : 3 * maxColLen n (csStep n st) ≤ 2 * maxColLen n st + 3 := by
    dsimp only [maxColLen]
    rw [nat_mul_sup_le]
    intro b _
    rw [csStep_col_length]
    have hx : (st.cols b).length ≤ Finset.univ.sup (fun b => (st.cols b).length) :=
      Finset.le_sup (f := fun b : Fin (hcEll n) => (st.cols b).length) (Finset.mem_univ b)
    by_cases hb : 0 < b.1
    · rw [dif_pos hb]
      have hy : (st.cols ⟨b.1 - 1, by have := b.isLt; omega⟩).length ≤
          Finset.univ.sup (fun b => (st.cols b).length) :=
        Finset.le_sup (f := fun b : Fin (hcEll n) => (st.cols b).length) (Finset.mem_univ _)
      exact cs_step_num_bound _ _ _ hx hy
    · rw [dif_neg hb]
      omega
  omega

private lemma maxColLen_two_steps (n : ℕ) (st : CSState n) :
    2 * (maxColLen n (csStep n (csStep n st)) - 3) ≤ maxColLen n st - 3 := by
  have h1 := maxColLen_step_le n st
  have h2 := maxColLen_step_le n (csStep n st)
  omega

private lemma csStateAt_init_max (n : ℕ) :
    maxColLen n (csStateAt n 0) ≤ n := by
  dsimp only [maxColLen, csStateAt, csInit]
  refine Finset.sup_le fun b _ => ?_
  split_ifs <;> simp

private lemma csStateAt_two_mul_clog (n : ℕ) :
    ∀ b : Fin (hcEll n), ((csStateAt n (2 * hcEll n)).cols b).length ≤ 3 := by
  have hpow : ∀ k : ℕ, 2 ^ k * (maxColLen n (csStateAt n (2 * k)) - 3) ≤
      maxColLen n (csStateAt n 0) - 3 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, csStateAt, csStateAt, pow_succ']
      have h2 := maxColLen_two_steps n (csStateAt n (2 * k))
      calc 2 * 2 ^ k * (maxColLen n (csStep n (csStep n (csStateAt n (2 * k)))) - 3)
          = 2 ^ k * (2 * (maxColLen n (csStep n (csStep n (csStateAt n (2 * k)))) - 3)) := by
            ring
        _ ≤ 2 ^ k * (maxColLen n (csStateAt n (2 * k)) - 3) := Nat.mul_le_mul_left _ h2
        _ ≤ maxColLen n (csStateAt n 0) - 3 := ih
  have hk := hpow (hcEll n)
  have h0 := csStateAt_init_max n
  have hlt := lt_two_pow_hcEll n
  have hsub0 : maxColLen n (csStateAt n (2 * hcEll n)) - 3 = 0 := by
    by_contra hne
    have hge1 : 1 ≤ maxColLen n (csStateAt n (2 * hcEll n)) - 3 := by omega
    have hmul : 2 ^ hcEll n ≤ 2 ^ hcEll n * (maxColLen n (csStateAt n (2 * hcEll n)) - 3) :=
      Nat.le_mul_of_pos_right _ hge1
    omega
  intro b
  have hb : ((csStateAt n (2 * hcEll n)).cols b).length ≤
      maxColLen n (csStateAt n (2 * hcEll n)) := by
    dsimp only [maxColLen]
    exact Finset.le_sup (f := fun b : Fin (hcEll n) => ((csStateAt n (2 * hcEll n)).cols b).length)
      (Finset.mem_univ b)
  omega

private lemma csStateAt_three_mul_clog (n : ℕ) :
    ∀ b : Fin (hcEll n), ((csStateAt n (3 * hcEll n)).cols b).length ≤ 2 := by
  have hpref : ∀ t : ℕ,
      (∀ b : Fin (hcEll n), ((csStateAt n (2 * hcEll n + t)).cols b).length ≤ 3) ∧
      (∀ b : Fin (hcEll n), b.1 < t →
        ((csStateAt n (2 * hcEll n + t)).cols b).length ≤ 2) := by
    intro t
    induction t with
    | zero => exact ⟨csStateAt_two_mul_clog n, fun b hb => by omega⟩
    | succ t ih =>
      rcases ih with ⟨ih3, ih2⟩
      rw [← Nat.add_assoc]
      dsimp only [csStateAt]
      refine ⟨fun b => ?_, fun b hb => ?_⟩
      · rw [csStep_col_length]
        have hx := ih3 b
        by_cases h0 : 0 < b.1
        · rw [dif_pos h0]
          have hy := ih3 ⟨b.1 - 1, by have := b.isLt; omega⟩
          omega
        · rw [dif_neg h0]; omega
      · rw [csStep_col_length]
        have hx := ih3 b
        by_cases h0 : 0 < b.1
        · rw [dif_pos h0]
          have hy := ih2 ⟨b.1 - 1, by have := b.isLt; omega⟩ (by simp; omega)
          omega
        · rw [dif_neg h0]; omega
  intro b
  have h3 : 3 * hcEll n = 2 * hcEll n + hcEll n := by omega
  rw [h3]
  exact (hpref (hcEll n)).2 b b.isLt

private structure CSValid (n : ℕ) (st : CSState n) : Prop where
  pair_le : st.nextPair ≤ n
  nodup : ((List.finRange (hcEll n)).flatMap st.cols).Nodup
  wire_bound : ∀ b : Fin (hcEll n), ∀ w ∈ st.cols b,
    w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * st.nextPair)
  work_le : (∑ b : Fin (hcEll n), (st.cols b).length) + st.nextPair ≤ n

private lemma csValid_nextPair_add_triples {n : ℕ} {st : CSState n} (hv : CSValid n st) :
    st.nextPair + (csAllTriples n st).length ≤ n := by
  have hT_le_sum : 3 * (csAllTriples n st).length ≤ ∑ b : Fin (hcEll n), (st.cols b).length := by
    rw [csAllTriples_length, Finset.mul_sum]
    exact Finset.sum_le_sum fun _ _ => by omega
  have := hv.work_le
  omega

private lemma csValid_cols_nodup {n : ℕ} {st : CSState n} (hv : CSValid n st) :
    ∀ b : Fin (hcEll n), (st.cols b).Nodup ∧
      ∀ b' : Fin (hcEll n), b ≠ b' → ∀ w, w ∈ st.cols b → w ∉ st.cols b' := by
  have hfm := hv.nodup
  have hmem : ∀ b : Fin (hcEll n), (st.cols b).Nodup := by
    intro b
    have hb : b ∈ List.finRange (hcEll n) := List.mem_finRange b
    generalize List.finRange (hcEll n) = bs at hfm hb
    induction bs with
    | nil => cases hb
    | cons a rest ih =>
      simp only [List.flatMap_cons, List.nodup_append] at hfm
      rw [List.mem_cons] at hb
      rcases hb with rfl | hrest
      · exact hfm.1
      · exact ih hfm.2.1 hrest
  refine fun b => ⟨hmem b, fun b' hne w hwb hwb' => ?_⟩
  have ha : b ∈ List.finRange (hcEll n) := List.mem_finRange b
  have hb' : b' ∈ List.finRange (hcEll n) := List.mem_finRange b'
  have hnd := List.nodup_finRange (hcEll n)
  generalize List.finRange (hcEll n) = bs at hfm ha hb' hnd
  induction bs with
  | nil => cases ha
  | cons a rest ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.flatMap_cons, List.nodup_append] at hfm
    rw [List.mem_cons] at ha hb'
    rcases ha with rfl | ha <;> rcases hb' with rfl | hb'
    · exact hne rfl
    · exact hfm.2.2 w hwb w (List.mem_flatMap.mpr ⟨b', hb', hwb'⟩) rfl
    · exact hfm.2.2 w hwb' w (List.mem_flatMap.mpr ⟨b, ha, hwb⟩) rfl
    · exact ih hfm.2.1 ha hb' hnd.2

private lemma csValid_init (n : ℕ) (hn : 1 ≤ n) : CSValid n (csInit n) := by
  have hell := hcEll_pos hn
  refine ⟨by simp [csInit], ?_, ?_, ?_⟩
  · dsimp only [csInit]
    apply nodup_flatMap_of (List.nodup_finRange _)
    · intro b _
      split_ifs
      · refine List.Nodup.map (fun i j h => ?_) (List.nodup_finRange n)
        exact Fin.ext (by simpa [hcQWire] using congrArg Fin.val h)
      · simp
    · intro a _ b _ hab w hwa hwb
      split_ifs at hwa hwb with ha hb
      · exact hab (Fin.ext (by omega))
      · simp at hwb
      · simp at hwa
      · simp at hwa
  · intro b w hw
    dsimp only [csInit] at hw
    split_ifs at hw
    · simp only [List.mem_map, List.mem_finRange, true_and] at hw
      rcases hw with ⟨i, rfl⟩
      left; exact i.isLt
    · cases hw
  · dsimp only [csInit]
    let z0 : Fin (hcEll n) := ⟨0, hell⟩
    have hlen : ∀ b : Fin (hcEll n),
        (if b.1 = 0 then (List.finRange n).map (hcQWire n) else []).length =
        if b = z0 then n else 0 := by
      intro b
      by_cases hb : b = z0
      · subst hb; simp [z0]
      · have hne : b.1 ≠ 0 := fun h => hb (Fin.ext h)
        rw [if_neg hne, if_neg hb, List.length_nil]
    simp_rw [hlen]
    simp

private lemma sum_shift_pred_le {m : ℕ} (hm : 1 ≤ m) (f : Fin m → ℕ) :
    (∑ b : Fin m, if h : 0 < b.1 then f ⟨b.1 - 1, by have := b.isLt; omega⟩ else 0) ≤
      ∑ b : Fin m, f b := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = k + 1 := ⟨m - 1, by omega⟩
  have hsub : ∀ g : Fin (k + 1) → ℕ,
      (∑ b : Fin (k + 1), if h : 0 < b.1 then g ⟨b.1 - 1, by have := b.isLt; omega⟩ else 0) ≤
        ∑ b : Fin (k + 1), g b := by
    intro g
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_zero, lt_self_iff_false, ↓reduceDIte, zero_add, Fin.val_succ,
      Nat.zero_lt_succ, Nat.add_sub_cancel]
    exact Nat.le_add_right _ _
  subst hk
  exact hsub f

private lemma csValid_step {n : ℕ} (hn : 1 ≤ n) {st : CSState n} (hv : CSValid n st) :
    CSValid n (csStep n st) := by
  have hell := hcEll_pos hn
  have hnext_le : st.nextPair + (csAllTriples n st).length ≤ n :=
    csValid_nextPair_add_triples hv
  have hmem_lt : ∀ {p}, p ∈ numberItems st.nextPair (csAllTriples n st) → p.2 < n := by
    intro p hp
    have hb := mem_numberItems_bounds hp
    omega
  have hpair' : (csStep n st).nextPair ≤ n := hnext_le
  have hnodup_cols := csValid_cols_nodup hv
  have hwire' : ∀ b : Fin (hcEll n), ∀ w ∈ (csStep n st).cols b,
      w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * (csStep n st).nextPair) := by
    intro b w hw
    dsimp only [csStep] at hw ⊢
    simp only [List.mem_append, List.mem_map, List.mem_filter] at hw
    rcases hw with (hw | ⟨p, ⟨hp, _⟩, rfl⟩) | ⟨p, ⟨hp, _⟩, rfl⟩
    · rcases hv.wire_bound b w (takeTriples_mem_snd hw) with hq | hp
      · left; exact hq
      · right; omega
    · have hb := mem_numberItems_bounds hp
      right; rw [csRawSum_val (hmem_lt hp)]; omega
    · have hb := mem_numberItems_bounds hp
      right; rw [csRawCarry_val (hmem_lt hp)]; omega
  have hwork' : (∑ b : Fin (hcEll n), ((csStep n st).cols b).length) +
      (csStep n st).nextPair ≤ n := by
    have hcol_sum : (∑ b : Fin (hcEll n), ((csStep n st).cols b).length) =
        (∑ b : Fin (hcEll n), ((st.cols b).length % 3 + (st.cols b).length / 3)) +
        ∑ b : Fin (hcEll n),
          (if h : 0 < b.1 then (st.cols ⟨b.1 - 1, by have := b.isLt; omega⟩).length / 3 else 0) := by
      simp_rw [csStep_col_length, Finset.sum_add_distrib]
    have hcarry_le : (∑ b : Fin (hcEll n),
        (if h : 0 < b.1 then (st.cols ⟨b.1 - 1, by have := b.isLt; omega⟩).length / 3 else 0)) ≤
        ∑ b : Fin (hcEll n), (st.cols b).length / 3 :=
      sum_shift_pred_le hell (fun b => (st.cols b).length / 3)
    have hrem_add : (∑ b : Fin (hcEll n), ((st.cols b).length % 3 + (st.cols b).length / 3)) +
        (∑ b : Fin (hcEll n), (st.cols b).length / 3) + (csAllTriples n st).length =
        ∑ b : Fin (hcEll n), (st.cols b).length := by
      rw [csAllTriples_length, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      omega
    have hnext_val : (csStep n st).nextPair = st.nextPair + (csAllTriples n st).length := rfl
    have hwl := hv.work_le
    rw [hcol_sum, hnext_val]
    omega
  have hnodup' : ((List.finRange (hcEll n)).flatMap (csStep n st).cols).Nodup := by
    apply nodup_flatMap_of (List.nodup_finRange _)
    · intro b _
      dsimp only [csStep]
      rw [List.nodup_append, List.nodup_append]
      refine ⟨⟨takeTriples_nodup_snd (hnodup_cols b).1, ?_, ?_⟩, ?_, ?_⟩
      · refine nodup_map_of_pairwise ?_
        refine ((numberItems_pairwise_ne st.nextPair (csAllTriples n st)).filter _).imp_of_mem ?_
        intro p q hp hq hpq heq
        simp only [List.mem_filter] at hp hq
        have hval := congrArg Fin.val heq
        rw [csRawSum_val (hmem_lt hp.1), csRawSum_val (hmem_lt hq.1)] at hval
        exact hpq (by omega)
      · intro w hwr w' hws heq
        subst heq
        simp only [List.mem_map, List.mem_filter] at hws
        rcases hws with ⟨p, ⟨hp, _⟩, rfl⟩
        rcases hv.wire_bound b _ (takeTriples_mem_snd hwr) with hwq | hwp
        · have := csRawSum_val (hmem_lt hp); omega
        · have := (mem_numberItems_bounds hp).1; have := csRawSum_val (hmem_lt hp); omega
      · refine nodup_map_of_pairwise ?_
        refine ((numberItems_pairwise_ne st.nextPair (csAllTriples n st)).filter _).imp_of_mem ?_
        intro p q hp hq hpq heq
        simp only [List.mem_filter] at hp hq
        have hval := congrArg Fin.val heq
        rw [csRawCarry_val (hmem_lt hp.1), csRawCarry_val (hmem_lt hq.1)] at hval
        exact hpq (by omega)
      · intro w hwa w' hwc heq
        subst heq
        simp only [List.mem_append, List.mem_map, List.mem_filter] at hwa hwc
        rcases hwc with ⟨q, ⟨hq, _⟩, rfl⟩
        rcases hwa with hwr | ⟨p, ⟨hp, _⟩, heq⟩
        · rcases hv.wire_bound b _ (takeTriples_mem_snd hwr) with hwq | hwp
          · have := csRawCarry_val (hmem_lt hq); omega
          · have := (mem_numberItems_bounds hq).1; have := csRawCarry_val (hmem_lt hq); omega
        · have hval := congrArg Fin.val heq
          rw [csRawSum_val (hmem_lt hp), csRawCarry_val (hmem_lt hq)] at hval
          omega
    · intro a _ b _ hab w hwa hwb
      dsimp only [csStep] at hwa hwb
      simp only [List.mem_append, List.mem_map, List.mem_filter] at hwa hwb
      rcases hwa with (hwa | ⟨p, ⟨hp, hpa⟩, rfl⟩) | ⟨p, ⟨hp, hpa⟩, rfl⟩ <;>
        rcases hwb with (hwb | ⟨q, ⟨hq, hqb⟩, heq⟩) | ⟨q, ⟨hq, hqb⟩, heq⟩
      · exact (hnodup_cols a).2 b hab w (takeTriples_mem_snd hwa) (takeTriples_mem_snd hwb)
      · have hq1 := (mem_numberItems_bounds hq).1
        rcases hv.wire_bound a w (takeTriples_mem_snd hwa) with hwq | hwp
        · have := congrArg Fin.val heq; rw [csRawSum_val (hmem_lt hq)] at this; omega
        · have := congrArg Fin.val heq; rw [csRawSum_val (hmem_lt hq)] at this; omega
      · have hq1 := (mem_numberItems_bounds hq).1
        rcases hv.wire_bound a w (takeTriples_mem_snd hwa) with hwq | hwp
        · have := congrArg Fin.val heq; rw [csRawCarry_val (hmem_lt hq)] at this; omega
        · have := congrArg Fin.val heq; rw [csRawCarry_val (hmem_lt hq)] at this; omega
      · have hp1 := (mem_numberItems_bounds hp).1
        rcases hv.wire_bound b _ (takeTriples_mem_snd hwb) with hwq | hwp
        · have := csRawSum_val (hmem_lt hp); omega
        · have := csRawSum_val (hmem_lt hp); omega
      · have hval := congrArg Fin.val heq
        rw [csRawSum_val (hmem_lt hp), csRawSum_val (hmem_lt hq)] at hval
        have heq_p : p = q :=
          pairwise_eq_of_snd (numberItems_pairwise_ne st.nextPair (csAllTriples n st)) hp hq (by omega)
        subst heq_p
        simp only [decide_eq_true_eq] at hpa hqb
        exact hab (hpa.symm.trans hqb)
      · have hval := congrArg Fin.val heq
        rw [csRawSum_val (hmem_lt hp), csRawCarry_val (hmem_lt hq)] at hval
        omega
      · have hp1 := (mem_numberItems_bounds hp).1
        rcases hv.wire_bound b _ (takeTriples_mem_snd hwb) with hwq | hwp
        · have := csRawCarry_val (hmem_lt hp); omega
        · have := csRawCarry_val (hmem_lt hp); omega
      · have hval := congrArg Fin.val heq
        rw [csRawCarry_val (hmem_lt hp), csRawSum_val (hmem_lt hq)] at hval
        omega
      · have hval := congrArg Fin.val heq
        rw [csRawCarry_val (hmem_lt hp), csRawCarry_val (hmem_lt hq)] at hval
        have heq_p : p = q :=
          pairwise_eq_of_snd (numberItems_pairwise_ne st.nextPair (csAllTriples n st)) hp hq (by omega)
        subst heq_p
        simp only [decide_eq_true_eq] at hpa hqb
        exact hab (Fin.ext (by omega))
  exact ⟨hpair', hnodup', hwire', hwork'⟩

private lemma csValid_at (n : ℕ) (hn : 1 ≤ n) (r : ℕ) : CSValid n (csStateAt n r) := by
  induction r with
  | zero => exact csValid_init n hn
  | succ r ih => exact csValid_step hn ih

private def csTripleWireSet {n : ℕ}
    (item : (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ) :
    Finset (Fin (hcWires n)) :=
  {item.1.2.1, item.1.2.2.1, item.1.2.2.2, csRawSum n item.2, csRawCarry n item.2}

private noncomputable def csTripleGate {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (item : (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)
    (hitem : item ∈ numberItems st.nextPair (csAllTriples n st)) :
    { lc : LayeredCircuit (hcWires n) //
      lc.UsesOnly (csTripleWireSet item) ∧ lc.size = 13 ∧ lc.depth = 13 } :=
  let b := item.1.1
  let w1 := item.1.2.1
  let w2 := item.1.2.2.1
  let w3 := item.1.2.2.2
  let ws := csRawSum n item.2
  let wc := csRawCarry n item.2
  have hmem := mem_numberItems_bounds hitem
  have hT_le := csValid_nextPair_add_triples hv
  have hidx_lt : item.2 < n := by omega
  have htri : (w1, w2, w3) ∈ (takeTriples (st.cols b)).1 := by
    have hm := hmem.2.2
    simp only [csAllTriples, List.mem_flatMap, List.mem_map] at hm
    rcases hm with ⟨b', _, t', ht', heq⟩
    have hb : b' = b := congrArg Prod.fst heq
    have ht : t' = (w1, w2, w3) := congrArg Prod.snd heq
    subst hb; subst ht; exact ht'
  have hcol_nd : (st.cols b).Nodup := (csValid_cols_nodup hv b).1
  have h123 := (takeTriples_triples_disjoint hcol_nd).2 (w1, w2, w3) htri
  have hw_bnd : ∀ w ∈ (st.cols b), w.1 < n ∨
      (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * st.nextPair) := hv.wire_bound b
  have hmem_col := takeTriples_mem_fst htri
  have hw1_b := hw_bnd w1 hmem_col.1
  have hw2_b := hw_bnd w2 hmem_col.2.1
  have hw3_b := hw_bnd w3 hmem_col.2.2
  have hws_v := csRawSum_val hidx_lt
  have hwc_v := csRawCarry_val hidx_lt
  have h1s : w1 ≠ ws := fun h => by have := congrArg Fin.val h; omega
  have h1c : w1 ≠ wc := fun h => by have := congrArg Fin.val h; omega
  have h2s : w2 ≠ ws := fun h => by have := congrArg Fin.val h; omega
  have h2c : w2 ≠ wc := fun h => by have := congrArg Fin.val h; omega
  have h3s : w3 ≠ ws := fun h => by have := congrArg Fin.val h; omega
  have h3c : w3 ≠ wc := fun h => by have := congrArg Fin.val h; omega
  have hsc : ws ≠ wc := fun h => by have := congrArg Fin.val h; omega
  ⟨fullAdder5 w1 w2 w3 ws wc h123.1 h1s h1c h2s h2c h3s h3c hsc,
    fullAdder5_usesOnly w1 w2 w3 ws wc h123.1 h1s h1c h2s h2c h3s h3c hsc,
    fullAdder5_size _ _ _ _ _ _ _ _ _ _ _ _ _,
    fullAdder5_depth _ _ _ _ _ _ _ _ _ _ _ _ _⟩

private lemma csAllTriples_pairwise_disjoint {n : ℕ} (st : CSState n)
    (hv : CSValid n st) :
    (numberItems st.nextPair (csAllTriples n st)).Pairwise fun p q =>
      Disjoint (csTripleWireSet p) (csTripleWireSet q) := by
  have htri_pw : (csAllTriples n st).Pairwise fun a b =>
      Disjoint ({a.2.1, a.2.2.1, a.2.2.2} : Finset (Fin (hcWires n)))
        ({b.2.1, b.2.2.1, b.2.2.2} : Finset (Fin (hcWires n))) := by
    have hnodup_cols := csValid_cols_nodup hv
    dsimp only [csAllTriples]
    have hgen : ∀ bs : List (Fin (hcEll n)), bs.Nodup →
        (bs.flatMap fun b => (takeTriples (st.cols b)).1.map fun t => (b, t)).Pairwise fun a b =>
          Disjoint ({a.2.1, a.2.2.1, a.2.2.2} : Finset (Fin (hcWires n)))
            ({b.2.1, b.2.2.1, b.2.2.2} : Finset (Fin (hcWires n))) := by
      intro bs hbs
      induction bs with
      | nil => simp
      | cons b rest ih =>
        rw [List.nodup_cons] at hbs
        simp only [List.flatMap_cons, List.pairwise_append]
        refine ⟨?_, ih hbs.2, ?_⟩
        · rw [List.pairwise_map]
          exact (takeTriples_triples_disjoint (hnodup_cols b).1).1
        · intro x hx y hy
          simp only [List.mem_map] at hx
          simp only [List.mem_flatMap, List.mem_map] at hy
          rcases hx with ⟨tx, htx, rfl⟩
          rcases hy with ⟨b', hb', ty, hty, rfl⟩
          have hbb' : b ≠ b' := fun h => hbs.1 (h ▸ hb')
          have hmx := takeTriples_mem_fst htx
          have hmy := takeTriples_mem_fst hty
          rw [Finset.disjoint_left]
          intro w hwx hwy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwx hwy
          have hwx' : w ∈ st.cols b := by
            rcases hwx with rfl | rfl | rfl
            · exact hmx.1
            · exact hmx.2.1
            · exact hmx.2.2
          have hwy' : w ∈ st.cols b' := by
            rcases hwy with rfl | rfl | rfl
            · exact hmy.1
            · exact hmy.2.1
            · exact hmy.2.2
          exact (hnodup_cols b).2 b' hbb' w hwx' hwy'
    exact hgen (List.finRange (hcEll n)) (List.nodup_finRange _)
  have hnumber : ∀ (start : ℕ) (xs : List (Fin (hcEll n) ×
        (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n)))),
      xs.Pairwise (fun a b =>
        Disjoint ({a.2.1, a.2.2.1, a.2.2.2} : Finset (Fin (hcWires n)))
          ({b.2.1, b.2.2.1, b.2.2.2} : Finset (Fin (hcWires n)))) →
      start + xs.length ≤ n →
      (∀ x ∈ xs, x.2.1.1 < n ∨ (n + hcEll n ≤ x.2.1.1 ∧ x.2.1.1 < n + hcEll n + 2 * start)) →
      (∀ x ∈ xs, x.2.2.1.1 < n ∨ (n + hcEll n ≤ x.2.2.1.1 ∧ x.2.2.1.1 < n + hcEll n + 2 * start)) →
      (∀ x ∈ xs, x.2.2.2.1 < n ∨ (n + hcEll n ≤ x.2.2.2.1 ∧ x.2.2.2.1 < n + hcEll n + 2 * start)) →
      (numberItems start xs).Pairwise fun p q =>
        Disjoint (csTripleWireSet p) (csTripleWireSet q) := by
    intro start xs hpwx hlen h1 h2 h3
    induction xs generalizing start with
    | nil => simp [numberItems]
    | cons x rest ih =>
      rw [List.pairwise_cons] at hpwx
      simp only [numberItems, List.pairwise_cons]
      refine ⟨fun q hq => ?_, ih (start + 1) hpwx.2 (by simp at hlen; omega)
        (fun y hy => by rcases h1 y (List.mem_cons_of_mem _ hy) with h | h <;> [left; right] <;> omega)
        (fun y hy => by rcases h2 y (List.mem_cons_of_mem _ hy) with h | h <;> [left; right] <;> omega)
        (fun y hy => by rcases h3 y (List.mem_cons_of_mem _ hy) with h | h <;> [left; right] <;> omega)⟩
      have hqb := mem_numberItems_bounds hq
      have hstart_lt : start < n := by simp at hlen; omega
      have hq_lt : q.2 < n := by simp at hlen; omega
      have hdisj_in := hpwx.1 q.1 hqb.2.2
      have hx1 := h1 x List.mem_cons_self
      have hx2 := h2 x List.mem_cons_self
      have hx3 := h3 x List.mem_cons_self
      have hq1 := h1 q.1 (List.mem_cons_of_mem _ hqb.2.2)
      have hq2 := h2 q.1 (List.mem_cons_of_mem _ hqb.2.2)
      have hq3 := h3 q.1 (List.mem_cons_of_mem _ hqb.2.2)
      have hws1 := csRawSum_val hstart_lt
      have hwc1 := csRawCarry_val hstart_lt
      have hws2 := csRawSum_val hq_lt
      have hwc2 := csRawCarry_val hq_lt
      have hx_eq : csTripleWireSet (x, start) =
          ({x.2.1, x.2.2.1, x.2.2.2} : Finset (Fin (hcWires n))) ∪
            ({csRawSum n start, csRawCarry n start} : Finset (Fin (hcWires n))) := by
        ext w; simp only [csTripleWireSet, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
        · rintro ((rfl | rfl | rfl) | (rfl | rfl)) <;> simp
      have hq_eq : csTripleWireSet q =
          ({q.1.2.1, q.1.2.2.1, q.1.2.2.2} : Finset (Fin (hcWires n))) ∪
            ({csRawSum n q.2, csRawCarry n q.2} : Finset (Fin (hcWires n))) := by
        ext w; simp only [csTripleWireSet, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
        · rintro ((rfl | rfl | rfl) | (rfl | rfl)) <;> simp
      have hxin_lt : ∀ w ∈ ({x.2.1, x.2.2.1, x.2.2.2} : Finset (Fin (hcWires n))),
          w.1 < n + hcEll n + 2 * start := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · rcases hx1 with h | h <;> omega
        · rcases hx2 with h | h <;> omega
        · rcases hx3 with h | h <;> omega
      have hqin_lt : ∀ w ∈ ({q.1.2.1, q.1.2.2.1, q.1.2.2.2} : Finset (Fin (hcWires n))),
          w.1 < n + hcEll n + 2 * start := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · rcases hq1 with h | h <;> omega
        · rcases hq2 with h | h <;> omega
        · rcases hq3 with h | h <;> omega
      have hxout_ge : ∀ w ∈ ({csRawSum n start, csRawCarry n start} : Finset (Fin (hcWires n))),
          n + hcEll n + 2 * start ≤ w.1 ∧ w.1 < n + hcEll n + 2 * (start + 1) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> omega
      have hqout_ge : ∀ w ∈ ({csRawSum n q.2, csRawCarry n q.2} : Finset (Fin (hcWires n))),
          n + hcEll n + 2 * (start + 1) ≤ w.1 := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        have hsq : start + 1 ≤ q.2 := hqb.1
        rcases hw with rfl | rfl <;> omega
      rw [hx_eq, hq_eq, Finset.disjoint_union_left, Finset.disjoint_union_right,
        Finset.disjoint_union_right]
      refine ⟨⟨hdisj_in, ?_⟩, ⟨?_, ?_⟩⟩
      · rw [Finset.disjoint_left]
        intro w hwx hwq
        have := hxin_lt w hwx
        have := hqout_ge w hwq
        omega
      · rw [Finset.disjoint_left]
        intro w hwx hwq
        have := hxout_ge w hwx
        have := hqin_lt w hwq
        omega
      · rw [Finset.disjoint_left]
        intro w hwx hwq
        have := hxout_ge w hwx
        have := hqout_ge w hwq
        omega
  have hT_le := csValid_nextPair_add_triples hv
  have hmem_tri : ∀ x ∈ csAllTriples n st,
      (x.2.1.1 < n ∨ (n + hcEll n ≤ x.2.1.1 ∧ x.2.1.1 < n + hcEll n + 2 * st.nextPair)) ∧
      (x.2.2.1.1 < n ∨ (n + hcEll n ≤ x.2.2.1.1 ∧ x.2.2.1.1 < n + hcEll n + 2 * st.nextPair)) ∧
      (x.2.2.2.1 < n ∨ (n + hcEll n ≤ x.2.2.2.1 ∧ x.2.2.2.1 < n + hcEll n + 2 * st.nextPair)) := by
    intro ⟨b, t⟩ hx
    simp only [csAllTriples, List.mem_flatMap, List.mem_map] at hx
    rcases hx with ⟨b', _, t', ht', heq⟩
    have hm := takeTriples_mem_fst ht'
    have h1 := hv.wire_bound b' t'.1 hm.1
    have h2 := hv.wire_bound b' t'.2.1 hm.2.1
    have h3 := hv.wire_bound b' t'.2.2 hm.2.2
    have ht_eq : (b', t') = (b, t) := heq
    cases ht_eq
    exact ⟨h1, h2, h3⟩
  exact hnumber st.nextPair (csAllTriples n st) htri_pw hT_le
    (fun x hx => (hmem_tri x hx).1)
    (fun x hx => (hmem_tri x hx).2.1)
    (fun x hx => (hmem_tri x hx).2.2)

private def csApplyList (n : ℕ) (z : Qubits (hcWires n)) :
    List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ) →
    Qubits (hcWires n)
  | [] => z
  | item :: rest =>
    let restQ := csApplyList n z rest
    let w1 := item.1.2.1
    let w2 := item.1.2.2.1
    let w3 := item.1.2.2.2
    fun w =>
      if w = csRawSum n item.2 then xor (xor (z w1) (z w2)) (z w3)
      else if w = csRawCarry n item.2 then xor (z w1 && z w2) (xor (z w1) (z w2) && z w3)
      else restQ w

private lemma csApplyList_sum {n : ℕ} (z : Qubits (hcWires n))
    {L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)}
    (hpw : L.Pairwise fun p q => p.2 ≠ q.2)
    (hlt : ∀ p ∈ L, p.2 < n)
    {item : (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ}
    (hitem : item ∈ L) :
    csApplyList n z L (csRawSum n item.2) =
      xor (xor (z item.1.2.1) (z item.1.2.2.1)) (z item.1.2.2.2) := by
  induction L with
  | nil => cases hitem
  | cons h rest ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.mem_cons] at hitem
    dsimp only [csApplyList]
    rcases hitem with rfl | hrest
    · rw [if_pos rfl]
    · have hne_idx : h.2 ≠ item.2 := hpw.1 item hrest
      have hh_lt : h.2 < n := hlt h List.mem_cons_self
      have hi_lt : item.2 < n := hlt item (List.mem_cons_of_mem _ hrest)
      have hs := csRawSum_val hh_lt
      have hc := csRawCarry_val hh_lt
      have his := csRawSum_val hi_lt
      have hns : csRawSum n item.2 ≠ csRawSum n h.2 := fun e => by
        have := congrArg Fin.val e; omega
      have hnc : csRawSum n item.2 ≠ csRawCarry n h.2 := fun e => by
        have := congrArg Fin.val e; omega
      rw [if_neg hns, if_neg hnc]
      exact ih hpw.2 (fun p hp => hlt p (List.mem_cons_of_mem _ hp)) hrest

private lemma csApplyList_carry {n : ℕ} (z : Qubits (hcWires n))
    {L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)}
    (hpw : L.Pairwise fun p q => p.2 ≠ q.2)
    (hlt : ∀ p ∈ L, p.2 < n)
    {item : (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ}
    (hitem : item ∈ L) :
    csApplyList n z L (csRawCarry n item.2) =
      xor (z item.1.2.1 && z item.1.2.2.1)
        (xor (z item.1.2.1) (z item.1.2.2.1) && z item.1.2.2.2) := by
  induction L with
  | nil => cases hitem
  | cons h rest ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.mem_cons] at hitem
    dsimp only [csApplyList]
    rcases hitem with rfl | hrest
    · have hh_lt : item.2 < n := hlt item List.mem_cons_self
      have hs := csRawSum_val hh_lt
      have hc := csRawCarry_val hh_lt
      have hne : csRawCarry n item.2 ≠ csRawSum n item.2 := fun e => by
        have := congrArg Fin.val e; omega
      rw [if_neg hne, if_pos rfl]
    · have hne_idx : h.2 ≠ item.2 := hpw.1 item hrest
      have hh_lt : h.2 < n := hlt h List.mem_cons_self
      have hi_lt : item.2 < n := hlt item (List.mem_cons_of_mem _ hrest)
      have hs := csRawSum_val hh_lt
      have hc := csRawCarry_val hh_lt
      have hic := csRawCarry_val hi_lt
      have hns : csRawCarry n item.2 ≠ csRawSum n h.2 := fun e => by
        have := congrArg Fin.val e; omega
      have hnc : csRawCarry n item.2 ≠ csRawCarry n h.2 := fun e => by
        have := congrArg Fin.val e; omega
      rw [if_neg hns, if_neg hnc]
      exact ih hpw.2 (fun p hp => hlt p (List.mem_cons_of_mem _ hp)) hrest

private lemma csApplyList_other {n : ℕ} (z : Qubits (hcWires n))
    {L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)}
    {w : Fin (hcWires n)} (hw : ∀ item ∈ L, w ≠ csRawSum n item.2 ∧ w ≠ csRawCarry n item.2) :
    csApplyList n z L w = z w := by
  induction L with
  | nil => rfl
  | cons h rest ih =>
    dsimp only [csApplyList]
    have hh := hw h List.mem_cons_self
    rw [if_neg hh.1, if_neg hh.2]
    exact ih (fun p hp => hw p (List.mem_cons_of_mem _ hp))

private lemma mem_foldr_union_of_mem {α β : Type*} [DecidableEq β]
    {xs : List (α × Finset β)} {p : α × Finset β} {w : β}
    (hp : p ∈ xs) (hw : w ∈ p.2) :
    w ∈ xs.foldr (fun q acc => q.2 ∪ acc) ∅ := by
  induction xs with
  | nil => cases hp
  | cons q rest ih =>
    rw [List.mem_cons] at hp
    simp only [List.foldr_cons, Finset.mem_union]
    rcases hp with rfl | hrest
    · left; exact hw
    · right; exact ih hrest

private noncomputable def csRoundList {n : ℕ} (st : CSState n) (hv : CSValid n st) :
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)) →
    (∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) →
    List (LayeredCircuit (hcWires n) × Finset (Fin (hcWires n)))
  | [], _ => []
  | item :: rest, h =>
    ((csTripleGate st hv item (h item List.mem_cons_self)).1, csTripleWireSet item) ::
      csRoundList st hv rest (fun p hp => h p (List.mem_cons_of_mem _ hp))

private lemma csRoundList_usesOnly {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    ∀ p ∈ csRoundList st hv L h, p.1.UsesOnly p.2 := by
  induction L with
  | nil => intro p hp; cases hp
  | cons item rest ih =>
    intro p hp
    dsimp only [csRoundList] at hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact (csTripleGate st hv item (h item List.mem_cons_self)).2.1
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) p hp

private lemma csRoundList_map_snd {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    (csRoundList st hv L h).map Prod.snd = L.map csTripleWireSet := by
  induction L with
  | nil => rfl
  | cons item rest ih =>
    simp only [csRoundList, List.map_cons]
    congr 1
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

private lemma csRoundList_pairwise {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st))
    (hpw : L.Pairwise fun p q => Disjoint (csTripleWireSet p) (csTripleWireSet q)) :
    (csRoundList st hv L h).Pairwise fun p q => Disjoint p.2 q.2 := by
  induction L with
  | nil => simp [csRoundList]
  | cons item rest ih =>
    rw [List.pairwise_cons] at hpw
    simp only [csRoundList, List.pairwise_cons]
    refine ⟨fun q hq => ?_, ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) hpw.2⟩
    have hq2 : q.2 ∈ (csRoundList st hv rest _).map Prod.snd := List.mem_map_of_mem hq
    rw [csRoundList_map_snd, List.mem_map] at hq2
    rcases hq2 with ⟨item', hitem', heq⟩
    rw [← heq]
    exact hpw.1 item' hitem'

private lemma csRoundList_size {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    ((csRoundList st hv L h).map fun p => p.1.size).sum = 13 * L.length := by
  induction L with
  | nil => simp [csRoundList]
  | cons item rest ih =>
    simp only [csRoundList, List.map_cons, List.sum_cons, List.length_cons,
      (csTripleGate st hv item (h item List.mem_cons_self)).2.2.1,
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    ring

private lemma csRoundList_depth {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    ∀ p ∈ csRoundList st hv L h, p.1.depth ≤ 13 := by
  induction L with
  | nil => intro p hp; cases hp
  | cons item rest ih =>
    intro p hp
    dsimp only [csRoundList] at hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · dsimp only
      have := (csTripleGate st hv item (h item List.mem_cons_self)).2.2.2
      omega
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) p hp

private lemma csRoundList_fwd {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    ∀ p ∈ csRoundList st hv L h, p.2 ⊆ fwdSupport n := by
  have hT_le := csValid_nextPair_add_triples hv
  induction L with
  | nil => intro p hp; cases hp
  | cons item rest ih =>
    intro p hp
    dsimp only [csRoundList] at hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · intro w hw
      have hb := mem_numberItems_bounds (h item List.mem_cons_self)
      have hidx_lt : item.2 < n := by omega
      have hmem_tri := hb.2.2
      simp only [csAllTriples, List.mem_flatMap, List.mem_map] at hmem_tri
      rcases hmem_tri with ⟨b', _, t', ht', heq⟩
      have hmem_col := takeTriples_mem_fst ht'
      have h1 := hv.wire_bound b' t'.1 hmem_col.1
      have h2 := hv.wire_bound b' t'.2.1 hmem_col.2.1
      have h3 := hv.wire_bound b' t'.2.2 hmem_col.2.2
      have ht1 : t'.1 = item.1.2.1 := congrArg (fun q => q.2.1) heq
      have ht2 : t'.2.1 = item.1.2.2.1 := congrArg (fun q => q.2.2.1) heq
      have ht3 : t'.2.2 = item.1.2.2.2 := congrArg (fun q => q.2.2.2) heq
      rw [mem_fwdSupport_iff]
      simp only [csTripleWireSet, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · rw [← ht1]; rcases h1 with hlt | hlt <;> [left; right] <;> omega
      · rw [← ht2]; rcases h2 with hlt | hlt <;> [left; right] <;> omega
      · rw [← ht3]; rcases h3 with hlt | hlt <;> [left; right] <;> omega
      · right; rw [csRawSum_val hidx_lt]; omega
      · right; rw [csRawCarry_val hidx_lt]; omega
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) p hp

private lemma act_csTripleGate_ket {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (item : (Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ)
    (hitem : item ∈ numberItems st.nextPair (csAllTriples n st))
    (z : Qubits (hcWires n))
    (hclean : ∀ w : Fin (hcWires n), n + hcEll n + 2 * st.nextPair ≤ w.1 → z w = false) :
    ∃ x' : Qubits (hcWires n),
      act (csTripleGate st hv item hitem).1.unitary (ket z) = ket x' ∧
      ∀ w ∈ csTripleWireSet item,
        x' w = csApplyList n z (numberItems st.nextPair (csAllTriples n st)) w := by
  let ann := numberItems st.nextPair (csAllTriples n st)
  have hT_le := csValid_nextPair_add_triples hv
  have hann_pw : ann.Pairwise fun p q => p.2 ≠ q.2 :=
    numberItems_pairwise_ne st.nextPair (csAllTriples n st)
  have hann_lt : ∀ p ∈ ann, p.2 < n := by
    intro p hp; have := mem_numberItems_bounds hp; omega
  have hb := mem_numberItems_bounds hitem
  have hidx_lt : item.2 < n := by omega
  have hws_v := csRawSum_val hidx_lt
  have hwc_v := csRawCarry_val hidx_lt
  have hzs : z (csRawSum n item.2) = false := hclean _ (by omega)
  have hzc : z (csRawCarry n item.2) = false := hclean _ (by omega)
  have hmem_tri := hb.2.2
  simp only [csAllTriples, List.mem_flatMap, List.mem_map] at hmem_tri
  rcases hmem_tri with ⟨b', _, t', ht', heq⟩
  have hmem_col := takeTriples_mem_fst ht'
  have h1 := hv.wire_bound b' t'.1 hmem_col.1
  have h2 := hv.wire_bound b' t'.2.1 hmem_col.2.1
  have h3 := hv.wire_bound b' t'.2.2 hmem_col.2.2
  have ht1 : t'.1 = item.1.2.1 := congrArg (fun q => q.2.1) heq
  have ht2 : t'.2.1 = item.1.2.2.1 := congrArg (fun q => q.2.2.1) heq
  have ht3 : t'.2.2 = item.1.2.2.2 := congrArg (fun q => q.2.2.2) heq
  refine ⟨fun w =>
    if w = csRawSum n item.2 then xor (xor (z item.1.2.1) (z item.1.2.2.1)) (z item.1.2.2.2)
    else if w = csRawCarry n item.2 then
      xor (z item.1.2.1 && z item.1.2.2.1) (xor (z item.1.2.1) (z item.1.2.2.1) && z item.1.2.2.2)
    else z w, ?_, ?_⟩
  · dsimp only [csTripleGate]
    exact act_fullAdder5_ket _ _ _ _ _ _ _ _ _ _ _ _ _ z hzs hzc
  · intro w hw
    have houtside : ∀ u : Fin (hcWires n),
        (u.1 < n ∨ (n + hcEll n ≤ u.1 ∧ u.1 < n + hcEll n + 2 * st.nextPair)) →
        csApplyList n z ann u = z u := by
      intro u hu
      apply csApplyList_other
      intro q hq
      have hqb := mem_numberItems_bounds hq
      have hq_lt : q.2 < n := by omega
      have hqs := csRawSum_val hq_lt
      have hqc := csRawCarry_val hq_lt
      constructor <;> intro e <;> [have := congrArg Fin.val e; have := congrArg Fin.val e] <;> omega
    simp only [csTripleWireSet, Finset.mem_insert, Finset.mem_singleton] at hw
    dsimp only
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · have h1b : item.1.2.1.1 < n ∨
          (n + hcEll n ≤ item.1.2.1.1 ∧ item.1.2.1.1 < n + hcEll n + 2 * st.nextPair) := by
        rw [← ht1]; exact h1
      have h1s : item.1.2.1 ≠ csRawSum n item.2 := fun e => by have := congrArg Fin.val e; omega
      have h1c : item.1.2.1 ≠ csRawCarry n item.2 := fun e => by have := congrArg Fin.val e; omega
      rw [if_neg h1s, if_neg h1c, houtside _ h1b]
    · have h2b : item.1.2.2.1.1 < n ∨
          (n + hcEll n ≤ item.1.2.2.1.1 ∧ item.1.2.2.1.1 < n + hcEll n + 2 * st.nextPair) := by
        rw [← ht2]; exact h2
      have h2s : item.1.2.2.1 ≠ csRawSum n item.2 := fun e => by have := congrArg Fin.val e; omega
      have h2c : item.1.2.2.1 ≠ csRawCarry n item.2 := fun e => by have := congrArg Fin.val e; omega
      rw [if_neg h2s, if_neg h2c, houtside _ h2b]
    · have h3b : item.1.2.2.2.1 < n ∨
          (n + hcEll n ≤ item.1.2.2.2.1 ∧ item.1.2.2.2.1 < n + hcEll n + 2 * st.nextPair) := by
        rw [← ht3]; exact h3
      have h3s : item.1.2.2.2 ≠ csRawSum n item.2 := fun e => by have := congrArg Fin.val e; omega
      have h3c : item.1.2.2.2 ≠ csRawCarry n item.2 := fun e => by have := congrArg Fin.val e; omega
      rw [if_neg h3s, if_neg h3c, houtside _ h3b]
    · rw [if_pos rfl, csApplyList_sum z hann_pw hann_lt hitem]
    · have hcs : csRawCarry n item.2 ≠ csRawSum n item.2 := fun e => by
        have := congrArg Fin.val e; omega
      rw [if_neg hcs, if_pos rfl, csApplyList_carry z hann_pw hann_lt hitem]

private lemma csRoundList_act {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (L : List ((Fin (hcEll n) × (Fin (hcWires n) × Fin (hcWires n) × Fin (hcWires n))) × ℕ))
    (h : ∀ p ∈ L, p ∈ numberItems st.nextPair (csAllTriples n st)) :
    ∀ p ∈ csRoundList st hv L h, ∀ z : Qubits (hcWires n),
      (∀ w : Fin (hcWires n), n + hcEll n + 2 * st.nextPair ≤ w.1 → z w = false) →
      ∃ x' : Qubits (hcWires n), act p.1.unitary (ket z) = ket x' ∧
        ∀ w ∈ p.2, x' w = csApplyList n z (numberItems st.nextPair (csAllTriples n st)) w := by
  induction L with
  | nil => intro p hp; cases hp
  | cons item rest ih =>
    intro p hp z hclean
    dsimp only [csRoundList] at hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact act_csTripleGate_ket st hv item (h item List.mem_cons_self) z hclean
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) p hp z hclean

private noncomputable def csRoundItems {n : ℕ} (st : CSState n) (hv : CSValid n st) :
    { xs : List (LayeredCircuit (hcWires n) × Finset (Fin (hcWires n))) //
      (∀ p ∈ xs, p.1.UsesOnly p.2) ∧
      xs.Pairwise (fun p q => Disjoint p.2 q.2) ∧
      (xs.map fun p => p.1.size).sum = 13 * (csAllTriples n st).length ∧
      (∀ p ∈ xs, p.1.depth ≤ 13) ∧
      (∀ p ∈ xs, p.2 ⊆ fwdSupport n) ∧
      (∀ p ∈ xs, ∀ z : Qubits (hcWires n),
        (∀ w : Fin (hcWires n), n + hcEll n + 2 * st.nextPair ≤ w.1 → z w = false) →
        ∃ x' : Qubits (hcWires n), act p.1.unitary (ket z) = ket x' ∧
          ∀ w ∈ p.2, x' w = csApplyList n z (numberItems st.nextPair (csAllTriples n st)) w) ∧
      xs.map Prod.snd = (numberItems st.nextPair (csAllTriples n st)).map csTripleWireSet } :=
  let ann := numberItems st.nextPair (csAllTriples n st)
  ⟨csRoundList st hv ann (fun _ h => h),
    csRoundList_usesOnly st hv ann _,
    csRoundList_pairwise st hv ann _ (csAllTriples_pairwise_disjoint st hv),
    by rw [csRoundList_size st hv ann _, numberItems_length],
    csRoundList_depth st hv ann _,
    csRoundList_fwd st hv ann _,
    csRoundList_act st hv ann _,
    csRoundList_map_snd st hv ann _⟩

private noncomputable def csRoundCircuit {n : ℕ} (st : CSState n) (hv : CSValid n st) :
    { lc : LayeredCircuit (hcWires n) //
      lc.UsesOnly (fwdSupport n) ∧
      lc.size = 13 * (csAllTriples n st).length ∧
      lc.depth ≤ 13 } :=
  let items := csRoundItems st hv
  let merged := parMergeAux items.1 items.2.1 items.2.2.1
  have huses : merged.1.UsesOnly (fwdSupport n) := by
    refine merged.2.1.mono ?_
    have hfold : ∀ (L : List (LayeredCircuit (hcWires n) × Finset (Fin (hcWires n)))),
        (∀ p ∈ L, p.2 ⊆ fwdSupport n) → L.foldr (fun p acc => p.2 ∪ acc) ∅ ⊆ fwdSupport n := by
      intro L hL
      induction L with
      | nil => simp
      | cons p rest ih =>
        simp only [List.foldr_cons, Finset.union_subset_iff]
        exact ⟨hL p List.mem_cons_self, ih fun q hq => hL q (List.mem_cons_of_mem _ hq)⟩
    exact hfold items.1 items.2.2.2.2.2.1
  ⟨merged.1, huses, merged.2.2.1.trans items.2.2.2.1,
    le_trans merged.2.2.2 (foldr_max_le items.1 13 items.2.2.2.2.1)⟩

private noncomputable def csCircuitAt (n : ℕ) (hn : 1 ≤ n) : ℕ → LayeredCircuit (hcWires n)
  | 0 => LayeredCircuit.id (hcWires n)
  | r + 1 => (csCircuitAt n hn r).seq (csRoundCircuit (csStateAt n r) (csValid_at n hn r)).1

private lemma csCircuitAt_usesOnly (n : ℕ) (hn : 1 ≤ n) (r : ℕ) :
    (csCircuitAt n hn r).UsesOnly (fwdSupport n) := by
  induction r with
  | zero => exact LayeredCircuit.id_usesOnly _
  | succ r ih =>
    exact LayeredCircuit.seq_usesOnly ih (csRoundCircuit (csStateAt n r) (csValid_at n hn r)).2.1

private lemma csCircuitAt_size (n : ℕ) (hn : 1 ≤ n) (r : ℕ) :
    (csCircuitAt n hn r).size = 13 * (csStateAt n r).nextPair := by
  induction r with
  | zero => simp [csCircuitAt, csStateAt, csInit]
  | succ r ih =>
    simp only [csCircuitAt, csStateAt, csStep, LayeredCircuit.seq_size, ih,
      (csRoundCircuit (csStateAt n r) (csValid_at n hn r)).2.2.1]
    ring

private lemma csCircuitAt_size_le (n : ℕ) (hn : 1 ≤ n) (r : ℕ) :
    (csCircuitAt n hn r).size ≤ 13 * n := by
  rw [csCircuitAt_size]
  exact Nat.mul_le_mul_left 13 (csValid_at n hn r).pair_le

private lemma csCircuitAt_depth (n : ℕ) (hn : 1 ≤ n) (r : ℕ) :
    (csCircuitAt n hn r).depth ≤ 13 * r := by
  induction r with
  | zero => simp [csCircuitAt]
  | succ r ih =>
    simp only [csCircuitAt, LayeredCircuit.seq_depth]
    have hround := (csRoundCircuit (csStateAt n r) (csValid_at n hn r)).2.2.2
    omega

private lemma countP_eq_sum_map {α : Type*} (xs : List α) (p : α → Bool) :
    xs.countP p = (xs.map fun a => if p a then 1 else 0).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]
    cases p a <;> simp [Nat.add_comm]

private lemma list_finRange_countP {n : ℕ} (p : Fin n → Bool) :
    (List.finRange n).countP p = (Finset.univ.filter fun i : Fin n => p i = true).card := by
  rw [countP_eq_sum_map, List.map_congr_left (fun _ _ => rfl), sum_map_finRange, Finset.card_filter]

private lemma sum_map_flatMap {α β : Type*} (xs : List α) (f : α → List β) (g : β → ℕ) :
    ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih => simp [List.flatMap_cons, ih]

private lemma sum_filter_eq_map {α : Type*} {k : ℕ} (L : List α) (col : α → Fin k) (g : α → ℕ) :
    (∑ b : Fin k, 2 ^ b.1 * ((L.filter fun a => decide (col a = b)).map g).sum) =
      (L.map fun a => 2 ^ (col a).1 * g a).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    have hterm : ∀ b : Fin k,
        2 ^ b.1 * (List.map g (if decide (col a = b) = true then a :: rest.filter (fun x => decide (col x = b))
          else rest.filter (fun x => decide (col x = b)))).sum =
        (if col a = b then 2 ^ b.1 * g a else 0) +
          2 ^ b.1 * ((rest.filter fun x => decide (col x = b)).map g).sum := by
      intro b
      by_cases h : col a = b
      · simp [h, mul_add]
      · simp [h]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ih, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

private lemma sum_filter_succ_eq_map {α : Type*} {k : ℕ} (L : List α) (col : α → Fin k) (g : α → ℕ) :
    (∑ b : Fin k, 2 ^ b.1 * ((L.filter fun a => decide ((col a).1 + 1 = b.1)).map g).sum) +
      2 ^ k * ((L.filter fun a => decide ((col a).1 + 1 = k)).map g).sum =
      (L.map fun a => 2 ^ (col a).1 * 2 * g a).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases hlt : (col a).1 + 1 < k
    · let b0 : Fin k := ⟨(col a).1 + 1, hlt⟩
      have hne_k : (col a).1 + 1 ≠ k := by omega
      have hterm : ∀ b : Fin k,
          2 ^ b.1 * (List.map g (if decide ((col a).1 + 1 = b.1) = true then
              a :: rest.filter (fun x => decide ((col x).1 + 1 = b.1))
            else rest.filter (fun x => decide ((col x).1 + 1 = b.1)))).sum =
          (if b0 = b then 2 ^ b.1 * g a else 0) +
            2 ^ b.1 * ((rest.filter fun x => decide ((col x).1 + 1 = b.1)).map g).sum := by
        intro b
        by_cases h : b0 = b
        · have heq : (col a).1 + 1 = b.1 := by rw [← h]
          simp [h, heq, mul_add]
        · have hneq : (col a).1 + 1 ≠ b.1 := fun heq => h (Fin.ext heq)
          simp [h, hneq]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _),
        if_neg (by simp [hne_k])]
      have hpow : 2 ^ b0.1 = 2 ^ (col a).1 * 2 := by
        change 2 ^ ((col a).1 + 1) = 2 ^ (col a).1 * 2
        rw [pow_succ]
      rw [hpow, ← ih]
      ring
    · have hcol_eq : (col a).1 + 1 = k := by have := (col a).isLt; omega
      have hterm : ∀ b : Fin k,
          2 ^ b.1 * (List.map g (if decide ((col a).1 + 1 = b.1) = true then
              a :: rest.filter (fun x => decide ((col x).1 + 1 = b.1))
            else rest.filter (fun x => decide ((col x).1 + 1 = b.1)))).sum =
          2 ^ b.1 * ((rest.filter fun x => decide ((col x).1 + 1 = b.1)).map g).sum := by
        intro b
        have hneq : (col a).1 + 1 ≠ b.1 := by have := b.isLt; omega
        simp [hneq]
      simp_rw [hterm]
      rw [if_pos (by simp [hcol_eq]), List.map_cons, List.sum_cons]
      have h_assoc :
          (∑ x : Fin k, 2 ^ x.1 * ((rest.filter fun x_1 => decide ((col x_1).1 + 1 = x.1)).map g).sum) +
            2 ^ k * (g a + ((rest.filter fun x => decide ((col x).1 + 1 = k)).map g).sum) =
          2 ^ k * g a +
            ((∑ x : Fin k, 2 ^ x.1 * ((rest.filter fun x_1 => decide ((col x_1).1 + 1 = x.1)).map g).sum) +
              2 ^ k * ((rest.filter fun x => decide ((col x).1 + 1 = k)).map g).sum) := by ring
      have hpow : 2 ^ k = 2 ^ (col a).1 * 2 := by
        conv_lhs => rw [← hcol_eq, pow_succ]
      rw [h_assoc, ih, hpow]

private lemma act_csRoundCircuit_ket {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (z : Qubits (hcWires n))
    (hclean : ∀ w : Fin (hcWires n), n + hcEll n + 2 * st.nextPair ≤ w.1 → z w = false) :
    act (csRoundCircuit st hv).1.unitary (ket z) =
      ket (csApplyList n z (numberItems st.nextPair (csAllTriples n st))) := by
  dsimp only [csRoundCircuit]
  let ann := numberItems st.nextPair (csAllTriples n st)
  let z_next := csApplyList n z ann
  let items := csRoundItems st hv
  have hact_items : ∀ p ∈ items.1, ∃ x' : Qubits (hcWires n),
      act p.1.unitary (ket z) = ket x' ∧ ∀ w ∈ p.2, x' w = z_next w :=
    fun p hp => items.2.2.2.2.2.2.1 p hp z hclean
  rw [act_parMergeAux_ket items.1 items.2.1 items.2.2.1 z z_next hact_items]
  congr 1
  funext w
  split_ifs with hw
  · rfl
  · have hout : ∀ item ∈ ann, w ≠ csRawSum n item.2 ∧ w ≠ csRawCarry n item.2 := by
      intro item hitem
      have hset_mem : csTripleWireSet item ∈ items.1.map Prod.snd := by
        rw [items.2.2.2.2.2.2.2]
        exact List.mem_map_of_mem hitem
      rw [List.mem_map] at hset_mem
      rcases hset_mem with ⟨p, hp, hp_eq⟩
      constructor <;> intro heq <;> apply hw <;> rw [heq] <;>
        exact mem_foldr_union_of_mem hp (hp_eq ▸ by simp [csTripleWireSet])
    exact (csApplyList_other z hout).symm

private lemma csApplyList_preserve_low {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (z : Qubits (hcWires n)) {w : Fin (hcWires n)} (hw : w.1 < n + hcEll n) :
    csApplyList n z (numberItems st.nextPair (csAllTriples n st)) w = z w := by
  have hT_le := csValid_nextPair_add_triples hv
  apply csApplyList_other
  intro item hitem
  have hb := mem_numberItems_bounds hitem
  have hlt : item.2 < n := by omega
  have hs := csRawSum_val hlt
  have hc := csRawCarry_val hlt
  constructor <;> intro e <;> [have := congrArg Fin.val e; have := congrArg Fin.val e] <;> omega

private lemma csApplyList_preserve_high {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (z : Qubits (hcWires n)) {w : Fin (hcWires n)}
    (hw : n + hcEll n + 2 * (csStep n st).nextPair ≤ w.1) :
    csApplyList n z (numberItems st.nextPair (csAllTriples n st)) w = z w := by
  have hT_le := csValid_nextPair_add_triples hv
  apply csApplyList_other
  intro item hitem
  have hb := mem_numberItems_bounds hitem
  have hlt : item.2 < n := by omega
  have hs := csRawSum_val hlt
  have hc := csRawCarry_val hlt
  dsimp only [csStep] at hw
  constructor <;> intro e <;> [have := congrArg Fin.val e; have := congrArg Fin.val e] <;> omega

private lemma csApplyList_weighted_sum {n : ℕ} (st : CSState n) (hv : CSValid n st)
    (z : Qubits (hcWires n)) :
    let z' := csApplyList n z (numberItems st.nextPair (csAllTriples n st))
    (∑ b : Fin (hcEll n), 2 ^ b.1 * ((csStep n st).cols b).countP z') +
      2 ^ hcEll n * (((numberItems st.nextPair (csAllTriples n st)).filter
        fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p => if z' (csRawCarry n p.2) then 1 else 0).sum =
      ∑ b : Fin (hcEll n), 2 ^ b.1 * (st.cols b).countP z := by
  let ann := numberItems st.nextPair (csAllTriples n st)
  let z' := csApplyList n z ann
  have hT_le := csValid_nextPair_add_triples hv
  have hann_pw : ann.Pairwise fun p q => p.2 ≠ q.2 :=
    numberItems_pairwise_ne st.nextPair (csAllTriples n st)
  have hann_lt : ∀ p ∈ ann, p.2 < n := by
    intro p hp; have := mem_numberItems_bounds hp; omega
  have hrem_count : ∀ b : Fin (hcEll n),
      (takeTriples (st.cols b)).2.countP z' = (takeTriples (st.cols b)).2.countP z := by
    intro b
    refine List.countP_congr fun w hw => ?_
    have hwb := hv.wire_bound b w (takeTriples_mem_snd hw)
    have hout : ∀ item ∈ ann, w ≠ csRawSum n item.2 ∧ w ≠ csRawCarry n item.2 := by
      intro item hitem
      have hb := mem_numberItems_bounds hitem
      have hlt : item.2 < n := by omega
      have hs := csRawSum_val hlt
      have hc := csRawCarry_val hlt
      constructor <;> intro e <;> [have := congrArg Fin.val e; have := congrArg Fin.val e] <;> omega
    rw [show z' w = z w from csApplyList_other z hout]
  have hstep_col : ∀ b : Fin (hcEll n),
      ((csStep n st).cols b).countP z' =
        (takeTriples (st.cols b)).2.countP z +
        ((ann.filter fun p => decide (p.1.1 = b)).map fun p => if z' (csRawSum n p.2) then 1 else 0).sum +
        ((ann.filter fun p => decide (p.1.1.1 + 1 = b.1)).map fun p =>
          if z' (csRawCarry n p.2) then 1 else 0).sum := by
    intro b
    dsimp only [csStep]
    rw [List.countP_append, List.countP_append, hrem_count b]
    simp_rw [countP_eq_sum_map, List.map_map]
    rfl
  have hsum_cols : (∑ b : Fin (hcEll n), 2 ^ b.1 * ((csStep n st).cols b).countP z') =
      (∑ b : Fin (hcEll n), 2 ^ b.1 * (takeTriples (st.cols b)).2.countP z) +
      (∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1 = b)).map fun p =>
        if z' (csRawSum n p.2) then 1 else 0).sum) +
      (∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1.1 + 1 = b.1)).map fun p =>
        if z' (csRawCarry n p.2) then 1 else 0).sum) := by
    simp_rw [hstep_col, mul_add, Finset.sum_add_distrib]
  have hpart1 : (∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1 = b)).map fun p =>
      if z' (csRawSum n p.2) then 1 else 0).sum) =
      (ann.map fun p => 2 ^ p.1.1.1 * (if z' (csRawSum n p.2) then 1 else 0)).sum :=
    sum_filter_eq_map ann (fun p => p.1.1) (fun p => if z' (csRawSum n p.2) then 1 else 0)
  have hpart2 : (∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1.1 + 1 = b.1)).map fun p =>
      if z' (csRawCarry n p.2) then 1 else 0).sum) +
      2 ^ hcEll n * ((ann.filter fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p =>
        if z' (csRawCarry n p.2) then 1 else 0).sum =
      (ann.map fun p => 2 ^ p.1.1.1 * 2 * (if z' (csRawCarry n p.2) then 1 else 0)).sum :=
    sum_filter_succ_eq_map ann (fun p => p.1.1) (fun p => if z' (csRawCarry n p.2) then 1 else 0)
  have hadd_ann : (ann.map fun p => 2 ^ p.1.1.1 * (if z' (csRawSum n p.2) then 1 else 0)).sum +
      (ann.map fun p => 2 ^ p.1.1.1 * 2 * (if z' (csRawCarry n p.2) then 1 else 0)).sum =
      ((csAllTriples n st).map fun q => 2 ^ q.1.1 * ((if z q.2.1 then 1 else 0) +
        (if z q.2.2.1 then 1 else 0) + (if z q.2.2.2 then 1 else 0))).sum := by
    have hmap_sum : ∀ (L : List _), (∀ p ∈ L, p ∈ ann) →
        (L.map fun p => 2 ^ p.1.1.1 * (if z' (csRawSum n p.2) then 1 else 0)).sum +
        (L.map fun p => 2 ^ p.1.1.1 * 2 * (if z' (csRawCarry n p.2) then 1 else 0)).sum =
        (L.map fun p => 2 ^ p.1.1.1 * ((if z p.1.2.1 then 1 else 0) +
          (if z p.1.2.2.1 then 1 else 0) + (if z p.1.2.2.2 then 1 else 0))).sum := by
      intro L hL
      induction L with
      | nil => simp
      | cons p rest ih =>
        have hp := hL p List.mem_cons_self
        have hs : z' (csRawSum n p.2) = xor (xor (z p.1.2.1) (z p.1.2.2.1)) (z p.1.2.2.2) :=
          csApplyList_sum z hann_pw hann_lt hp
        have hc : z' (csRawCarry n p.2) =
            xor (z p.1.2.1 && z p.1.2.2.1) (xor (z p.1.2.1) (z p.1.2.2.1) && z p.1.2.2.2) :=
          csApplyList_carry z hann_pw hann_lt hp
        have harith := bool_fullAdder_arith (z p.1.2.1) (z p.1.2.2.1) (z p.1.2.2.2)
        simp only [List.map_cons, List.sum_cons]
        have h_ih := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
        rw [add_add_add_comm, h_ih, hs, hc]
        rw [mul_assoc (2 ^ p.1.1.1) 2, ← mul_add, harith]
    rw [hmap_sum ann (fun _ h => h), ← numberItems_map_fst st.nextPair (csAllTriples n st),
      List.map_map]
    rfl
  have htri_sum : ((csAllTriples n st).map fun q => 2 ^ q.1.1 * ((if z q.2.1 then 1 else 0) +
      (if z q.2.2.1 then 1 else 0) + (if z q.2.2.2 then 1 else 0))).sum =
      ∑ b : Fin (hcEll n), 2 ^ b.1 * ((takeTriples (st.cols b)).1.map fun t =>
        (if z t.1 then 1 else 0) + (if z t.2.1 then 1 else 0) + (if z t.2.2 then 1 else 0)).sum := by
    dsimp only [csAllTriples]
    rw [sum_map_flatMap]
    have hinner : ∀ b : Fin (hcEll n),
        (((takeTriples (st.cols b)).1.map fun t => (b, t)).map fun q =>
          2 ^ q.1.1 * ((if z q.2.1 then 1 else 0) + (if z q.2.2.1 then 1 else 0) +
            (if z q.2.2.2 then 1 else 0))).sum =
        2 ^ b.1 * ((takeTriples (st.cols b)).1.map fun t =>
          (if z t.1 then 1 else 0) + (if z t.2.1 then 1 else 0) + (if z t.2.2 then 1 else 0)).sum := by
      intro b
      rw [List.map_map]
      induction (takeTriples (st.cols b)).1 with
      | nil => simp
      | cons t rest ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp_def] at ih ⊢
        rw [ih]; ring
    have hfun : (List.finRange (hcEll n)).map (fun b => (((takeTriples (st.cols b)).1.map fun t => (b, t)).map fun q =>
          2 ^ q.1.1 * ((if z q.2.1 then 1 else 0) + (if z q.2.2.1 then 1 else 0) +
            (if z q.2.2.2 then 1 else 0))).sum) =
        (List.finRange (hcEll n)).map fun b => 2 ^ b.1 * ((takeTriples (st.cols b)).1.map fun t =>
          (if z t.1 then 1 else 0) + (if z t.2.1 then 1 else 0) + (if z t.2.2 then 1 else 0)).sum := by
      exact List.map_congr_left fun b _ => hinner b
    change ((List.finRange (hcEll n)).map (fun x => (List.map _ _).sum)).sum = _
    rw [hfun, sum_map_finRange]
  have hcombine : (∑ b : Fin (hcEll n), 2 ^ b.1 * (takeTriples (st.cols b)).2.countP z) +
      (∑ b : Fin (hcEll n), 2 ^ b.1 * ((takeTriples (st.cols b)).1.map fun t =>
        (if z t.1 then 1 else 0) + (if z t.2.1 then 1 else 0) + (if z t.2.2 then 1 else 0)).sum) =
      ∑ b : Fin (hcEll n), 2 ^ b.1 * (st.cols b).countP z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_add, add_comm ((takeTriples (st.cols b)).2.countP z), ← takeTriples_countP]
  dsimp only [z', ann] at hsum_cols hpart1 hpart2 hadd_ann ⊢
  calc (∑ b : Fin (hcEll n), 2 ^ b.1 * ((csStep n st).cols b).countP z') +
        2 ^ hcEll n * (((numberItems st.nextPair (csAllTriples n st)).filter
          fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p => if z' (csRawCarry n p.2) then 1 else 0).sum
      = (∑ b : Fin (hcEll n), 2 ^ b.1 * (takeTriples (st.cols b)).2.countP z) +
          ((∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1 = b)).map fun p =>
            if z' (csRawSum n p.2) then 1 else 0).sum) +
          ((∑ b : Fin (hcEll n), 2 ^ b.1 * ((ann.filter fun p => decide (p.1.1.1 + 1 = b.1)).map fun p =>
            if z' (csRawCarry n p.2) then 1 else 0).sum) +
          2 ^ hcEll n * ((ann.filter fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p =>
            if z' (csRawCarry n p.2) then 1 else 0).sum)) := by
        rw [hsum_cols]; abel
    _ = (∑ b : Fin (hcEll n), 2 ^ b.1 * (takeTriples (st.cols b)).2.countP z) +
          ((ann.map fun p => 2 ^ p.1.1.1 * (if z' (csRawSum n p.2) then 1 else 0)).sum +
           (ann.map fun p => 2 ^ p.1.1.1 * 2 * (if z' (csRawCarry n p.2) then 1 else 0)).sum) := by
        rw [hpart1, hpart2]
    _ = (∑ b : Fin (hcEll n), 2 ^ b.1 * (takeTriples (st.cols b)).2.countP z) +
          (∑ b : Fin (hcEll n), 2 ^ b.1 * ((takeTriples (st.cols b)).1.map fun t =>
            (if z t.1 then 1 else 0) + (if z t.2.1 then 1 else 0) + (if z t.2.2 then 1 else 0)).sum) := by
        rw [hadd_ann, htri_sum]
    _ = ∑ b : Fin (hcEll n), 2 ^ b.1 * (st.cols b).countP z := hcombine

private lemma act_csCircuitAt_ket (n : ℕ) (hn : 1 ≤ n) (z₀ : Qubits (hcWires n))
    (hclean : ∀ w : Fin (hcWires n), n + hcEll n ≤ w.1 → z₀ w = false) (r : ℕ) :
    ∃ x : Qubits (hcWires n),
      act (csCircuitAt n hn r).unitary (ket z₀) = ket x ∧
      (∀ w : Fin (hcWires n), w.1 < n + hcEll n → x w = z₀ w) ∧
      (∀ w : Fin (hcWires n), n + hcEll n + 2 * (csStateAt n r).nextPair ≤ w.1 → x w = false) ∧
      ∑ b : Fin (hcEll n), 2 ^ b.1 * ((csStateAt n r).cols b).countP x =
        (Finset.univ.filter fun i : Fin n => z₀ (hcQWire n i) = true).card := by
  have hell := hcEll_pos hn
  induction r with
  | zero =>
    refine ⟨z₀, by simp [csCircuitAt, LayeredCircuit.id_unitary, act_one], fun _ _ => rfl,
      fun w hw => hclean w (by simp [csStateAt, csInit] at hw; omega), ?_⟩
    dsimp only [csStateAt, csInit]
    let z0 : Fin (hcEll n) := ⟨0, hell⟩
    rw [Finset.sum_eq_single z0]
    · simp only [z0, pow_zero, one_mul, ↓reduceIte, List.countP_map]
      exact list_finRange_countP (fun i => z₀ (hcQWire n i))
    · intro b _ hb
      have hne : b.1 ≠ 0 := fun h => hb (Fin.ext h)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  | succ r ih =>
    rcases ih with ⟨x, hx_act, hx_low, hx_high, hx_sum⟩
    have hv := csValid_at n hn r
    have hround := act_csRoundCircuit_ket (csStateAt n r) hv x hx_high
    let x' := csApplyList n x (numberItems (csStateAt n r).nextPair (csAllTriples n (csStateAt n r)))
    refine ⟨x', ?_, ?_, ?_, ?_⟩
    · simp only [csCircuitAt, LayeredCircuit.seq_unitary, act_mul, hx_act, hround]
      rfl
    · intro w hw
      dsimp only [x']
      rw [csApplyList_preserve_low (csStateAt n r) hv x hw, hx_low w hw]
    · intro w hw
      change csApplyList n x (numberItems (csStateAt n r).nextPair (csAllTriples n (csStateAt n r))) w = false
      rw [csApplyList_preserve_high (csStateAt n r) hv x hw]
      apply hx_high
      dsimp only [csStateAt, csStep] at hw
      omega
    · have hws := csApplyList_weighted_sum (csStateAt n r) hv x
      dsimp only at hws
      have hcard_le : (Finset.univ.filter fun i : Fin n => z₀ (hcQWire n i) = true).card ≤ n := by
        calc (Finset.univ.filter fun i : Fin n => z₀ (hcQWire n i) = true).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
          _ = n := Fintype.card_fin n
      have hlt_pow := lt_two_pow_hcEll n
      have htop0 : (((numberItems (csStateAt n r).nextPair (csAllTriples n (csStateAt n r))).filter
          fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p =>
          if x' (csRawCarry n p.2) then 1 else 0).sum = 0 := by
        by_contra hne
        have h1 : 1 ≤ (((numberItems (csStateAt n r).nextPair (csAllTriples n (csStateAt n r))).filter
            fun p => decide (p.1.1.1 + 1 = hcEll n)).map fun p =>
            if x' (csRawCarry n p.2) then 1 else 0).sum := Nat.pos_of_ne_zero hne
        have hmul := Nat.mul_le_mul_left (2 ^ hcEll n) h1
        dsimp only [x'] at hmul
        omega
      dsimp only [x'] at htop0
      rw [htop0, mul_zero, add_zero] at hws
      exact hws.trans hx_sum

private noncomputable def rippleStep (n : ℕ) (b : Fin (hcEll n)) (ws : List (Fin (hcWires n))) :
    LayeredCircuit (hcWires n) :=
  let cin := hcCarryWire n b.1 (le_of_lt b.isLt)
  let s := hcSumWire n b
  let cout := hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt)
  match ws with
  | [] =>
    have hcs : cin ≠ s := by
      intro h; have := congrArg Fin.val h; dsimp [cin, s, hcCarryWire, hcSumWire] at this; omega
    cnotGate cin s hcs
  | [w1] =>
    if h1 : w1.1 < n ∨ (n + hcEll n ≤ w1.1 ∧ w1.1 < n + hcEll n + 2 * n) then
      have h1c : w1 ≠ cin := by
        intro h; have := congrArg Fin.val h; dsimp [cin, hcCarryWire] at this; omega
      have h1s : w1 ≠ s := by
        intro h; have := congrArg Fin.val h; dsimp [s, hcSumWire] at this; omega
      have h1co : w1 ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [cout, hcCarryWire] at this; omega
      have hcs : cin ≠ s := by
        intro h; have := congrArg Fin.val h; dsimp [cin, s, hcCarryWire, hcSumWire] at this; omega
      have hcco : cin ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [cin, cout, hcCarryWire] at this; omega
      halfAdder4 w1 cin s cout h1c h1s h1co hcs hcco
    else LayeredCircuit.id (hcWires n)
  | [w1, w2] =>
    if h12 : w1 ≠ w2 ∧ (w1.1 < n ∨ (n + hcEll n ≤ w1.1 ∧ w1.1 < n + hcEll n + 2 * n)) ∧
        (w2.1 < n ∨ (n + hcEll n ≤ w2.1 ∧ w2.1 < n + hcEll n + 2 * n)) then
      have h1s : w1 ≠ s := by
        intro h; have := congrArg Fin.val h; dsimp [s, hcSumWire] at this; omega
      have h1co : w1 ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [cout, hcCarryWire] at this; omega
      have h2s : w2 ≠ s := by
        intro h; have := congrArg Fin.val h; dsimp [s, hcSumWire] at this; omega
      have h2co : w2 ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [cout, hcCarryWire] at this; omega
      have hcs : cin ≠ s := by
        intro h; have := congrArg Fin.val h; dsimp [cin, s, hcCarryWire, hcSumWire] at this; omega
      have hcco : cin ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [cin, cout, hcCarryWire] at this; omega
      have hsco : s ≠ cout := by
        intro h; have := congrArg Fin.val h; dsimp [s, cout, hcSumWire, hcCarryWire] at this; omega
      fullAdder5 w1 w2 cin s cout h12.1 h1s h1co h2s h2co hcs hcco hsco
    else LayeredCircuit.id (hcWires n)
  | _ :: _ :: _ :: _ => LayeredCircuit.id (hcWires n)

private lemma rippleStep_usesOnly (n : ℕ) (b : Fin (hcEll n)) (ws : List (Fin (hcWires n))) :
    (rippleStep n b ws).UsesOnly (fwdSupport n) := by
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, rest⟩⟩⟩ <;> dsimp only [rippleStep]
  · refine (cnotGate_usesOnly _ _ _).mono fun w hw => ?_
    rw [mem_fwdSupport_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> [dsimp [hcCarryWire]; dsimp [hcSumWire]] <;> right <;> omega
  · split_ifs with h1
    · refine (halfAdder4_usesOnly _ _ _ _ _ _ _ _ _).mono fun w hw => ?_
      rw [mem_fwdSupport_iff]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · rcases h1 with h | h <;> [left; right] <;> omega
      · right; dsimp [hcCarryWire]; omega
      · right; dsimp [hcSumWire]; omega
      · right; dsimp [hcCarryWire]; omega
    · exact LayeredCircuit.id_usesOnly _
  · split_ifs with h12
    · refine (fullAdder5_usesOnly _ _ _ _ _ _ _ _ _ _ _ _ _).mono fun w hw => ?_
      rw [mem_fwdSupport_iff]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · rcases h12.2.1 with h | h <;> [left; right] <;> omega
      · rcases h12.2.2 with h | h <;> [left; right] <;> omega
      · right; dsimp [hcCarryWire]; omega
      · right; dsimp [hcSumWire]; omega
      · right; dsimp [hcCarryWire]; omega
    · exact LayeredCircuit.id_usesOnly _
  · exact LayeredCircuit.id_usesOnly _

private lemma rippleStep_size (n : ℕ) (b : Fin (hcEll n)) (ws : List (Fin (hcWires n))) :
    (rippleStep n b ws).size ≤ 13 := by
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, rest⟩⟩⟩ <;> dsimp only [rippleStep]
  · simp
  · split_ifs <;> simp
  · split_ifs <;> simp
  · simp

private lemma rippleStep_depth (n : ℕ) (b : Fin (hcEll n)) (ws : List (Fin (hcWires n))) :
    (rippleStep n b ws).depth ≤ 13 := by
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, rest⟩⟩⟩ <;> dsimp only [rippleStep]
  · simp
  · split_ifs <;> simp
  · split_ifs <;> simp
  · simp

private lemma act_rippleStep_ket (n : ℕ) (b : Fin (hcEll n)) (ws : List (Fin (hcWires n)))
    (hlen : ws.length ≤ 2) (hnd : ws.Nodup)
    (hbnd : ∀ w ∈ ws, w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * n))
    (x : Qubits (hcWires n))
    (hxs : x (hcSumWire n b) = false)
    (hxc : x (hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt)) = false) :
    ∃ sVal cVal : Bool,
      act (rippleStep n b ws).unitary (ket x) =
        ket (fun w =>
          if w = hcSumWire n b then sVal
          else if w = hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) then cVal
          else x w) ∧
      (if sVal then 1 else 0) + 2 * (if cVal then 1 else 0) =
        (if x (hcCarryWire n b.1 (le_of_lt b.isLt)) then 1 else 0) + ws.countP x := by
  let cin := hcCarryWire n b.1 (le_of_lt b.isLt)
  let s := hcSumWire n b
  let cout := hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt)
  have hsc : s ≠ cout := by
    intro h; have := congrArg Fin.val h; dsimp [s, cout, hcSumWire, hcCarryWire] at this; omega
  rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, rest⟩⟩⟩
  · refine ⟨x cin, false, ?_, by simp [cin]⟩
    dsimp only [rippleStep]
    rw [act_cnotGate_ket]
    congr 1
    funext w
    by_cases hws : w = s
    · subst hws; simp [s, cin, hxs]
    · by_cases hwc : w = cout
      · subst hwc; rw [Function.update_of_ne hsc.symm, if_neg hws, if_pos rfl, hxc]
      · rw [Function.update_of_ne hws, if_neg hws, if_neg hwc]
  · have h1 := hbnd w1 List.mem_cons_self
    refine ⟨xor (x w1) (x cin), x w1 && x cin, ?_, ?_⟩
    · dsimp only [rippleStep]
      rw [dif_pos h1, act_halfAdder4_ket _ _ _ _ _ _ _ _ _ hsc x hxs hxc]
    · have har := bool_halfAdder_arith (x w1) (x cin)
      have hcnt : [w1].countP x = if x w1 then 1 else 0 := by
        cases hx : x w1 <;> simp [hx]
      dsimp only [cin] at har ⊢
      rw [hcnt]
      omega
  · have h1 := hbnd w1 (by simp)
    have h2 := hbnd w2 (by simp)
    rw [List.nodup_cons] at hnd
    have h12_ne : w1 ≠ w2 := fun h => hnd.1 (by simp [h])
    have h12 : w1 ≠ w2 ∧ (w1.1 < n ∨ (n + hcEll n ≤ w1.1 ∧ w1.1 < n + hcEll n + 2 * n)) ∧
        (w2.1 < n ∨ (n + hcEll n ≤ w2.1 ∧ w2.1 < n + hcEll n + 2 * n)) := ⟨h12_ne, h1, h2⟩
    refine ⟨xor (xor (x w1) (x w2)) (x cin),
      xor (x w1 && x w2) (xor (x w1) (x w2) && x cin), ?_, ?_⟩
    · dsimp only [rippleStep]
      rw [dif_pos h12, act_fullAdder5_ket _ _ _ _ _ _ _ _ _ _ _ _ _ x hxs hxc]
    · have har := bool_fullAdder_arith (x w1) (x w2) (x cin)
      have hcnt : [w1, w2].countP x = (if x w1 then 1 else 0) + (if x w2 then 1 else 0) := by
        cases hx1 : x w1 <;> cases hx2 : x w2 <;> simp [hx1, hx2]
      dsimp only [cin] at har ⊢
      rw [hcnt]
      omega
  · simp at hlen

private noncomputable def ripplePrefix (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n))) :
    (k : ℕ) → k ≤ hcEll n → LayeredCircuit (hcWires n)
  | 0, _ => LayeredCircuit.id (hcWires n)
  | k + 1, hk => (ripplePrefix n cols k (by omega)).seq (rippleStep n ⟨k, hk⟩ (cols ⟨k, hk⟩))

private lemma ripplePrefix_usesOnly (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n)))
    (k : ℕ) (hk : k ≤ hcEll n) :
    (ripplePrefix n cols k hk).UsesOnly (fwdSupport n) := by
  induction k with
  | zero => exact LayeredCircuit.id_usesOnly _
  | succ k ih =>
    exact LayeredCircuit.seq_usesOnly (ih (by omega)) (rippleStep_usesOnly n ⟨k, hk⟩ _)

private lemma ripplePrefix_size (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n)))
    (k : ℕ) (hk : k ≤ hcEll n) :
    (ripplePrefix n cols k hk).size ≤ 13 * k := by
  induction k with
  | zero => simp [ripplePrefix]
  | succ k ih =>
    simp only [ripplePrefix, LayeredCircuit.seq_size]
    have h1 := ih (by omega)
    have h2 := rippleStep_size n ⟨k, hk⟩ (cols ⟨k, hk⟩)
    omega

private lemma ripplePrefix_depth (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n)))
    (k : ℕ) (hk : k ≤ hcEll n) :
    (ripplePrefix n cols k hk).depth ≤ 13 * k := by
  induction k with
  | zero => simp [ripplePrefix]
  | succ k ih =>
    simp only [ripplePrefix, LayeredCircuit.seq_depth]
    have h1 := ih (by omega)
    have h2 := rippleStep_depth n ⟨k, hk⟩ (cols ⟨k, hk⟩)
    omega

private lemma sum_fin_lt_succ {m : ℕ} (k : ℕ) (hk : k + 1 ≤ m) (f : Fin m → ℕ) :
    (∑ j : Fin m, if j.1 < k + 1 then f j else 0) =
      (∑ j : Fin m, if j.1 < k then f j else 0) + f ⟨k, hk⟩ := by
  have hstep : ∀ j : Fin m,
      (if j.1 < k + 1 then f j else 0) =
        (if j.1 < k then f j else 0) + (if j = ⟨k, hk⟩ then f ⟨k, hk⟩ else 0) := by
    intro j
    by_cases hj : j.1 < k
    · have hne : j ≠ ⟨k, hk⟩ := fun h => by
        have := congrArg Fin.val h; dsimp at this; omega
      rw [if_pos (by omega), if_pos hj, if_neg hne, add_zero]
    · by_cases heq : j = ⟨k, hk⟩
      · subst heq; rw [if_pos (by simp), if_neg hj, if_pos rfl, zero_add]
      · have hne : j.1 ≠ k := fun h => heq (Fin.ext h)
        rw [if_neg (by omega), if_neg hj, if_neg heq]
  simp only [hstep, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private lemma act_ripplePrefix_ket (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n)))
    (hlen : ∀ b : Fin (hcEll n), (cols b).length ≤ 2)
    (hnd : ∀ b : Fin (hcEll n), (cols b).Nodup)
    (hbnd : ∀ b : Fin (hcEll n), ∀ w ∈ cols b,
      w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * n))
    (x₀ : Qubits (hcWires n))
    (hclean_sum : ∀ b : Fin (hcEll n), x₀ (hcSumWire n b) = false)
    (hclean_carry : ∀ c (hc : c ≤ hcEll n), x₀ (hcCarryWire n c hc) = false)
    (k : ℕ) (hk : k ≤ hcEll n) :
    ∃ x : Qubits (hcWires n),
      act (ripplePrefix n cols k hk).unitary (ket x₀) = ket x ∧
      (∀ w : Fin (hcWires n), w.1 < n + hcEll n + 2 * n → x w = x₀ w) ∧
      (∀ b : Fin (hcEll n), k ≤ b.1 → x (hcSumWire n b) = false) ∧
      (∀ c (hc : c ≤ hcEll n), k < c → x (hcCarryWire n c hc) = false) ∧
      (∑ j : Fin (hcEll n), if j.1 < k then 2 ^ j.1 * (if x (hcSumWire n j) then 1 else 0) else 0) +
        2 ^ k * (if x (hcCarryWire n k hk) then 1 else 0) =
        ∑ j : Fin (hcEll n), if j.1 < k then 2 ^ j.1 * (cols j).countP x₀ else 0 := by
  induction k with
  | zero =>
    refine ⟨x₀, by simp [ripplePrefix, LayeredCircuit.id_unitary, act_one], fun _ _ => rfl,
      fun b _ => hclean_sum b, fun c hc _ => hclean_carry c hc, ?_⟩
    simp [hclean_carry 0 (Nat.zero_le _)]
  | succ k ih =>
    rcases ih (by omega) with ⟨x, hx_act, hx_low, hx_sum, hx_carry, hx_val⟩
    let b : Fin (hcEll n) := ⟨k, hk⟩
    have hxs : x (hcSumWire n b) = false := hx_sum b le_rfl
    have hxc : x (hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt)) = false :=
      hx_carry (k + 1) hk (Nat.lt_succ_self k)
    rcases act_rippleStep_ket n b (cols b) (hlen b) (hnd b) (hbnd b) x hxs hxc with
      ⟨sVal, cVal, hstep_act, hstep_arith⟩
    let x' : Qubits (hcWires n) := fun w =>
      if w = hcSumWire n b then sVal
      else if w = hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) then cVal
      else x w
    have hcount_eq : (cols b).countP x = (cols b).countP x₀ := by
      refine List.countP_congr fun w hw => ?_
      have heq : x w = x₀ w := by
        rcases hbnd b w hw with h | h <;> exact hx_low w (by omega)
      simp [heq]
    refine ⟨x', ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ripplePrefix, LayeredCircuit.seq_unitary, act_mul, hx_act]
      exact hstep_act
    · intro w hw
      have hns : w ≠ hcSumWire n b := fun e => by
        have := congrArg Fin.val e; dsimp [hcSumWire] at this; omega
      have hnc : w ≠ hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) := fun e => by
        have := congrArg Fin.val e; dsimp [hcCarryWire] at this; omega
      dsimp only [x']
      rw [if_neg hns, if_neg hnc, hx_low w hw]
    · intro j hj
      have hne_s : hcSumWire n j ≠ hcSumWire n b := fun e => by
        have := congrArg Fin.val e; dsimp [hcSumWire, b] at this; omega
      have hne_c : hcSumWire n j ≠ hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) := fun e => by
        have := congrArg Fin.val e; dsimp [hcSumWire, hcCarryWire] at this; omega
      dsimp only [x']
      rw [if_neg hne_s, if_neg hne_c]
      exact hx_sum j (by omega)
    · intro c hc hgt
      have hne_s : hcCarryWire n c hc ≠ hcSumWire n b := fun e => by
        have := congrArg Fin.val e; dsimp [hcCarryWire, hcSumWire] at this; omega
      have hne_c : hcCarryWire n c hc ≠ hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) := fun e => by
        have := congrArg Fin.val e; dsimp [hcCarryWire, b] at this; omega
      dsimp only [x']
      rw [if_neg hne_s, if_neg hne_c]
      exact hx_carry c hc (by omega)
    · have hsum_x' : (∑ j : Fin (hcEll n),
          if j.1 < k + 1 then 2 ^ j.1 * (if x' (hcSumWire n j) then 1 else 0) else 0) =
          (∑ j : Fin (hcEll n),
            if j.1 < k then 2 ^ j.1 * (if x (hcSumWire n j) then 1 else 0) else 0) +
            2 ^ k * (if sVal then 1 else 0) := by
        rw [sum_fin_lt_succ k hk (fun j => 2 ^ j.1 * (if x' (hcSumWire n j) then 1 else 0))]
        have hleft : (∑ j : Fin (hcEll n),
            if j.1 < k then 2 ^ j.1 * (if x' (hcSumWire n j) then 1 else 0) else 0) =
            ∑ j : Fin (hcEll n),
              if j.1 < k then 2 ^ j.1 * (if x (hcSumWire n j) then 1 else 0) else 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j.1 < k
          · rw [if_pos hj, if_pos hj]
            have hne_s : hcSumWire n j ≠ hcSumWire n b := fun e => by
              have := congrArg Fin.val e; dsimp [hcSumWire, b] at this; omega
            have hne_c : hcSumWire n j ≠ hcCarryWire n (b.1 + 1) (Nat.succ_le_of_lt b.isLt) := fun e => by
              have := congrArg Fin.val e; dsimp [hcSumWire, hcCarryWire] at this; omega
            have heq : x' (hcSumWire n j) = x (hcSumWire n j) := by
              dsimp only [x']; rw [if_neg hne_s, if_neg hne_c]
            simp only [heq]
          · rw [if_neg hj, if_neg hj]
        have hright : x' (hcSumWire n b) = sVal := by
          dsimp only [x']; rw [if_pos rfl]
        change _ + 2 ^ b.1 * (if x' (hcSumWire n b) then 1 else 0) = _
        rw [hleft, hright]
      have hcarry_x' : x' (hcCarryWire n (k + 1) hk) = cVal := by
        have hne_s : hcCarryWire n (k + 1) hk ≠ hcSumWire n b := fun e => by
          have := congrArg Fin.val e; dsimp [hcCarryWire, hcSumWire] at this; omega
        dsimp only [x']
        rw [if_neg hne_s, if_pos rfl]
      rw [hsum_x', hcarry_x', sum_fin_lt_succ k hk (fun j => 2 ^ j.1 * (cols j).countP x₀)]
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      rw [hpow]
      have har' : (if sVal then 1 else 0) + 2 * (if cVal then 1 else 0) =
          (if x (hcCarryWire n k (by omega)) then 1 else 0) + (cols b).countP x₀ := by
        rw [← hcount_eq]; exact hstep_arith
      dsimp only [b] at har'
      have hmk : (⟨k, hk⟩ : Fin (hcEll n)).1 = k := rfl
      rw [hmk, add_assoc, mul_assoc (2 ^ k) 2, ← mul_add, har', mul_add, ← add_assoc, hx_val]

private noncomputable def rippleCarry (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n))) :
    LayeredCircuit (hcWires n) :=
  ripplePrefix n cols (hcEll n) le_rfl

private lemma rippleCarry_usesOnly (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n))) :
    (rippleCarry n cols).UsesOnly (fwdSupport n) :=
  ripplePrefix_usesOnly n cols (hcEll n) le_rfl

private lemma rippleCarry_size (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n))) :
    (rippleCarry n cols).size ≤ 13 * hcEll n :=
  ripplePrefix_size n cols (hcEll n) le_rfl

private lemma rippleCarry_depth (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n))) :
    (rippleCarry n cols).depth ≤ 13 * hcEll n :=
  ripplePrefix_depth n cols (hcEll n) le_rfl

private lemma act_rippleCarry_ket (n : ℕ) (cols : Fin (hcEll n) → List (Fin (hcWires n)))
    (hlen : ∀ b : Fin (hcEll n), (cols b).length ≤ 2)
    (hnd : ∀ b : Fin (hcEll n), (cols b).Nodup)
    (hbnd : ∀ b : Fin (hcEll n), ∀ w ∈ cols b,
      w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * n))
    (x₀ : Qubits (hcWires n))
    (hclean_sum : ∀ b : Fin (hcEll n), x₀ (hcSumWire n b) = false)
    (hclean_carry : ∀ c (hc : c ≤ hcEll n), x₀ (hcCarryWire n c hc) = false)
    (hw : ℕ) (hsum : ∑ b : Fin (hcEll n), 2 ^ b.1 * (cols b).countP x₀ = hw)
    (hhw_lt : hw < 2 ^ hcEll n) :
    ∃ x : Qubits (hcWires n),
      act (rippleCarry n cols).unitary (ket x₀) = ket x ∧
      (∀ w : Fin (hcWires n), w.1 < n + hcEll n + 2 * n → x w = x₀ w) ∧
      ∀ b : Fin (hcEll n), x (hcSumWire n b) = natToBitsLSB (hcEll n) hw b := by
  rcases act_ripplePrefix_ket n cols hlen hnd hbnd x₀ hclean_sum hclean_carry (hcEll n) le_rfl with
    ⟨x, hx_act, hx_low, _, _, hx_val⟩
  have hlt1 : (∑ j : Fin (hcEll n), if j.1 < hcEll n then 2 ^ j.1 * (if x (hcSumWire n j) then 1 else 0) else 0) =
      bitsToNatLSB (fun j : Fin (hcEll n) => x (hcSumWire n j)) := by
    dsimp only [bitsToNatLSB]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos j.isLt]
    split_ifs <;> simp
  have hlt2 : (∑ j : Fin (hcEll n), if j.1 < hcEll n then 2 ^ j.1 * (cols j).countP x₀ else 0) = hw := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => if_pos j.isLt
  rw [hlt1, hlt2] at hx_val
  have hcarry0 : (if x (hcCarryWire n (hcEll n) le_rfl) then 1 else 0) = 0 := by
    by_contra hne
    have h1 : 1 ≤ if x (hcCarryWire n (hcEll n) le_rfl) then 1 else 0 := Nat.pos_of_ne_zero hne
    have hmul := Nat.mul_le_mul_left (2 ^ hcEll n) h1
    omega
  rw [hcarry0, mul_zero, add_zero] at hx_val
  refine ⟨x, hx_act, hx_low, fun b => ?_⟩
  have hbits := natToBitsLSB_bitsToNatLSB (fun j : Fin (hcEll n) => x (hcSumWire n j))
  rw [hx_val] at hbits
  exact (congrFun hbits b).symm

private def copyWireSet (n : ℕ) (b : Fin (hcEll n)) : Finset (Fin (hcWires n)) :=
  {hcSumWire n b, hcOutWire n b}

private noncomputable def copyItems (n : ℕ) :
    List (LayeredCircuit (hcWires n) × Finset (Fin (hcWires n))) :=
  (List.finRange (hcEll n)).map fun b =>
    (cnotGate (hcSumWire n b) (hcOutWire n b) (by
      intro h; have := congrArg Fin.val h; dsimp [hcSumWire, hcOutWire] at this; omega),
     copyWireSet n b)

private lemma copyItems_usesOnly (n : ℕ) : ∀ p ∈ copyItems n, p.1.UsesOnly p.2 := by
  intro p hp
  simp only [copyItems, List.mem_map] at hp
  rcases hp with ⟨b, _, rfl⟩
  exact cnotGate_usesOnly _ _ _

private lemma copyItems_pairwise (n : ℕ) :
    (copyItems n).Pairwise fun p q => Disjoint p.2 q.2 := by
  dsimp only [copyItems]
  rw [List.pairwise_map]
  refine (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange (hcEll n))).imp fun {a b} hab => ?_
  rw [Finset.disjoint_left]
  intro w ha hb
  simp only [copyWireSet, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with h | h <;>
    [have := congrArg Fin.val h; have := congrArg Fin.val h;
     have := congrArg Fin.val h; have := congrArg Fin.val h] <;>
    dsimp [hcSumWire, hcOutWire] at * <;> omega

private noncomputable def copyLayer (n : ℕ) : LayeredCircuit (hcWires n) :=
  (parMergeAux (copyItems n) (copyItems_usesOnly n) (copyItems_pairwise n)).1

private lemma copyLayer_size (n : ℕ) : (copyLayer n).size = hcEll n := by
  dsimp only [copyLayer]
  rw [(parMergeAux (copyItems n) (copyItems_usesOnly n) (copyItems_pairwise n)).2.2.1]
  have hsum : ∀ xs : List (Fin (hcEll n)),
      ((xs.map fun b => (cnotGate (hcSumWire n b) (hcOutWire n b) (by
        intro h; have := congrArg Fin.val h; dsimp [hcSumWire, hcOutWire] at this; omega),
        copyWireSet n b)).map fun p => p.1.size).sum = xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons, cnotGate_size, List.length_cons]
      rw [ih]; omega
  dsimp only [copyItems]
  rw [hsum (List.finRange (hcEll n)), List.length_finRange]

private lemma copyLayer_depth (n : ℕ) : (copyLayer n).depth ≤ 1 := by
  dsimp only [copyLayer]
  refine le_trans (parMergeAux (copyItems n) (copyItems_usesOnly n) (copyItems_pairwise n)).2.2.2 ?_
  refine foldr_max_le (copyItems n) 1 fun p hp => ?_
  simp only [copyItems, List.mem_map] at hp
  rcases hp with ⟨b, _, rfl⟩
  simp

private lemma act_copyLayer_ket (n : ℕ) (z : Qubits (hcWires n)) :
    act (copyLayer n).unitary (ket z) =
      ket (fun w =>
        if h : n ≤ w.1 ∧ w.1 < n + hcEll n then
          xor (z w) (z (hcSumWire n ⟨w.1 - n, by omega⟩))
        else z w) := by
  let z_next : Qubits (hcWires n) := fun w =>
    if h : n ≤ w.1 ∧ w.1 < n + hcEll n then
      xor (z w) (z (hcSumWire n ⟨w.1 - n, by omega⟩))
    else z w
  dsimp only [copyLayer]
  have hact : ∀ p ∈ copyItems n, ∃ x' : Qubits (hcWires n),
      act p.1.unitary (ket z) = ket x' ∧ ∀ w ∈ p.2, x' w = z_next w := by
    intro p hp
    simp only [copyItems, List.mem_map] at hp
    rcases hp with ⟨b, _, rfl⟩
    refine ⟨_, act_cnotGate_ket _ _ _ z, fun w hw => ?_⟩
    simp only [copyWireSet, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · have hne : hcSumWire n b ≠ hcOutWire n b := by
        intro h; have := congrArg Fin.val h; dsimp [hcSumWire, hcOutWire] at this; omega
      have hnot : ¬ (n ≤ (hcSumWire n b).1 ∧ (hcSumWire n b).1 < n + hcEll n) := by
        dsimp [hcSumWire]; omega
      rw [Function.update_of_ne hne]
      dsimp only [z_next]
      rw [dif_neg hnot]
    · have hin : n ≤ (hcOutWire n b).1 ∧ (hcOutWire n b).1 < n + hcEll n := by
        dsimp [hcOutWire]; have := b.isLt; omega
      have hfin : (⟨(hcOutWire n b).1 - n, by omega⟩ : Fin (hcEll n)) = b := by
        ext; dsimp [hcOutWire]; omega
      rw [Function.update_self]
      dsimp only [z_next]
      rw [dif_pos hin, hfin]
  rw [act_parMergeAux_ket (copyItems n) (copyItems_usesOnly n) (copyItems_pairwise n) z z_next hact]
  congr 1
  funext w
  by_cases hw : w ∈ (copyItems n).foldr (fun p acc => p.2 ∪ acc) ∅
  · rw [if_pos hw]
  · rw [if_neg hw]
    split_ifs with h
    · exfalso; apply hw
      let b : Fin (hcEll n) := ⟨w.1 - n, by omega⟩
      have hw_eq : w = hcOutWire n b := Fin.ext (by dsimp [hcOutWire, b]; omega)
      have hp_mem : (cnotGate (hcSumWire n b) (hcOutWire n b) (by
          intro h; have := congrArg Fin.val h; dsimp [hcSumWire, hcOutWire] at this; omega),
          copyWireSet n b) ∈ copyItems n := by
        simp only [copyItems, List.mem_map]
        exact ⟨b, List.mem_finRange b, rfl⟩
      exact mem_foldr_union_of_mem hp_mem (by simp [copyWireSet, hw_eq])
    · rfl

def hammingAddFn (n : ℕ) (z : Qubits (n + hcEll n)) : Qubits (n + hcEll n) :=
  let hw : ℕ := (Finset.univ.filter fun i : Fin n => z (Fin.castAdd (hcEll n) i) = true).card
  fun k =>
    if hk : k.1 < n then z k
    else xor (z k) (natToBitsLSB (hcEll n) hw ⟨k.1 - n, by have := k.isLt; omega⟩)

private noncomputable def hammingFwd (n : ℕ) (hn : 1 ≤ n) : LayeredCircuit (hcWires n) :=
  (csCircuitAt n hn (3 * hcEll n)).seq (rippleCarry n (csStateAt n (3 * hcEll n)).cols)

private lemma hammingFwd_usesOnly (n : ℕ) (hn : 1 ≤ n) :
    (hammingFwd n hn).UsesOnly (fwdSupport n) :=
  LayeredCircuit.seq_usesOnly (csCircuitAt_usesOnly n hn (3 * hcEll n)) (rippleCarry_usesOnly n _)

noncomputable def hammingCounter (n : ℕ) : LayeredCircuit (n + hcEll n + hammingAnc n) :=
  if hn : 1 ≤ n then
    let fwd := hammingFwd n hn
    fwd.seq ((copyLayer n).seq fwd.adj)
  else
    LayeredCircuit.id (hcWires n)

lemma hammingCounter_size_tight (n : ℕ) :
    (hammingCounter n).size ≤ 26 * n + 27 * hcEll n := by
  unfold hammingCounter
  split_ifs with hn
  · simp only [hammingFwd, LayeredCircuit.seq_size, LayeredCircuit.adj_size, copyLayer_size]
    have h1 := csCircuitAt_size_le n hn (3 * hcEll n)
    have h2 := rippleCarry_size n (csStateAt n (3 * hcEll n)).cols
    omega
  · simp

lemma hammingCounter_size (n : ℕ) : (hammingCounter n).size ≤ 53 * n := by
  have h1 := hammingCounter_size_tight n
  have h2 := hcEll_le_self n
  omega

lemma hammingCounter_depth (n : ℕ) : (hammingCounter n).depth ≤ 104 * hcEll n + 1 := by
  unfold hammingCounter
  split_ifs with hn
  · simp only [hammingFwd, LayeredCircuit.seq_depth, LayeredCircuit.adj_depth]
    have h1 := csCircuitAt_depth n hn (3 * hcEll n)
    have h2 := rippleCarry_depth n (csStateAt n (3 * hcEll n)).cols
    have h3 := copyLayer_depth n
    omega
  · simp

lemma hammingCounter_depth_real (n : ℕ) (hn : 2 ≤ n) :
    ((hammingCounter n).depth : ℝ) ≤ (209 / Real.log 2) * Real.log n := by
  have h1 : 1 ≤ n := by omega
  have hd : ((hammingCounter n).depth : ℝ) ≤ 104 * (hcEll n : ℝ) + 1 := by
    exact_mod_cast hammingCounter_depth n
  have hclog := clog2_succ_le_real_log h1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ge : 1 ≤ Real.log n / Real.log 2 := by
    rw [one_le_div hlog2_pos]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  calc ((hammingCounter n).depth : ℝ)
      ≤ 104 * (Real.log n / Real.log 2 + 1) + 1 := by linarith
    _ = 104 * (Real.log n / Real.log 2) + 105 := by ring
    _ ≤ 104 * (Real.log n / Real.log 2) + 105 * (Real.log n / Real.log 2) := by linarith
    _ = (209 / Real.log 2) * Real.log n := by ring

private lemma act_hammingCounter_ket_aux (n : ℕ) (z : Qubits (hcWires n))
    (hclean : ∀ j : Fin (hammingAnc n), z (Fin.natAdd (n + hcEll n) j) = false) :
    act (hammingCounter n).unitary (ket z) =
      ket (Fin.addCases
        (hammingAddFn n (fun i => z (Fin.castAdd (hammingAnc n) i)))
        (fun _ : Fin (hammingAnc n) => false)) := by
  have hclean_ge : ∀ w : Fin (hcWires n), n + hcEll n ≤ w.1 → z w = false := by
    intro w hw
    have hj : w = Fin.natAdd (n + hcEll n) ⟨w.1 - (n + hcEll n), by
        dsimp only [hcWires] at *; have := w.isLt; omega⟩ := by
      ext; simp; omega
    rw [hj]
    exact hclean _
  by_cases hn : 1 ≤ n
  · simp only [hammingCounter, dif_pos hn]
    let fwd := hammingFwd n hn
    let hw : ℕ := (Finset.univ.filter fun i : Fin n =>
      z (Fin.castAdd (hammingAnc n) (Fin.castAdd (hcEll n) i)) = true).card
    have hcs := act_csCircuitAt_ket n hn z hclean_ge (3 * hcEll n)
    rcases hcs with ⟨x_cs, hcs_act, hcs_low, hcs_high, hcs_sum⟩
    have hst_len := csStateAt_three_mul_clog n
    have hvF := csValid_at n hn (3 * hcEll n)
    have hst_nd : ∀ b : Fin (hcEll n), ((csStateAt n (3 * hcEll n)).cols b).Nodup :=
      fun b => (csValid_cols_nodup hvF b).1
    have hst_bnd : ∀ b : Fin (hcEll n), ∀ w ∈ (csStateAt n (3 * hcEll n)).cols b,
        w.1 < n ∨ (n + hcEll n ≤ w.1 ∧ w.1 < n + hcEll n + 2 * n) := by
      intro b w hw_m
      have hp := hvF.pair_le
      rcases hvF.wire_bound b w hw_m with h | h
      · left; exact h
      · right; omega
    have hclean_sum : ∀ b : Fin (hcEll n), x_cs (hcSumWire n b) = false := by
      intro b
      apply hcs_high
      have := hvF.pair_le
      dsimp [hcSumWire]; omega
    have hclean_carry : ∀ c (hc : c ≤ hcEll n), x_cs (hcCarryWire n c hc) = false := by
      intro c hc
      apply hcs_high
      have := hvF.pair_le
      dsimp [hcCarryWire]; omega
    have hhw_eq : (Finset.univ.filter fun i : Fin n => z (hcQWire n i) = true).card = hw := by
      rfl
    rw [hhw_eq] at hcs_sum
    have hrc := act_rippleCarry_ket n (csStateAt n (3 * hcEll n)).cols hst_len hst_nd hst_bnd x_cs
      hclean_sum hclean_carry hw hcs_sum (by
        have hle : hw ≤ n := by
          calc hw ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
            _ = n := Fintype.card_fin n
        exact Nat.lt_of_le_of_lt hle (lt_two_pow_hcEll n))
    rcases hrc with ⟨x_mid, hrc_act, hrc_low, hrc_sum⟩
    have hfwd_act : act fwd.unitary (ket z) = ket x_mid := by
      dsimp only [fwd, hammingFwd]
      rw [LayeredCircuit.seq_unitary, act_mul, hcs_act, hrc_act]
    have hx_mid_low : ∀ w : Fin (hcWires n), w.1 < n + hcEll n → x_mid w = z w := by
      intro w hw_lt
      rw [hrc_low w (by omega), hcs_low w hw_lt]
    have hcopy := act_copyLayer_ket n x_mid
    let x_copy : Qubits (hcWires n) := fun w =>
      if h : n ≤ w.1 ∧ w.1 < n + hcEll n then
        xor (x_mid w) (x_mid (hcSumWire n ⟨w.1 - n, by omega⟩))
      else x_mid w
    have hfwd_adj_xmid : act fwd.adj.unitary (ket x_mid) = ket z := by
      rw [← hfwd_act, ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp fwd.unitary_mem_unitaryGroup, act_one]
    have hagree : ∀ w ∈ fwdSupport n, x_copy w = x_mid w := by
      intro w hw_mem
      rw [mem_fwdSupport_iff] at hw_mem
      dsimp only [x_copy]
      rw [dif_neg (by omega)]
    have hfwd_adj_copy := act_ket_agree_on_usesOnly fwd.adj
      (LayeredCircuit.adj_usesOnly (hammingFwd_usesOnly n hn)) hfwd_adj_xmid hagree
    change act (fwd.seq ((copyLayer n).seq fwd.adj)).unitary (ket z) = _
    simp only [LayeredCircuit.seq_unitary, act_mul, hfwd_act]
    rw [hcopy, hfwd_adj_copy]
    congr 1
    funext w
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · simp only [Fin.addCases_left, hammingAddFn]
      by_cases hi : i.1 < n
      · have hmem : Fin.castAdd (hammingAnc n) i ∈ fwdSupport n := by
          rw [mem_fwdSupport_iff]; left; simp [hi]
        rw [if_pos hmem]
        simp [hi]
      · have hnot : Fin.castAdd (hammingAnc n) i ∉ fwdSupport n := by
          rw [mem_fwdSupport_iff]; simp only [Fin.val_castAdd]; omega
        rw [if_neg hnot]
        have hi_lt := i.isLt
        have hin : n ≤ (Fin.castAdd (hammingAnc n) i).1 ∧
            (Fin.castAdd (hammingAnc n) i).1 < n + hcEll n := by
          simp only [Fin.val_castAdd]; omega
        dsimp only [x_copy]
        rw [dif_pos hin, hx_mid_low _ (by simp)]
        have hb_eq : (⟨(Fin.castAdd (hammingAnc n) i).1 - n, by omega⟩ : Fin (hcEll n)) =
            ⟨i.1 - n, by omega⟩ := Fin.ext (by simp)
        rw [hb_eq, hrc_sum ⟨i.1 - n, by omega⟩]
        simp only [hi, ↓reduceDIte]
        rfl
    · have hmem : Fin.natAdd (n + hcEll n) j ∈ fwdSupport n := by
        rw [mem_fwdSupport_iff]; right; simp
      rw [if_pos hmem, Fin.addCases_right]
      exact hclean j
  · have hn0 : n = 0 := by omega
    subst hn0
    simp only [hammingCounter, dif_neg (by decide : ¬ 1 ≤ 0), LayeredCircuit.id_unitary, act_one]
    congr 1
    funext w
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · simp only [Fin.addCases_left, hammingAddFn]
      have hi_lt := i.isLt
      have h0 : hcEll 0 = 0 := by simp [hcEll]
      omega
    · rw [Fin.addCases_right]
      exact hclean j

theorem act_hammingCounter_zero_ket (n : ℕ) (x : Qubits n) :
    act (hammingCounter n).unitary
        (ket (Fin.addCases (Fin.addCases x (fun _ => false)) (fun _ : Fin (hammingAnc n) => false))) =
      ket (Fin.addCases
        (Fin.addCases x (natToBitsLSB (hcEll n) (Finset.univ.filter fun i : Fin n => x i = true).card))
        (fun _ : Fin (hammingAnc n) => false)) := by
  let z : Qubits (hcWires n) :=
    Fin.addCases (Fin.addCases x (fun _ : Fin (hcEll n) => false)) (fun _ : Fin (hammingAnc n) => false)
  have hclean : ∀ j : Fin (hammingAnc n), z (Fin.natAdd (n + hcEll n) j) = false := fun j => by
    simp only [z, Fin.addCases_right]
  rw [act_hammingCounter_ket_aux n z hclean]
  congr 1
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [Fin.addCases_left, hammingAddFn]
    have hw_eq : (Finset.univ.filter fun i' : Fin n =>
        z (Fin.castAdd (hammingAnc n) (Fin.castAdd (hcEll n) i')) = true).card =
        (Finset.univ.filter fun i' : Fin n => x i' = true).card := by
      congr 1; ext i'; simp only [z, Fin.addCases_left]
    refine Fin.addCases (fun q => ?_) (fun b => ?_) i
    · simp only [Fin.val_castAdd, q.isLt, ↓reduceDIte, z, Fin.addCases_left]
    · have hnot : ¬ (n + b.1 < n) := by omega
      simp only [Fin.val_natAdd, hnot, ↓reduceDIte, Fin.addCases_right]
      have hz_b : z (Fin.castAdd (hammingAnc n) (Fin.natAdd n b)) = false := by
        simp only [z, Fin.addCases_left, Fin.addCases_right]
      have hb_sub : (⟨n + b.1 - n, by have := (Fin.natAdd n b).isLt; omega⟩ : Fin (hcEll n)) = b :=
        Fin.ext (by dsimp; omega)
      rw [hz_b, hw_eq, hb_sub]
      simp only [Bool.false_xor]
  · simp only [Fin.addCases_right]

end Thm49Primitives



namespace Thm49Algebra

open QAlgorithms QuantumLTF.Majority

section KrawtchoukAndMod4

lemma krawtchouk_reflection (r t a : ℕ) (ha : a ≤ r) :
    krawtchouk r t (r - a) = (-1 : ℤ) ^ t * krawtchouk r t a := by
  unfold krawtchouk
  rw [← Finset.sum_range_reflect
    (fun j => (-1 : ℤ) ^ j * ((r - a).choose j : ℤ) * ((r - (r - a)).choose (t - j) : ℤ)) (t + 1)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hr : r - (r - a) = a := Nat.sub_sub_self ha
  have ht1 : t + 1 - 1 - j = t - j := by omega
  have ht2 : t - (t - j) = j := Nat.sub_sub_self hj'
  rw [hr, ht1, ht2]
  have hsq : (-1 : ℤ) ^ j * (-1 : ℤ) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hpow : (-1 : ℤ) ^ (t - j) = (-1 : ℤ) ^ t * (-1 : ℤ) ^ j := by
    calc (-1 : ℤ) ^ (t - j)
        = (-1 : ℤ) ^ (t - j) * ((-1 : ℤ) ^ j * (-1 : ℤ) ^ j) := by rw [hsq, mul_one]
      _ = ((-1 : ℤ) ^ (t - j) * (-1 : ℤ) ^ j) * (-1 : ℤ) ^ j := by ring
      _ = (-1 : ℤ) ^ t * (-1 : ℤ) ^ j := by rw [← pow_add, Nat.sub_add_cancel hj']
  rw [hpow]
  ring

private lemma choose_triple_symm (r t a j : ℕ) (ht : t ≤ r) (ha : a ≤ r) (hjt : j ≤ t) (hja : j ≤ a) :
    r.choose a * a.choose j * (r - a).choose (t - j) =
      r.choose t * t.choose j * (r - t).choose (a - j) := by
  have h1 : r.choose a * a.choose j = r.choose j * (r - j).choose (a - j) := Nat.choose_mul hja
  have h2 : r.choose t * t.choose j = r.choose j * (r - j).choose (t - j) := Nat.choose_mul hjt
  have ha1 : (r - j) - (a - j) = r - a := by omega
  have ht1 : (r - j) - (t - j) = r - t := by omega
  have h3 : (r - j).choose ((a - j) + (t - j)) * ((a - j) + (t - j)).choose (a - j) =
      (r - j).choose (a - j) * (r - a).choose (t - j) := by
    have := Nat.choose_mul (n := r - j) (k := (a - j) + (t - j)) (s := a - j) (Nat.le_add_right _ _)
    simpa [ha1, Nat.add_sub_cancel_left] using this
  have h4 : (r - j).choose ((t - j) + (a - j)) * ((t - j) + (a - j)).choose (t - j) =
      (r - j).choose (t - j) * (r - t).choose (a - j) := by
    have := Nat.choose_mul (n := r - j) (k := (t - j) + (a - j)) (s := t - j) (Nat.le_add_right _ _)
    simpa [ht1, Nat.add_sub_cancel_left] using this
  have hsym : ((a - j) + (t - j)).choose (a - j) = ((t - j) + (a - j)).choose (t - j) := by
    calc ((a - j) + (t - j)).choose (a - j)
        = ((a - j) + (t - j)).choose (((a - j) + (t - j)) - (t - j)) := by rw [Nat.add_sub_cancel]
      _ = ((a - j) + (t - j)).choose (t - j) := Nat.choose_symm (Nat.le_add_left _ _)
      _ = ((t - j) + (a - j)).choose (t - j) := by rw [Nat.add_comm]
  calc r.choose a * a.choose j * (r - a).choose (t - j)
      = r.choose j * ((r - j).choose (a - j) * (r - a).choose (t - j)) := by rw [h1, mul_assoc]
    _ = r.choose j * ((r - j).choose ((a - j) + (t - j)) * ((a - j) + (t - j)).choose (a - j)) := by rw [← h3]
    _ = r.choose j * ((r - j).choose ((t - j) + (a - j)) * ((t - j) + (a - j)).choose (t - j)) := by rw [hsym, Nat.add_comm (a - j)]
    _ = r.choose j * ((r - j).choose (t - j) * (r - t).choose (a - j)) := by rw [h4]
    _ = r.choose t * t.choose j * (r - t).choose (a - j) := by rw [← mul_assoc, ← h2]

lemma krawtchouk_reciprocity (r t a : ℕ) (ht : t ≤ r) (ha : a ≤ r) :
    (r.choose a : ℤ) * krawtchouk r t a = (r.choose t : ℤ) * krawtchouk r a t := by
  unfold krawtchouk
  rw [Finset.mul_sum, Finset.mul_sum]
  have hL : ∑ j ∈ Finset.range (t + 1), (r.choose a : ℤ) * ((-1 : ℤ) ^ j * (a.choose j : ℤ) * ((r - a).choose (t - j) : ℤ)) =
      ∑ j ∈ Finset.range (min t a + 1), (r.choose a : ℤ) * ((-1 : ℤ) ^ j * (a.choose j : ℤ) * ((r - a).choose (t - j) : ℤ)) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j hj1 hj2 => ?_
    rw [Finset.mem_range] at hj1 hj2
    have hja : a < j := by omega
    simp [Nat.choose_eq_zero_of_lt hja]
  have hR : ∑ j ∈ Finset.range (a + 1), (r.choose t : ℤ) * ((-1 : ℤ) ^ j * (t.choose j : ℤ) * ((r - t).choose (a - j) : ℤ)) =
      ∑ j ∈ Finset.range (min t a + 1), (r.choose t : ℤ) * ((-1 : ℤ) ^ j * (t.choose j : ℤ) * ((r - t).choose (a - j) : ℤ)) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j hj1 hj2 => ?_
    rw [Finset.mem_range] at hj1 hj2
    have hjt : t < j := by omega
    simp [Nat.choose_eq_zero_of_lt hjt]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hjt : j ≤ t := by omega
  have hja : j ≤ a := by omega
  have hnat := choose_triple_symm r t a j ht ha hjt hja
  have hint : (r.choose a : ℤ) * (a.choose j : ℤ) * ((r - a).choose (t - j) : ℤ) =
      (r.choose t : ℤ) * (t.choose j : ℤ) * ((r - t).choose (a - j) : ℤ) := by
    exact_mod_cast hnat
  calc (r.choose a : ℤ) * ((-1 : ℤ) ^ j * (a.choose j : ℤ) * ((r - a).choose (t - j) : ℤ))
      = (-1 : ℤ) ^ j * ((r.choose a : ℤ) * (a.choose j : ℤ) * ((r - a).choose (t - j) : ℤ)) := by ring
    _ = (-1 : ℤ) ^ j * ((r.choose t : ℤ) * (t.choose j : ℤ) * ((r - t).choose (a - j) : ℤ)) := by rw [hint]
    _ = (r.choose t : ℤ) * ((-1 : ℤ) ^ j * (t.choose j : ℤ) * ((r - t).choose (a - j) : ℤ)) := by ring

noncomputable def krawtchoukPoly (r u : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (u + 1),
    Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) *
      (∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ))) *
      (∏ i ∈ Finset.range (u - j), (Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ)))

private lemma desc_prod_eq_descFactorial (m j : ℕ) :
    (∏ i ∈ Finset.range j, ((m : ℝ) - (i : ℝ))) = (Nat.descFactorial m j : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ]
    by_cases hjm : j ≤ m
    · rw [Nat.cast_mul, Nat.cast_sub hjm]
      ring
    · have hlt : m < j := Nat.lt_of_not_ge hjm
      have hdf : Nat.descFactorial m j = 0 := Nat.descFactorial_of_lt hlt
      simp [hdf]

private lemma desc_prod_eq_choose_mul_factorial (m j : ℕ) :
    (∏ i ∈ Finset.range j, ((m : ℝ) - (i : ℝ))) = (m.choose j : ℝ) * (j.factorial : ℝ) := by
  rw [desc_prod_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

lemma krawtchoukPoly_eval (r u t : ℕ) (ht : t ≤ r) :
    (krawtchoukPoly r u).eval (t : ℝ) = (krawtchouk r u t : ℝ) := by
  unfold krawtchoukPoly krawtchouk
  rw [Polynomial.eval_finsetSum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X]
  have h1 := desc_prod_eq_choose_mul_factorial t j
  have h2 : (∏ i ∈ Finset.range (u - j), ((r : ℝ) - (t : ℝ) - (i : ℝ))) =
      (((r - t).choose (u - j) : ℕ) : ℝ) * (((u - j).factorial : ℕ) : ℝ) := by
    have hsub : (r : ℝ) - (t : ℝ) = ((r - t : ℕ) : ℝ) := by rw [Nat.cast_sub ht]
    simp_rw [hsub]
    exact desc_prod_eq_choose_mul_factorial (r - t) (u - j)
  rw [h1, h2]
  have hjf : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have huf : ((u - j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (u - j))
  field_simp [hjf, huf]

private lemma natDegree_prod_X_sub_C (k : ℕ) (f : ℕ → ℝ) :
    (∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (f i))).natDegree = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmon : (∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (f i))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
    rw [Finset.prod_range_succ, Polynomial.natDegree_mul hmon.ne_zero (Polynomial.monic_X_sub_C _).ne_zero,
      ih, Polynomial.natDegree_X_sub_C]

private lemma krawtchoukPoly_term_deg_and_coeff (r u j : ℕ) (hj : j ≤ u) :
    let T := Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) *
      (∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ))) *
      (∏ i ∈ Finset.range (u - j), (Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ)))
    T.natDegree ≤ u ∧ T.coeff u = (-1 : ℝ) ^ u / ((j.factorial : ℝ) * ((u - j).factorial : ℝ)) := by
  intro T
  let P₁ : Polynomial ℝ := ∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ))
  let Q₂ : Polynomial ℝ := ∏ i ∈ Finset.range (u - j), (Polynomial.X - Polynomial.C ((r : ℝ) - (i : ℝ)))
  have hP1_monic : P₁.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hQ2_monic : Q₂.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hP1_deg : P₁.natDegree = j := natDegree_prod_X_sub_C j (fun i => (i : ℝ))
  have hQ2_deg : Q₂.natDegree = u - j := natDegree_prod_X_sub_C (u - j) (fun i => (r : ℝ) - (i : ℝ))
  have hneg1 : (-1 : Polynomial ℝ) = Polynomial.C (-1 : ℝ) := by simp
  have hP2_eq : (∏ i ∈ Finset.range (u - j), (Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ))) =
      Polynomial.C ((-1 : ℝ) ^ (u - j)) * Q₂ := by
    have hfac : ∀ i : ℕ, Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ) =
        (-1 : Polynomial ℝ) * (Polynomial.X - Polynomial.C ((r : ℝ) - (i : ℝ))) := fun i => by
      simp only [map_sub]; ring
    simp_rw [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, hneg1, ← map_pow]
    rfl
  have hPQ_monic : (P₁ * Q₂).Monic := hP1_monic.mul hQ2_monic
  have hPQ_deg : (P₁ * Q₂).natDegree = u := by
    rw [Polynomial.natDegree_mul' (by simp [hP1_monic.leadingCoeff, hQ2_monic.leadingCoeff]),
      hP1_deg, hQ2_deg]
    omega
  have hTeq : T = Polynomial.C ((-1 : ℝ) ^ u / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) * (P₁ * Q₂) := by
    dsimp [T]
    change Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) * P₁ *
        (∏ i ∈ Finset.range (u - j), (Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ))) = _
    rw [hP2_eq]
    have hpow : (-1 : ℝ) ^ j * (-1 : ℝ) ^ (u - j) = (-1 : ℝ) ^ u := by
      rw [← pow_add, Nat.add_sub_cancel' hj]
    calc Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) * P₁ *
          (Polynomial.C ((-1 : ℝ) ^ (u - j)) * Q₂)
        = (Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) *
            Polynomial.C ((-1 : ℝ) ^ (u - j))) * (P₁ * Q₂) := by ring
      _ = Polynomial.C ((-1 : ℝ) ^ u / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) * (P₁ * Q₂) := by
          rw [← map_mul]; congr 2; rw [← hpow]; ring
  rw [hTeq]
  constructor
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hPQ_deg.le
  · rw [Polynomial.coeff_C_mul, ← hPQ_deg, Polynomial.coeff_natDegree, hPQ_monic.leadingCoeff, mul_one]

lemma krawtchoukPoly_deg_le (r u : ℕ) : (krawtchoukPoly r u).natDegree ≤ u := by
  unfold krawtchoukPoly
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le fun j hj => ?_
  exact (krawtchoukPoly_term_deg_and_coeff r u j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1

lemma krawtchoukPoly_coeff_self (r u : ℕ) :
    (krawtchoukPoly r u).coeff u = (-2 : ℝ) ^ u / (u.factorial : ℝ) := by
  unfold krawtchoukPoly
  rw [Polynomial.finsetSum_coeff]
  have hsum : ∑ j ∈ Finset.range (u + 1),
      (Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) *
        (∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ))) *
        (∏ i ∈ Finset.range (u - j), (Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ)))).coeff u =
      ∑ j ∈ Finset.range (u + 1), (-1 : ℝ) ^ u / ((j.factorial : ℝ) * ((u - j).factorial : ℝ)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    exact (krawtchoukPoly_term_deg_and_coeff r u j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2
  rw [hsum]
  have hu : (u.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero u)
  have hterm : ∀ j ∈ Finset.range (u + 1),
      (-1 : ℝ) ^ u / ((j.factorial : ℝ) * ((u - j).factorial : ℝ)) =
        ((-1 : ℝ) ^ u / (u.factorial : ℝ)) * (u.choose j : ℝ) := by
    intro j hj
    have hj' : j ≤ u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hch := Nat.choose_mul_factorial_mul_factorial hj'
    have hchR : (u.choose j : ℝ) * (j.factorial : ℝ) * ((u - j).factorial : ℝ) = (u.factorial : ℝ) := by
      exact_mod_cast hch
    have hjf : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have huf : ((u - j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (u - j))
    rw [div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero hjf huf) hu]
    rw [← hchR]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hbin : ∑ j ∈ Finset.range (u + 1), (u.choose j : ℝ) = (2 : ℝ) ^ u := by
    exact_mod_cast Nat.sum_range_choose u
  rw [hbin]
  have hpow : (-1 : ℝ) ^ u * (2 : ℝ) ^ u = (-2 : ℝ) ^ u := by
    rw [← mul_pow]; norm_num
  rw [div_mul_eq_mul_div, hpow]

lemma krawtchoukPoly_coeff_self_ne_zero (r u : ℕ) :
    (krawtchoukPoly r u).coeff u ≠ 0 := by
  rw [krawtchoukPoly_coeff_self]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero u))

lemma krawtchouk_poly_orthogonality (r a : ℕ) (ha : a ≤ r) :
    ∀ d : ℕ, d < a → ∀ P : Polynomial ℝ, P.natDegree ≤ d →
      ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P.eval (t : ℝ) = 0 := by
  intro d hd P hP
  induction d generalizing P with
  | zero =>
    have hP0 : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hP
    rw [hP0]
    have h0 : krawtchoukPoly r 0 = 1 := by
      unfold krawtchoukPoly; simp
    have hsum : ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * (Polynomial.C (P.coeff 0)).eval (t : ℝ) =
        P.coeff 0 * ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * (krawtchouk r 0 t : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hk0 : (krawtchouk r 0 t : ℝ) = 1 := by
        rw [← krawtchoukPoly_eval r 0 t (Nat.lt_succ_iff.mp t.isLt), h0]; simp
      simp [hk0]; ring
    rw [hsum]
    have horth := krawtchouk_weighted_orthogonality r ⟨a, by omega⟩ ⟨0, by omega⟩
    have ha0 : a ≠ 0 := by omega
    simp [ha0] at horth
    rw [horth, mul_zero]
  | succ d ih =>
    let K := krawtchoukPoly r (d + 1)
    let c := P.coeff (d + 1) / K.coeff (d + 1)
    let P' := P - Polynomial.C c * K
    have hK_ne : K.coeff (d + 1) ≠ 0 := krawtchoukPoly_coeff_self_ne_zero r (d + 1)
    have hP'_deg : P'.natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      simp only [P', Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      by_cases hNd : N = d + 1
      · subst hNd
        dsimp [c]
        rw [div_mul_cancel₀ _ hK_ne, sub_self]
      · have hNgt : d + 1 < N := by omega
        have h1 : P.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hNgt)
        have h2 : K.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (krawtchoukPoly_deg_le r (d + 1)) hNgt)
        simp [h1, h2]
    have hsplit : ∀ t : Fin (r + 1), P.eval (t : ℝ) = P'.eval (t : ℝ) + c * K.eval (t : ℝ) := fun t => by
      simp [P']
    have hsum : ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P.eval (t : ℝ) =
        (∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P'.eval (t : ℝ)) +
        c * ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * (krawtchouk r (d + 1) t : ℝ) := by
      calc ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P.eval (t : ℝ)
          = ∑ t : Fin (r + 1), ((r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P'.eval (t : ℝ) +
              c * ((r.choose t : ℝ) * (krawtchouk r a t : ℝ) * K.eval (t : ℝ))) := by
            refine Finset.sum_congr rfl fun t _ => ?_; rw [hsplit t]; ring
        _ = (∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P'.eval (t : ℝ)) +
              c * ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * K.eval (t : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = _ := by
            congr 2
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [krawtchoukPoly_eval r (d + 1) t (Nat.lt_succ_iff.mp t.isLt)]
    rw [hsum, ih (by omega) P' hP'_deg]
    have horth := krawtchouk_weighted_orthogonality r ⟨a, by omega⟩ ⟨d + 1, by omega⟩
    have hne : (⟨a, by omega⟩ : Fin (r + 1)) ≠ ⟨d + 1, by omega⟩ := by
      intro h; simp at h; omega
    simp [hne] at horth
    rw [horth]
    ring

lemma L_vanish_of_gt (m : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ m) (a : Fin (2 * m + 1 + 1))
    (ha : m < (a : ℕ)) :
    ∑ t : Fin (2 * m + 1 + 1), (krawtchouk (2 * m + 1) t a : ℝ) * P.eval (t : ℝ) = 0 := by
  let r := 2 * m + 1
  have ha_le : (a : ℕ) ≤ r := Nat.lt_succ_iff.mp a.isLt
  have hpos : (0 : ℝ) < (r.choose a : ℝ) := by
    exact_mod_cast Nat.choose_pos ha_le
  have hmul : (r.choose a : ℝ) * ∑ t : Fin (r + 1), (krawtchouk r t a : ℝ) * P.eval (t : ℝ) = 0 := by
    rw [Finset.mul_sum]
    have hrew : ∀ t : Fin (r + 1),
        (r.choose a : ℝ) * ((krawtchouk r t a : ℝ) * P.eval (t : ℝ)) =
          (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P.eval (t : ℝ) := by
      intro t
      have ht_le : (t : ℕ) ≤ r := Nat.lt_succ_iff.mp t.isLt
      have hrec : (r.choose a : ℝ) * (krawtchouk r t a : ℝ) = (r.choose t : ℝ) * (krawtchouk r a t : ℝ) := by
        exact_mod_cast krawtchouk_reciprocity r t a ht_le ha_le
      calc (r.choose a : ℝ) * ((krawtchouk r t a : ℝ) * P.eval (t : ℝ))
          = ((r.choose a : ℝ) * (krawtchouk r t a : ℝ)) * P.eval (t : ℝ) := by ring
        _ = ((r.choose t : ℝ) * (krawtchouk r a t : ℝ)) * P.eval (t : ℝ) := by rw [hrec]
        _ = (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P.eval (t : ℝ) := by ring
    rw [Finset.sum_congr rfl fun t _ => hrew t]
    exact krawtchouk_poly_orthogonality r a ha_le m ha P hP
  exact (mul_eq_zero.mp hmul).resolve_left hpos.ne'

lemma U_vanish_of_le (m : ℕ) (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ m) (a : Fin (2 * m + 1 + 1))
    (ha : (a : ℕ) ≤ m) :
    ∑ t : Fin (2 * m + 1 + 1), (krawtchouk (2 * m + 1) t a : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * Q.eval (t : ℝ)) = 0 := by
  let r := 2 * m + 1
  let a' : Fin (r + 1) := ⟨r - a, by omega⟩
  have hgt : m < (a' : ℕ) := by dsimp [a']; omega
  have hL := L_vanish_of_gt m Q hQ a' hgt
  have hrew : ∀ t : Fin (r + 1),
      (krawtchouk r t a' : ℝ) * Q.eval (t : ℝ) =
        (krawtchouk r t a : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * Q.eval (t : ℝ)) := by
    intro t
    have ha_le : (a : ℕ) ≤ r := Nat.lt_succ_iff.mp a.isLt
    have href : (krawtchouk r t a' : ℝ) = (-1 : ℝ) ^ (t : ℕ) * (krawtchouk r t a : ℝ) := by
      exact_mod_cast krawtchouk_reflection r t a ha_le
    rw [href]
    ring
  rw [← hL]
  symm
  exact Finset.sum_congr rfl fun t _ => hrew t

lemma krawtchouk_eq_powersetCard_sum {n' r : ℕ} (A : Finset (Fin n')) (hA : A.card = r)
    (u : Fin (r + 1)) (S : Qubits n') :
    (krawtchouk r u ((A.filter fun i => S i).card) : ℤ) =
      ∑ T ∈ A.powersetCard (u : ℕ), (-1 : ℤ) ^ ((T.filter fun i => S i).card) := by
  let A₁ := A.filter fun i => S i = true
  let A₀ := A.filter fun i => !(S i = true)
  let a := A₁.card
  have ha_le : a ≤ r := by
    rw [← hA]
    exact Finset.card_filter_le _ _
  have hA₀_card : A₀.card = r - a := by
    have hsum := Finset.card_filter_add_card_filter_not (s := A) (p := fun i => S i = true)
    rw [hA] at hsum
    dsimp [A₀]
    have hcard_eq : A₀.card = (A.filter fun i => ¬(S i = true)).card := by
      congr 1; ext i; dsimp [A₀]; simp
    rw [hcard_eq]
    dsimp [a, A₁]
    exact Nat.eq_sub_of_add_eq' hsum
  have hA₁_sub : ∀ x ∈ A₁, x ∈ A := fun x hx => (Finset.mem_filter.mp hx).1
  have hA₀_sub : ∀ x ∈ A₀, x ∈ A := fun x hx => (Finset.mem_filter.mp hx).1
  let e₁ : Fin a ≃ A₁ := A₁.equivFin.symm
  let e₀ : Fin (r - a) ≃ A₀ := (A₀.equivFin.trans (finCongr hA₀_card)).symm
  let φ : Fin r → Fin n' := fun i =>
    if h : (i : ℕ) < a then (e₁ ⟨i, h⟩).1 else (e₀ ⟨i - a, by omega⟩).1
  have hφ_mem : ∀ i : Fin r, φ i ∈ A := fun i => by
    dsimp [φ]
    split_ifs with h
    · exact hA₁_sub _ (e₁ ⟨i, h⟩).2
    · exact hA₀_sub _ (e₀ ⟨i - a, by omega⟩).2
  have hφ_S : ∀ i : Fin r, S (φ i) = true ↔ (i : ℕ) < a := fun i => by
    dsimp [φ]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => (Finset.mem_filter.mp (e₁ ⟨i, h⟩).2).2⟩
    · constructor
      · intro hS
        exfalso
        have hnot := (Finset.mem_filter.mp (e₀ ⟨i - a, by omega⟩).2).2
        simp [hS] at hnot
      · intro hi; exact False.elim (h hi)
  have hφ_inj : Function.Injective φ := by
    intro i j hij
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · have h' : (e₁ ⟨i, hi⟩).1 = (e₁ ⟨j, hj⟩).1 := by
        dsimp only [φ] at hij; rw [dif_pos hi, dif_pos hj] at hij; exact hij
      have h'' := e₁.injective (Subtype.ext h')
      exact Fin.ext (congrArg (Fin.val : Fin a → ℕ) h'')
    · exfalso
      have h1 := (hφ_S i).mpr hi
      rw [hij] at h1
      exact hj ((hφ_S j).mp h1)
    · exfalso
      have h1 := (hφ_S j).mpr hj
      rw [← hij] at h1
      exact hi ((hφ_S i).mp h1)
    · have h' : (e₀ ⟨i - a, by omega⟩).1 = (e₀ ⟨j - a, by omega⟩).1 := by
        dsimp only [φ] at hij; rw [dif_neg hi, dif_neg hj] at hij; exact hij
      have h'' := e₀.injective (Subtype.ext h')
      have hval := congrArg Fin.val h''
      dsimp at hval
      ext; omega
  let e : Fin r ↪ Fin n' := ⟨φ, hφ_inj⟩
  have hmap_eq : (Finset.univ : Finset (Fin r)).map e = A := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_map] at hx
      rcases hx with ⟨i, _, rfl⟩
      exact hφ_mem i
    · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, hA]
  have hpow_eq : ((Finset.univ : Finset (Fin r)).powersetCard (u : ℕ)).map (Finset.mapEmbedding e).toEmbedding =
      A.powersetCard (u : ℕ) := by
    rw [← hmap_eq]
    ext T
    simp only [Finset.mem_map, Finset.mem_powersetCard, Finset.mapEmbedding_apply,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨T₀, ⟨_, hT₀c⟩, rfl⟩
      exact ⟨Finset.map_subset_map.mpr (Finset.subset_univ _), by simpa using hT₀c⟩
    · rintro ⟨hTsub, hTc⟩
      refine ⟨T.preimage e e.injective.injOn, ?_, ?_⟩
      · refine ⟨Finset.subset_univ _, ?_⟩
        rw [Finset.card_preimage T e e.injective.injOn, Finset.filter_true_of_mem]
        · exact hTc
        · intro x hx
          have hx' := hTsub hx
          rw [Finset.mem_map] at hx'
          rcases hx' with ⟨i, _, rfl⟩
          exact ⟨i, rfl⟩
      · ext x
        simp only [Finset.mem_map, Finset.mem_preimage]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact hi
        · intro hx
          have hx' := hTsub hx
          rw [Finset.mem_map] at hx'
          rcases hx' with ⟨i, _, rfl⟩
          exact ⟨i, hx, rfl⟩
  have hchar := krawtchouk_as_character_sum r u ⟨a, by omega⟩
  change (krawtchouk r u a : ℤ) = _
  rw [hchar, ← hpow_eq, Finset.sum_map]
  refine Finset.sum_congr rfl fun T₀ _ => ?_
  congr 1
  change (T₀ ∩ Finset.univ.filter fun i : Fin r => (i : ℕ) < a).card = ((T₀.map e).filter fun i => S i).card
  have hfilt : ((T₀.map e).filter fun i => S i = true) =
      (T₀ ∩ Finset.univ.filter fun i : Fin r => (i : ℕ) < a).map e := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_inter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hSx⟩
      exact ⟨i, ⟨hi, (hφ_S i).mp (by simpa [e] using hSx)⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hia⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, by simpa [e] using (hφ_S i).mpr hia⟩
  have hfilt' : ((T₀.map e).filter fun i => S i) =
      ((T₀.map e).filter fun i => S i = true) := by
    ext x; simp
  rw [hfilt', hfilt, Finset.card_map]

def rootSetP (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * m)).filter fun r => r % 4 = 0 ∨ r % 4 = 1

def rootSetQ (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * m)).filter fun r => r % 4 = 2 ∨ r % 4 = 3

lemma rootSetP_disjoint_rootSetQ (m : ℕ) : Disjoint (rootSetP m) (rootSetQ m) := by
  rw [Finset.disjoint_left]
  intro x hxP hxQ
  simp only [rootSetP, rootSetQ, Finset.mem_filter] at hxP hxQ
  omega

lemma rootSetP_union_rootSetQ (m : ℕ) : rootSetP m ∪ rootSetQ m = Finset.Icc 1 (2 * m) := by
  ext x
  simp only [Finset.mem_union, rootSetP, rootSetQ, Finset.mem_filter, Finset.mem_Icc]
  omega

lemma card_rootSetP_and_Q (m : ℕ) : (rootSetP m).card = m ∧ (rootSetQ m).card = m := by
  induction m with
  | zero => simp [rootSetP, rootSetQ]
  | succ m ih =>
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hP_step : rootSetP (k + k + 1) = insert (2 * (k + k) + 1) (rootSetP (k + k)) := by
        ext x
        simp only [Finset.mem_insert, rootSetP, Finset.mem_filter, Finset.mem_Icc]
        omega
      have hQ_step : rootSetQ (k + k + 1) = insert (2 * (k + k) + 2) (rootSetQ (k + k)) := by
        ext x
        simp only [Finset.mem_insert, rootSetQ, Finset.mem_filter, Finset.mem_Icc]
        omega
      have hnotP : 2 * (k + k) + 1 ∉ rootSetP (k + k) := by
        simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]; omega
      have hnotQ : 2 * (k + k) + 2 ∉ rootSetQ (k + k) := by
        simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]; omega
      exact ⟨by rw [hP_step, Finset.card_insert_of_notMem hnotP, ih.1],
             by rw [hQ_step, Finset.card_insert_of_notMem hnotQ, ih.2]⟩
    · have hP_step : rootSetP (2 * k + 1 + 1) = insert (2 * (2 * k + 1) + 2) (rootSetP (2 * k + 1)) := by
        ext x
        simp only [Finset.mem_insert, rootSetP, Finset.mem_filter, Finset.mem_Icc]
        omega
      have hQ_step : rootSetQ (2 * k + 1 + 1) = insert (2 * (2 * k + 1) + 1) (rootSetQ (2 * k + 1)) := by
        ext x
        simp only [Finset.mem_insert, rootSetQ, Finset.mem_filter, Finset.mem_Icc]
        omega
      have hnotP : 2 * (2 * k + 1) + 2 ∉ rootSetP (2 * k + 1) := by
        simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]; omega
      have hnotQ : 2 * (2 * k + 1) + 1 ∉ rootSetQ (2 * k + 1) := by
        simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]; omega
      exact ⟨by rw [hP_step, Finset.card_insert_of_notMem hnotP, ih.1],
             by rw [hQ_step, Finset.card_insert_of_notMem hnotQ, ih.2]⟩

noncomputable def pPolyRaw (m : ℕ) : Polynomial ℝ :=
  ∏ r ∈ rootSetP m, (Polynomial.X - Polynomial.C (r : ℝ))

noncomputable def qPolyRaw (m : ℕ) : Polynomial ℝ :=
  ∏ r ∈ rootSetQ m, (Polynomial.X - Polynomial.C (r : ℝ))

lemma pPolyRaw_deg (m : ℕ) : (pPolyRaw m).natDegree ≤ m := by
  unfold pPolyRaw
  refine (Polynomial.natDegree_prod_le _ _).trans (le_of_eq ?_)
  calc ∑ r ∈ rootSetP m, (Polynomial.X - Polynomial.C (r : ℝ)).natDegree
      = ∑ _ ∈ rootSetP m, 1 := Finset.sum_congr rfl fun r _ => Polynomial.natDegree_X_sub_C (r : ℝ)
    _ = (rootSetP m).card := by simp
    _ = m := (card_rootSetP_and_Q m).1

lemma qPolyRaw_deg (m : ℕ) : (qPolyRaw m).natDegree ≤ m := by
  unfold qPolyRaw
  refine (Polynomial.natDegree_prod_le _ _).trans (le_of_eq ?_)
  calc ∑ r ∈ rootSetQ m, (Polynomial.X - Polynomial.C (r : ℝ)).natDegree
      = ∑ _ ∈ rootSetQ m, 1 := Finset.sum_congr rfl fun r _ => Polynomial.natDegree_X_sub_C (r : ℝ)
    _ = (rootSetQ m).card := by simp
    _ = m := (card_rootSetP_and_Q m).2

lemma pPolyRaw_eval_zero_ne (m : ℕ) : (pPolyRaw m).eval 0 ≠ 0 := by
  unfold pPolyRaw
  rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro r hr
  simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc] at hr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  linarith

lemma qPolyRaw_eval_zero_ne (m : ℕ) : (qPolyRaw m).eval 0 ≠ 0 := by
  unfold qPolyRaw
  rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro r hr
  simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc] at hr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  linarith

private lemma prod_Icc_eq_factorial (N : ℕ) :
    (∏ r ∈ Finset.Icc 1 N, (r : ℝ)) = (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
    rw [hIcc, Finset.prod_insert hnot, ih, Nat.factorial_succ]
    push_cast; ring

lemma pPolyRaw_mul_qPolyRaw_eval_zero (m : ℕ) :
    (pPolyRaw m).eval 0 * (qPolyRaw m).eval 0 = ((2 * m).factorial : ℝ) := by
  unfold pPolyRaw qPolyRaw
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  rw [← Finset.prod_union (rootSetP_disjoint_rootSetQ m), rootSetP_union_rootSetQ]
  have hneg : ∀ r ∈ Finset.Icc 1 (2 * m), (-(r : ℝ)) = (-1 : ℝ) * (r : ℝ) := fun r _ => by ring
  rw [Finset.prod_congr rfl hneg, Finset.prod_mul_distrib, Finset.prod_const]
  have hcard : (Finset.Icc 1 (2 * m)).card = 2 * m := by simp
  rw [hcard, pow_mul]
  simp [prod_Icc_eq_factorial]

lemma pPolyRaw_mul_qPolyRaw_eval_top (m : ℕ) :
    (pPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ) * (qPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ) =
      ((2 * m).factorial : ℝ) := by
  unfold pPolyRaw qPolyRaw
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [← Finset.prod_union (rootSetP_disjoint_rootSetQ m), rootSetP_union_rootSetQ]
  have hbij : (∏ r ∈ Finset.Icc 1 (2 * m), (((2 * m + 1 : ℕ) : ℝ) - (r : ℝ))) =
      ∏ v ∈ Finset.Icc 1 (2 * m), (v : ℝ) := by
    refine Finset.prod_bij (fun r _ => 2 * m + 1 - r)
      (fun r hr => by simp only [Finset.mem_Icc] at hr ⊢; omega)
      (fun r₁ r₂ hr₁ hr₂ h => by simp only [Finset.mem_Icc] at hr₁ hr₂; omega)
      (fun v hv => ⟨2 * m + 1 - v, by simp only [Finset.mem_Icc] at hv ⊢; omega, by
        simp only [Finset.mem_Icc] at hv; omega⟩)
      (fun r hr => by
        simp only [Finset.mem_Icc] at hr
        rw [Nat.cast_sub (by omega : r ≤ 2 * m + 1)])
  rw [hbij, prod_Icc_eq_factorial]

noncomputable def PPoly (m : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / (Real.sqrt 2 * (pPolyRaw m).eval 0)) * pPolyRaw m

noncomputable def QPoly (m : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / (Real.sqrt 2 * (qPolyRaw m).eval 0)) * qPolyRaw m

lemma PPoly_deg (m : ℕ) : (PPoly m).natDegree ≤ m :=
  (Polynomial.natDegree_C_mul_le _ _).trans (pPolyRaw_deg m)

lemma QPoly_deg (m : ℕ) : (QPoly m).natDegree ≤ m :=
  (Polynomial.natDegree_C_mul_le _ _).trans (qPolyRaw_deg m)

lemma PPoly_eval_zero (m : ℕ) : (PPoly m).eval 0 = 1 / Real.sqrt 2 := by
  unfold PPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hp := pPolyRaw_eval_zero_ne m
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hp, hs]

lemma QPoly_eval_zero (m : ℕ) : (QPoly m).eval 0 = 1 / Real.sqrt 2 := by
  unfold QPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hq := qPolyRaw_eval_zero_ne m
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hq, hs]

lemma PPoly_mul_QPoly_eval_top (m : ℕ) :
    (PPoly m).eval ((2 * m + 1 : ℕ) : ℝ) * (QPoly m).eval ((2 * m + 1 : ℕ) : ℝ) = 1 / 2 := by
  unfold PPoly QPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hp := pPolyRaw_eval_zero_ne m
  have hq := qPolyRaw_eval_zero_ne m
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfac : ((2 * m).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * m))
  have htop := pPolyRaw_mul_qPolyRaw_eval_top m
  have hzero := pPolyRaw_mul_qPolyRaw_eval_zero m
  calc (1 / (Real.sqrt 2 * (pPolyRaw m).eval 0) * (pPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ)) *
        (1 / (Real.sqrt 2 * (qPolyRaw m).eval 0) * (qPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ))
      = ((pPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ) * (qPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ)) /
          ((Real.sqrt 2 ^ 2) * ((pPolyRaw m).eval 0 * (qPolyRaw m).eval 0)) := by ring
    _ = ((2 * m).factorial : ℝ) / (2 * ((2 * m).factorial : ℝ)) := by rw [htop, hs, hzero]
    _ = 1 / 2 := by field_simp [hfac]

lemma PPoly_eval_root {m t : ℕ} (ht : t ∈ rootSetP m) : (PPoly m).eval (t : ℝ) = 0 := by
  unfold PPoly pPolyRaw
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X]
  have hprod : (∏ r ∈ rootSetP m, ((t : ℝ) - (r : ℝ))) = 0 := Finset.prod_eq_zero ht (by simp)
  rw [hprod, mul_zero]

lemma QPoly_eval_root {m t : ℕ} (ht : t ∈ rootSetQ m) : (QPoly m).eval (t : ℝ) = 0 := by
  unfold QPoly qPolyRaw
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X]
  have hprod : (∏ r ∈ rootSetQ m, ((t : ℝ) - (r : ℝ))) = 0 := Finset.prod_eq_zero ht (by simp)
  rw [hprod, mul_zero]

noncomputable def compProd (N t : ℕ) : ℝ :=
  ∏ u ∈ (Finset.Icc 1 N).erase t, |(t : ℝ) - (u : ℝ)|

lemma compProd_pos (N t : ℕ) : 0 < compProd N t := by
  unfold compProd
  refine Finset.prod_pos fun u hu => ?_
  have hne : u ≠ t := (Finset.mem_erase.mp hu).1
  have hneR : (t : ℝ) ≠ (u : ℝ) := by
    intro h; apply hne; exact_mod_cast h.symm
  exact abs_pos.mpr (sub_ne_zero.mpr hneR)

lemma compProd_zero (N : ℕ) : compProd N 0 = (N.factorial : ℝ) := by
  unfold compProd
  have h0 : 0 ∉ Finset.Icc 1 N := by simp
  rw [Finset.erase_eq_of_notMem h0]
  have hrew : ∀ u ∈ Finset.Icc 1 N, |((0 : ℕ) : ℝ) - (u : ℝ)| = (u : ℝ) := fun u _ => by
    rw [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg u)]
  rw [Finset.prod_congr rfl hrew, prod_Icc_eq_factorial]

lemma compProd_succ (N : ℕ) : compProd N (N + 1) = (N.factorial : ℝ) := by
  unfold compProd
  have hN : N + 1 ∉ Finset.Icc 1 N := by simp
  rw [Finset.erase_eq_of_notMem hN]
  have hbij : (∏ u ∈ Finset.Icc 1 N, |((N + 1 : ℕ) : ℝ) - (u : ℝ)|) = ∏ v ∈ Finset.Icc 1 N, (v : ℝ) := by
    refine Finset.prod_bij (fun u _ => N + 1 - u)
      (fun u hu => by simp only [Finset.mem_Icc] at hu ⊢; omega)
      (fun u₁ u₂ hu₁ hu₂ h => by simp only [Finset.mem_Icc] at hu₁ hu₂; omega)
      (fun v hv => ⟨N + 1 - v, by simp only [Finset.mem_Icc] at hv ⊢; omega, by simp only [Finset.mem_Icc] at hv; omega⟩)
      (fun u hu => by
        simp only [Finset.mem_Icc] at hu
        have hle : (u : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : u ≤ N + 1)
        rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        rw [Nat.cast_sub (by omega : u ≤ N + 1)])
  rw [hbij, prod_Icc_eq_factorial]

lemma compProd_interior (N t : ℕ) (ht1 : 1 ≤ t) (htN : t ≤ N) :
    compProd N t = ((t - 1).factorial : ℝ) * ((N - t).factorial : ℝ) := by
  unfold compProd
  have hpart : (Finset.Icc 1 N).erase t = Finset.Icc 1 (t - 1) ∪ Finset.Icc (t + 1) N := by
    ext u
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (t - 1)) (Finset.Icc (t + 1) N) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    simp only [Finset.mem_Icc] at hu1 hu2
    omega
  rw [hpart, Finset.prod_union hdisj]
  have hL : (∏ u ∈ Finset.Icc 1 (t - 1), |(t : ℝ) - (u : ℝ)|) = ((t - 1).factorial : ℝ) := by
    have hbij : (∏ u ∈ Finset.Icc 1 (t - 1), |(t : ℝ) - (u : ℝ)|) = ∏ v ∈ Finset.Icc 1 (t - 1), (v : ℝ) := by
      refine Finset.prod_bij (fun u _ => t - u)
        (fun u hu => by simp only [Finset.mem_Icc] at hu ⊢; omega)
        (fun u₁ u₂ hu₁ hu₂ h => by simp only [Finset.mem_Icc] at hu₁ hu₂; omega)
        (fun v hv => ⟨t - v, by simp only [Finset.mem_Icc] at hv ⊢; omega, by simp only [Finset.mem_Icc] at hv; omega⟩)
        (fun u hu => by
          simp only [Finset.mem_Icc] at hu
          have hle : (u : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : u ≤ t)
          rw [abs_of_nonneg (sub_nonneg.mpr hle), Nat.cast_sub (by omega : u ≤ t)])
    rw [hbij, prod_Icc_eq_factorial]
  have hR : (∏ u ∈ Finset.Icc (t + 1) N, |(t : ℝ) - (u : ℝ)|) = ((N - t).factorial : ℝ) := by
    have hbij : (∏ u ∈ Finset.Icc (t + 1) N, |(t : ℝ) - (u : ℝ)|) = ∏ v ∈ Finset.Icc 1 (N - t), (v : ℝ) := by
      refine Finset.prod_bij (fun u _ => u - t)
        (fun u hu => by simp only [Finset.mem_Icc] at hu ⊢; omega)
        (fun u₁ u₂ hu₁ hu₂ h => by simp only [Finset.mem_Icc] at hu₁ hu₂; omega)
        (fun v hv => ⟨t + v, by simp only [Finset.mem_Icc] at hv ⊢; omega, by simp only [Finset.mem_Icc] at hv; omega⟩)
        (fun u hu => by
          simp only [Finset.mem_Icc] at hu
          have hle : (t : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : t ≤ u)
          rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, Nat.cast_sub (by omega : t ≤ u)])
    rw [hbij, prod_Icc_eq_factorial]
  rw [hL, hR]

lemma choose_mul_compProd_le {l : ℕ} (_hl : 1 ≤ l) (t : Fin (2 * l + 1 + 1)) :
    ((2 * l + 1).choose (t : ℕ) : ℝ) * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ) ≤
      4 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)) := by
  let r := 2 * l + 1
  have hr_pos : (0 : ℝ) < r := by positivity
  have hfac_pos : (0 : ℝ) < ((2 * l).factorial : ℝ) := by positivity
  by_cases ht0 : (t : ℕ) = 0
  · simp only [ht0, Nat.choose_zero_right, Nat.cast_one, one_mul, compProd_zero]
    rw [div_self hfac_pos.ne']
    have hden_pos : (0 : ℝ) < ((0 + 1 : ℕ) : ℝ) * ((r - 0 + 1 : ℕ) : ℝ) := by positivity
    rw [le_div_iff₀ hden_pos, one_mul]
    have hle : ((0 + 1 : ℕ) : ℝ) * ((r - 0 + 1 : ℕ) : ℝ) ≤ 4 * (r : ℝ) := by
      have : (0 + 1) * (r - 0 + 1) ≤ 4 * r := by dsimp [r]; omega
      exact_mod_cast this
    exact hle
  · by_cases htr : (t : ℕ) = r
    · simp only [htr]
      dsimp [r]
      rw [Nat.choose_self, Nat.cast_one, one_mul, compProd_succ, div_self hfac_pos.ne']
      have hden_pos : (0 : ℝ) < ((2 * l + 1 + 1 : ℕ) : ℝ) * ((2 * l + 1 - (2 * l + 1) + 1 : ℕ) : ℝ) := by positivity
      rw [le_div_iff₀ hden_pos, one_mul]
      have hle : ((2 * l + 1 + 1 : ℕ) : ℝ) * ((2 * l + 1 - (2 * l + 1) + 1 : ℕ) : ℝ) ≤ 4 * ((2 * l + 1 : ℕ) : ℝ) := by
        have hnat_le : (2 * l + 1 + 1) * (2 * l + 1 - (2 * l + 1) + 1) ≤ 4 * (2 * l + 1) := by
          simp only [Nat.sub_self, zero_add, mul_one]; omega
        exact_mod_cast hnat_le
      exact hle
    · have ht1 : 1 ≤ (t : ℕ) := Nat.pos_of_ne_zero ht0
      have ht_le : (t : ℕ) ≤ 2 * l := by have := t.isLt; omega
      rw [compProd_interior (2 * l) (t : ℕ) ht1 ht_le]
      have hrt : 1 ≤ r - (t : ℕ) := by dsimp [r]; omega
      have hnat : r.choose (t : ℕ) * ((t : ℕ) - 1).factorial * (2 * l - (t : ℕ)).factorial * ((t : ℕ) * (r - (t : ℕ))) =
          r * (2 * l).factorial := by
        have hch := Nat.choose_mul_factorial_mul_factorial (show (t : ℕ) ≤ r by omega)
        have ht_fac : (t : ℕ).factorial = (t : ℕ) * ((t : ℕ) - 1).factorial := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ht0
          rw [hk, Nat.factorial_succ]; simp
        have hrt_fac : (r - (t : ℕ)).factorial = (r - (t : ℕ)) * (2 * l - (t : ℕ)).factorial := by
          have hsub : r - (t : ℕ) = (2 * l - (t : ℕ)) + 1 := by dsimp [r]; omega
          rw [hsub, Nat.factorial_succ]
        have hr_fac : r.factorial = r * (2 * l).factorial := by
          dsimp [r]; rw [Nat.factorial_succ]
        calc r.choose (t : ℕ) * ((t : ℕ) - 1).factorial * (2 * l - (t : ℕ)).factorial * ((t : ℕ) * (r - (t : ℕ)))
            = r.choose (t : ℕ) * ((t : ℕ) * ((t : ℕ) - 1).factorial) * ((r - (t : ℕ)) * (2 * l - (t : ℕ)).factorial) := by ring
          _ = r.choose (t : ℕ) * (t : ℕ).factorial * (r - (t : ℕ)).factorial := by rw [← ht_fac, ← hrt_fac]
          _ = r.factorial := hch
          _ = r * (2 * l).factorial := hr_fac
      have hreal : ((r.choose (t : ℕ) : ℝ) * ((((t : ℕ) - 1).factorial : ℝ) * ((2 * l - (t : ℕ)).factorial : ℝ))) / ((2 * l).factorial : ℝ) =
          (r : ℝ) / (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) := by
        have htR : ((t : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ht0
        have hrtR : ((r - (t : ℕ) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : r - (t : ℕ) ≠ 0)
        have hcast : (r.choose (t : ℕ) : ℝ) * (((t : ℕ) - 1).factorial : ℝ) * ((2 * l - (t : ℕ)).factorial : ℝ) *
            (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) = (r : ℝ) * ((2 * l).factorial : ℝ) := by
          exact_mod_cast hnat
        rw [div_eq_div_iff hfac_pos.ne' (mul_ne_zero htR hrtR)]
        calc (r.choose (t : ℕ) : ℝ) * ((((t : ℕ) - 1).factorial : ℝ) * ((2 * l - (t : ℕ)).factorial : ℝ)) *
                (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ))
            = (r.choose (t : ℕ) : ℝ) * (((t : ℕ) - 1).factorial : ℝ) * ((2 * l - (t : ℕ)).factorial : ℝ) *
                (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) := by ring
          _ = (r : ℝ) * ((2 * l).factorial : ℝ) := hcast
      change (r.choose (t : ℕ) : ℝ) * ((((t : ℕ) - 1).factorial : ℝ) * ((2 * l - (t : ℕ)).factorial : ℝ)) / ((2 * l).factorial : ℝ) ≤ _
      rw [hreal]
      have hden1 : (((t : ℕ) + 1 : ℕ) : ℝ) ≤ 2 * ((t : ℕ) : ℝ) := by
        exact_mod_cast (by omega : (t : ℕ) + 1 ≤ 2 * (t : ℕ))
      have hden2 : ((r - (t : ℕ) + 1 : ℕ) : ℝ) ≤ 2 * ((r - (t : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : r - (t : ℕ) + 1 ≤ 2 * (r - (t : ℕ)))
      have ht_pos : (0 : ℝ) < ((t : ℕ) : ℝ) := by positivity
      have hrt_pos : (0 : ℝ) < ((r - (t : ℕ) : ℕ) : ℝ) := by positivity
      have hden_pos : (0 : ℝ) < (((t : ℕ) + 1 : ℕ) : ℝ) * ((r - (t : ℕ) + 1 : ℕ) : ℝ) := by positivity
      have hmul : (((t : ℕ) + 1 : ℕ) : ℝ) * ((r - (t : ℕ) + 1 : ℕ) : ℝ) ≤
          4 * (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) := by
        calc (((t : ℕ) + 1 : ℕ) : ℝ) * ((r - (t : ℕ) + 1 : ℕ) : ℝ)
            ≤ (2 * ((t : ℕ) : ℝ)) * (2 * ((r - (t : ℕ) : ℕ) : ℝ)) :=
              mul_le_mul hden1 hden2 (Nat.cast_nonneg _) (by positivity)
          _ = 4 * (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) := by ring
      have hdiv1 : (r : ℝ) / (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) =
          (4 * (r : ℝ)) / (4 * (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ))) := by
        rw [div_eq_div_iff (mul_pos ht_pos hrt_pos).ne' (by positivity)]; ring
      rw [hdiv1]
      exact div_le_div_of_nonneg_left (by positivity) hden_pos hmul

private lemma prod_erase_union {A B : Finset ℕ} (hdisj : Disjoint A B) (t : ℕ) (f : ℕ → ℝ) :
    (∏ u ∈ (A ∪ B).erase t, f u) = (∏ u ∈ A.erase t, f u) * (∏ u ∈ B.erase t, f u) := by
  have heq : (A ∪ B).erase t = A.erase t ∪ B.erase t := by
    ext x; simp only [Finset.mem_erase, Finset.mem_union]; tauto
  rw [heq, Finset.prod_union (hdisj.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _))]

private lemma block4_real (x : ℝ) (hx : x < 0 ∨ 3 < x) :
    x ^ 2 * (x - 3) ^ 2 ≤ |x| * |x - 1| * |x - 2| * |x - 3| := by
  have hx03 : 0 < x * (x - 3) := by
    rcases hx with h | h
    · exact mul_pos_of_neg_of_neg h (by linarith)
    · exact mul_pos (by linarith) (by linarith)
  have hx12 : 0 < (x - 1) * (x - 2) := by
    rcases hx with h | h
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact mul_pos (by linarith) (by linarith)
  have hle : x * (x - 3) ≤ (x - 1) * (x - 2) := by linarith
  have h1 : x ^ 2 * (x - 3) ^ 2 = (x * (x - 3)) * (x * (x - 3)) := by ring
  have h2 : |x| * |x - 1| * |x - 2| * |x - 3| = (x * (x - 3)) * ((x - 1) * (x - 2)) := by
    calc |x| * |x - 1| * |x - 2| * |x - 3|
        = (|x| * |x - 3|) * (|x - 1| * |x - 2|) := by ring
      _ = |x * (x - 3)| * |(x - 1) * (x - 2)| := by rw [← abs_mul, ← abs_mul]
      _ = (x * (x - 3)) * ((x - 1) * (x - 2)) := by rw [abs_of_pos hx03, abs_of_pos hx12]
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left hle hx03.le

private lemma block4_ineq (a t : ℕ) :
    (∏ u ∈ ({a, a + 3} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) then (2 : ℝ) else 1) *
        (∏ u ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
  by_cases h0 : t = a
  · subst h0
    have hL : ({t, t + 3} : Finset ℕ).erase t = {t + 3} := by
      ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
    have hR : ({t, t + 1, t + 2, t + 3} : Finset ℕ).erase t = {t + 1, t + 2, t + 3} := by
      ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
    have hmem : t ∈ ({t, t + 1, t + 2, t + 3} : Finset ℕ) := by
      simp only [Finset.mem_insert, true_or]
    rw [hL, hR, if_pos hmem, Finset.prod_singleton,
      Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    have h1 : (t : ℝ) - ((t : ℝ) + 1) = -1 := by ring
    have h2 : (t : ℝ) - ((t : ℝ) + 2) = -2 := by ring
    have h3 : (t : ℝ) - ((t : ℝ) + 3) = -3 := by ring
    rw [h1, h2, h3]; norm_num
  · by_cases h1 : t = a + 1
    · subst h1
      have hL : ({a, a + 3} : Finset ℕ).erase (a + 1) = {a, a + 3} := by
        ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
      have hR : ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase (a + 1) = {a, a + 2, a + 3} := by
        ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
      have hmem : a + 1 ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
        simp only [Finset.mem_insert, true_or, or_true]
      rw [hL, hR, if_pos hmem,
        Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton,
        Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      have e1 : ((a : ℝ) + 1) - (a : ℝ) = 1 := by ring
      have e2 : ((a : ℝ) + 1) - ((a : ℝ) + 2) = -1 := by ring
      have e3 : ((a : ℝ) + 1) - ((a : ℝ) + 3) = -2 := by ring
      rw [e1, e2, e3]; norm_num
    · by_cases h2 : t = a + 2
      · subst h2
        have hL : ({a, a + 3} : Finset ℕ).erase (a + 2) = {a, a + 3} := by
          ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
        have hR : ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase (a + 2) = {a, a + 1, a + 3} := by
          ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
        have hmem : a + 2 ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
          simp only [Finset.mem_insert, true_or, or_true]
        rw [hL, hR, if_pos hmem,
          Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton,
          Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
          Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
        simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
        have e1 : ((a : ℝ) + 2) - (a : ℝ) = 2 := by ring
        have e2 : ((a : ℝ) + 2) - ((a : ℝ) + 1) = 1 := by ring
        have e3 : ((a : ℝ) + 2) - ((a : ℝ) + 3) = -1 := by ring
        rw [e1, e2, e3]; norm_num
      · by_cases h3 : t = a + 3
        · subst h3
          have hL : ({a, a + 3} : Finset ℕ).erase (a + 3) = {a} := by
            ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
          have hR : ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase (a + 3) = {a, a + 1, a + 2} := by
            ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
          have hmem : a + 3 ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
          rw [hL, hR, if_pos hmem, Finset.prod_singleton,
            Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
            Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
          simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
          have e1 : ((a : ℝ) + 3) - (a : ℝ) = 3 := by ring
          have e2 : ((a : ℝ) + 3) - ((a : ℝ) + 1) = 2 := by ring
          have e3 : ((a : ℝ) + 3) - ((a : ℝ) + 2) = 1 := by ring
          rw [e1, e2, e3]; norm_num
        · have hnotL : t ∉ ({a, a + 3} : Finset ℕ) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]; omega
          have hnotR : t ∉ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]; omega
          rw [Finset.erase_eq_of_notMem hnotL, Finset.erase_eq_of_notMem hnotR, if_neg hnotR, one_mul,
            Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton,
            Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
            Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
            Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
          simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
          have hlt_or_gt : t < a ∨ a + 3 < t := by omega
          have hx : (t : ℝ) - (a : ℝ) < 0 ∨ 3 < (t : ℝ) - (a : ℝ) := by
            rcases hlt_or_gt with hlt | hgt
            · left; exact sub_neg.mpr (Nat.cast_lt.mpr hlt)
            · right
              have hlt' : ((a + 3 : ℕ) : ℝ) < (t : ℝ) := Nat.cast_lt.mpr hgt
              rw [Nat.cast_add, Nat.cast_ofNat] at hlt'
              linarith
          have hb := block4_real ((t : ℝ) - (a : ℝ)) hx
          simp only [sub_add_eq_sub_sub, mul_assoc] at hb ⊢
          exact hb

private lemma pair2Left_ineq (t : ℕ) :
    (∏ u ∈ ({2} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t = 0 then (2 : ℝ) else 1) * (∏ u ∈ ({1, 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
  by_cases h0 : t = 0
  · subst h0; norm_num
  · by_cases h1 : t = 1
    · subst h1
      have hL : ({2} : Finset ℕ).erase 1 = {2} := by decide
      have hR : ({1, 2} : Finset ℕ).erase 1 = {2} := by decide
      rw [hL, hR, if_neg h0, one_mul, Finset.prod_singleton, Finset.prod_singleton]
      norm_num
    · by_cases h2 : t = 2
      · subst h2
        have hL : ({2} : Finset ℕ).erase 2 = ∅ := by decide
        have hR : ({1, 2} : Finset ℕ).erase 2 = {1} := by decide
        rw [hL, hR, if_neg h0, one_mul, Finset.prod_empty, Finset.prod_singleton]
        norm_num
      · have hL : ({2} : Finset ℕ).erase t = {2} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_singleton]; omega
        have hR : ({1, 2} : Finset ℕ).erase t = {1, 2} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        rw [hL, hR, if_neg h0, one_mul, Finset.prod_singleton,
          Finset.prod_insert (by decide), Finset.prod_singleton]
        simp only [Nat.cast_ofNat, Nat.cast_one]
        have ht1 : (0 : ℝ) < (t : ℝ) - 1 := by
          have : (1 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 1 < t)
          linarith
        have ht2 : (0 : ℝ) < (t : ℝ) - 2 := by
          have : (2 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 2 < t)
          linarith
        rw [abs_of_pos ht1, abs_of_pos ht2, sq]
        exact mul_le_mul_of_nonneg_right (by linarith) ht2.le

private lemma pair2Right_ineq (a t : ℕ) (ht : t ≤ a + 2) :
    (∏ u ∈ ({a} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t = a + 2 then (2 : ℝ) else 1) * (∏ u ∈ ({a, a + 1} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
  by_cases h0 : t = a
  · subst h0
    have hL : ({t} : Finset ℕ).erase t = ∅ := Finset.erase_singleton t
    have hR : ({t, t + 1} : Finset ℕ).erase t = {t + 1} := by
      ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hL, hR, if_neg (by omega), one_mul, Finset.prod_empty, Finset.prod_singleton]
    simp only [Nat.cast_add, Nat.cast_one, sub_add_cancel_left, abs_neg, abs_one, le_refl]
  · by_cases h1 : t = a + 1
    · subst h1
      have hL : ({a} : Finset ℕ).erase (a + 1) = {a} := by
        refine Finset.erase_eq_of_notMem ?_
        simp only [Finset.mem_singleton]; omega
      have hR : ({a, a + 1} : Finset ℕ).erase (a + 1) = {a} := by
        ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
      rw [hL, hR, if_neg (by omega), one_mul, Finset.prod_singleton, Finset.prod_singleton]
      simp only [Nat.cast_add, Nat.cast_one]
      have e : (a : ℝ) + 1 - (a : ℝ) = 1 := by ring
      rw [e]; norm_num
    · by_cases h2 : t = a + 2
      · subst h2
        have hL : ({a} : Finset ℕ).erase (a + 2) = {a} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_singleton]; omega
        have hR : ({a, a + 1} : Finset ℕ).erase (a + 2) = {a, a + 1} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        rw [hL, hR, if_pos rfl, Finset.prod_singleton,
          Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
        simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
        have e1 : (a : ℝ) + 2 - (a : ℝ) = 2 := by ring
        have e2 : (a : ℝ) + 2 - ((a : ℝ) + 1) = 1 := by ring
        rw [e1, e2]; norm_num
      · have hlt : t < a := by omega
        have hL : ({a} : Finset ℕ).erase t = {a} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_singleton]; omega
        have hR : ({a, a + 1} : Finset ℕ).erase t = {a, a + 1} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        rw [hL, hR, if_neg h2, one_mul, Finset.prod_singleton,
          Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
        simp only [Nat.cast_add, Nat.cast_one]
        have hneg1 : (t : ℝ) - (a : ℝ) < 0 := sub_neg.mpr (Nat.cast_lt.mpr hlt)
        have hneg2 : (t : ℝ) - ((a : ℝ) + 1) < 0 := by linarith
        rw [abs_of_neg hneg1, abs_of_neg hneg2]
        have hsq : ((t : ℝ) - (a : ℝ)) ^ 2 = ((a : ℝ) - (t : ℝ)) * ((a : ℝ) - (t : ℝ)) := by ring
        have hprod : -((t : ℝ) - (a : ℝ)) * -((t : ℝ) - ((a : ℝ) + 1)) =
            ((a : ℝ) - (t : ℝ)) * ((a : ℝ) - (t : ℝ) + 1) := by ring
        rw [hsq, hprod]
        exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

private lemma rootSetP_even_bound (j t : ℕ) :
    (∏ u ∈ (rootSetP (2 * j)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
        (∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) := by
  induction j with
  | zero => simp [rootSetP]
  | succ j ih =>
    have hIcc : Finset.Icc 1 (4 * (j + 1)) =
        Finset.Icc 1 (4 * j) ∪ {4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    have hdisj_Icc : Disjoint (Finset.Icc 1 (4 * j)) {4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2; omega
    have hP : rootSetP (2 * (j + 1)) = rootSetP (2 * j) ∪ {4 * j + 1, 4 * j + 4} := by
      ext x
      simp only [Finset.mem_union, rootSetP, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    have hdisj_P : Disjoint (rootSetP (2 * j)) {4 * j + 1, 4 * j + 4} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      omega
    rw [hP, prod_erase_union hdisj_P, hIcc, prod_erase_union hdisj_Icc]
    have hb4 := block4_ineq (4 * j + 1) t
    have h4a : 4 * j + 1 + 1 = 4 * j + 2 := by omega
    have h4b : 4 * j + 1 + 2 = 4 * j + 3 := by omega
    have h4c : 4 * j + 1 + 3 = 4 * j + 4 := by omega
    rw [h4a, h4b, h4c] at hb4
    have hmul := mul_le_mul ih hb4 (Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hfac : (if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
          (if t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ) then (2 : ℝ) else 1) =
        if t ∈ Finset.Icc 1 (4 * j) ∪ {4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} then (2 : ℝ) else 1 := by
      simp only [Finset.mem_union]
      by_cases hA : t ∈ Finset.Icc 1 (4 * j) <;>
        by_cases hB : t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ)
      · exfalso; exact Finset.disjoint_left.mp hdisj_Icc hA hB
      · rw [if_pos hA, if_neg hB, if_pos (Or.inl hA), mul_one]
      · rw [if_neg hA, if_pos hB, if_pos (Or.inr hB), one_mul]
      · rw [if_neg hA, if_neg hB, if_neg (fun h => h.elim hA hB), one_mul]
    calc (∏ u ∈ (rootSetP (2 * j)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) *
          ∏ u ∈ ({4 * j + 1, 4 * j + 4} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2
        ≤ ((if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
            ∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
          ((if t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ) then (2 : ℝ) else 1) *
            ∏ u ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := hmul
      _ = ((if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
            (if t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ) then (2 : ℝ) else 1)) *
          ((∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by ring
      _ = _ := by rw [hfac]

lemma rootSetP_bound (l t : ℕ) (ht : t ≤ 2 * l + 1) :
    (∏ u ∈ (rootSetP l).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤ 2 * compProd (2 * l) t := by
  rcases Nat.even_or_odd l with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h := rootSetP_even_bound j t
    have heq : j + j = 2 * j := by omega
    rw [heq]
    have h2 : (if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) ≤ 2 := by split_ifs <;> norm_num
    have hnn : 0 ≤ ∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)| :=
      Finset.prod_nonneg fun _ _ => abs_nonneg _
    have hc : 2 * (2 * j) = 4 * j := by omega
    unfold compProd; rw [hc]
    exact h.trans (mul_le_mul_of_nonneg_right h2 hnn)
  · have hIcc : Finset.Icc 1 (2 * (2 * j + 1)) = Finset.Icc 1 (4 * j) ∪ {4 * j + 1, 4 * j + 2} := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    have hdisj_Icc : Disjoint (Finset.Icc 1 (4 * j)) {4 * j + 1, 4 * j + 2} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2; omega
    have hP : rootSetP (2 * j + 1) = rootSetP (2 * j) ∪ {4 * j + 1} := by
      ext x
      simp only [Finset.mem_union, rootSetP, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      omega
    have hdisj_P : Disjoint (rootSetP (2 * j)) {4 * j + 1} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton] at hx1 hx2; omega
    unfold compProd
    rw [hP, prod_erase_union hdisj_P, hIcc, prod_erase_union hdisj_Icc]
    have h1 := rootSetP_even_bound j t
    have h2 := pair2Right_ineq (4 * j + 1) t (by omega)
    have h2a : 4 * j + 1 + 1 = 4 * j + 2 := by omega
    have h2b : 4 * j + 1 + 2 = 4 * j + 3 := by omega
    rw [h2a, h2b] at h2
    have hmul := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hfac : (if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
          (if t = 4 * j + 3 then (2 : ℝ) else 1) ≤ 2 := by
      by_cases hA : t ∈ Finset.Icc 1 (4 * j) <;> by_cases hB : t = 4 * j + 3
      · exfalso; simp only [Finset.mem_Icc] at hA; omega
      · rw [if_pos hA, if_neg hB, mul_one]
      · rw [if_neg hA, if_pos hB, one_mul]
      · rw [if_neg hA, if_neg hB, mul_one]; norm_num
    have hnn : 0 ≤ (∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
        ∏ u ∈ ({4 * j + 1, 4 * j + 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)| :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    calc (∏ u ∈ (rootSetP (2 * j)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) *
          ∏ u ∈ ({4 * j + 1} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2
        ≤ ((if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
            (if t = 4 * j + 3 then (2 : ℝ) else 1)) *
          ((∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j + 1, 4 * j + 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) :=
          hmul.trans_eq (by ring)
      _ ≤ 2 * ((∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j + 1, 4 * j + 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) :=
          mul_le_mul_of_nonneg_right hfac hnn

private lemma rootSetQ_odd_bound (j t : ℕ) :
    (∏ u ∈ (rootSetQ (2 * j + 1)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t ∈ insert 0 (Finset.Icc 3 (4 * j + 2)) then (2 : ℝ) else 1) *
        (∏ u ∈ (Finset.Icc 1 (4 * j + 2)).erase t, |(t : ℝ) - (u : ℝ)|) := by
  induction j with
  | zero =>
    have hQ : rootSetQ 1 = {2} := by
      ext x; simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]; omega
    have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
    have hins : insert 0 (Finset.Icc 3 2) = {0} := by decide
    rw [hQ, hIcc, hins]
    have hp := pair2Left_ineq t
    have hmem : (t ∈ ({0} : Finset ℕ)) ↔ t = 0 := Finset.mem_singleton
    simp only [hmem]
    exact hp
  | succ j ih =>
    have hIcc : Finset.Icc 1 (4 * (j + 1) + 2) =
        Finset.Icc 1 (4 * j + 2) ∪ {4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    have hdisj_Icc : Disjoint (Finset.Icc 1 (4 * j + 2)) {4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2; omega
    have hQ : rootSetQ (2 * (j + 1) + 1) = rootSetQ (2 * j + 1) ∪ {4 * j + 3, 4 * j + 6} := by
      ext x
      simp only [Finset.mem_union, rootSetQ, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    have hdisj_Q : Disjoint (rootSetQ (2 * j + 1)) {4 * j + 3, 4 * j + 6} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      omega
    rw [hQ, prod_erase_union hdisj_Q, hIcc, prod_erase_union hdisj_Icc]
    have hb4 := block4_ineq (4 * j + 3) t
    have h4a : 4 * j + 3 + 1 = 4 * j + 4 := by omega
    have h4b : 4 * j + 3 + 2 = 4 * j + 5 := by omega
    have h4c : 4 * j + 3 + 3 = 4 * j + 6 := by omega
    rw [h4a, h4b, h4c] at hb4
    have hmul := mul_le_mul ih hb4 (Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hfac : (if t ∈ insert 0 (Finset.Icc 3 (4 * j + 2)) then (2 : ℝ) else 1) *
          (if t ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ) then (2 : ℝ) else 1) =
        if t ∈ insert 0 (Finset.Icc 3 (4 * (j + 1) + 2)) then (2 : ℝ) else 1 := by
      have hU : insert 0 (Finset.Icc 3 (4 * (j + 1) + 2)) =
          insert 0 (Finset.Icc 3 (4 * j + 2)) ∪ {4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} := by
        ext x; simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
      have hdisjU : Disjoint (insert 0 (Finset.Icc 3 (4 * j + 2))) {4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_singleton] at hx1 hx2; omega
      simp only [hU, Finset.mem_union]
      by_cases hA : t ∈ insert 0 (Finset.Icc 3 (4 * j + 2)) <;>
        by_cases hB : t ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ)
      · exfalso; exact Finset.disjoint_left.mp hdisjU hA hB
      · rw [if_pos hA, if_neg hB, if_pos (Or.inl hA), mul_one]
      · rw [if_neg hA, if_pos hB, if_pos (Or.inr hB), one_mul]
      · rw [if_neg hA, if_neg hB, if_neg (fun h => h.elim hA hB), one_mul]
    calc (∏ u ∈ (rootSetQ (2 * j + 1)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) *
          ∏ u ∈ ({4 * j + 3, 4 * j + 6} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2
        ≤ ((if t ∈ insert 0 (Finset.Icc 3 (4 * j + 2)) then (2 : ℝ) else 1) *
            (if t ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ) then (2 : ℝ) else 1)) *
          ((∏ u ∈ (Finset.Icc 1 (4 * j + 2)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) :=
          hmul.trans_eq (by ring)
      _ = _ := by rw [hfac]

lemma rootSetQ_bound (l t : ℕ) (hl : 1 ≤ l) (ht : t ≤ 2 * l + 1) :
    (∏ u ∈ (rootSetQ l).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤ 2 * compProd (2 * l) t := by
  rcases Nat.even_or_odd l with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hj0 : j ≠ 0 := by omega
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have hl_eq : l = 2 * j' + 2 := by omega
    rw [hl_eq] at ht ⊢
    have hIcc : Finset.Icc 1 (2 * (2 * j' + 2)) = Finset.Icc 1 (4 * j' + 2) ∪ {4 * j' + 3, 4 * j' + 4} := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    have hdisj_Icc : Disjoint (Finset.Icc 1 (4 * j' + 2)) {4 * j' + 3, 4 * j' + 4} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2; omega
    have hQ : rootSetQ (2 * j' + 2) = rootSetQ (2 * j' + 1) ∪ {4 * j' + 3} := by
      ext x
      simp only [Finset.mem_union, rootSetQ, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      omega
    have hdisj_Q : Disjoint (rootSetQ (2 * j' + 1)) {4 * j' + 3} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton] at hx1 hx2; omega
    unfold compProd
    rw [hQ, prod_erase_union hdisj_Q, hIcc, prod_erase_union hdisj_Icc]
    have h1 := rootSetQ_odd_bound j' t
    have h2 := pair2Right_ineq (4 * j' + 3) t (by omega)
    have h2a : 4 * j' + 3 + 1 = 4 * j' + 4 := by omega
    have h2b : 4 * j' + 3 + 2 = 4 * j' + 5 := by omega
    rw [h2a, h2b] at h2
    have hmul := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hfac : (if t ∈ insert 0 (Finset.Icc 3 (4 * j' + 2)) then (2 : ℝ) else 1) *
          (if t = 4 * j' + 5 then (2 : ℝ) else 1) ≤ 2 := by
      by_cases hA : t ∈ insert 0 (Finset.Icc 3 (4 * j' + 2)) <;> by_cases hB : t = 4 * j' + 5
      · exfalso; simp only [Finset.mem_insert, Finset.mem_Icc] at hA; omega
      · rw [if_pos hA, if_neg hB, mul_one]
      · rw [if_neg hA, if_pos hB, one_mul]
      · rw [if_neg hA, if_neg hB, mul_one]; norm_num
    have hnn : 0 ≤ (∏ u ∈ (Finset.Icc 1 (4 * j' + 2)).erase t, |(t : ℝ) - (u : ℝ)|) *
        ∏ u ∈ ({4 * j' + 3, 4 * j' + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)| :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    calc (∏ u ∈ (rootSetQ (2 * j' + 1)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) *
          ∏ u ∈ ({4 * j' + 3} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2
        ≤ ((if t ∈ insert 0 (Finset.Icc 3 (4 * j' + 2)) then (2 : ℝ) else 1) *
            (if t = 4 * j' + 5 then (2 : ℝ) else 1)) *
          ((∏ u ∈ (Finset.Icc 1 (4 * j' + 2)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j' + 3, 4 * j' + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) :=
          hmul.trans_eq (by ring)
      _ ≤ 2 * ((∏ u ∈ (Finset.Icc 1 (4 * j' + 2)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j' + 3, 4 * j' + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) :=
          mul_le_mul_of_nonneg_right hfac hnn
  · subst hj
    have h := rootSetQ_odd_bound j t
    have h2 : (if t ∈ insert 0 (Finset.Icc 3 (4 * j + 2)) then (2 : ℝ) else 1) ≤ 2 := by
      split_ifs <;> norm_num
    have hnn : 0 ≤ ∏ u ∈ (Finset.Icc 1 (4 * j + 2)).erase t, |(t : ℝ) - (u : ℝ)| :=
      Finset.prod_nonneg fun _ _ => abs_nonneg _
    have hc : 2 * (2 * j + 1) = 4 * j + 2 := by omega
    unfold compProd; rw [hc]
    exact h.trans (mul_le_mul_of_nonneg_right h2 hnn)

lemma pPolyRaw_eval_zero_sq_bounds (l : ℕ) (hl : 1 ≤ l) :
    ((2 * l).factorial : ℝ) / 2 ≤ ((pPolyRaw l).eval 0) ^ 2 ∧
      ((2 * l).factorial : ℝ) / 2 ≤ ((qPolyRaw l).eval 0) ^ 2 := by
  have hp0 : ((pPolyRaw l).eval 0) ^ 2 ≤ 2 * ((2 * l).factorial : ℝ) := by
    have hP := rootSetP_bound l 0 (by omega)
    have hnot : 0 ∉ rootSetP l := by
      simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [Finset.erase_eq_of_notMem hnot, compProd_zero] at hP
    unfold pPolyRaw
    rw [Polynomial.eval_prod, ← Finset.prod_pow]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_zero] at hP ⊢
    exact hP
  have hq0 : ((qPolyRaw l).eval 0) ^ 2 ≤ 2 * ((2 * l).factorial : ℝ) := by
    have hQ := rootSetQ_bound l 0 hl (by omega)
    have hnot : 0 ∉ rootSetQ l := by
      simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [Finset.erase_eq_of_notMem hnot, compProd_zero] at hQ
    unfold qPolyRaw
    rw [Polynomial.eval_prod, ← Finset.prod_pow]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_zero] at hQ ⊢
    exact hQ
  have hmul : ((pPolyRaw l).eval 0) ^ 2 * ((qPolyRaw l).eval 0) ^ 2 = (((2 * l).factorial : ℝ) ^ 2) := by
    calc ((pPolyRaw l).eval 0) ^ 2 * ((qPolyRaw l).eval 0) ^ 2
        = ((pPolyRaw l).eval 0 * (qPolyRaw l).eval 0) ^ 2 := by ring
      _ = ((2 * l).factorial : ℝ) ^ 2 := by rw [pPolyRaw_mul_qPolyRaw_eval_zero l]
  have hfac_pos : (0 : ℝ) < ((2 * l).factorial : ℝ) := by positivity
  have hp_pos : 0 < ((pPolyRaw l).eval 0) ^ 2 := sq_pos_of_ne_zero (pPolyRaw_eval_zero_ne l)
  have hq_pos : 0 < ((qPolyRaw l).eval 0) ^ 2 := sq_pos_of_ne_zero (qPolyRaw_eval_zero_ne l)
  constructor
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h1 := mul_le_mul_of_nonneg_left hq0 hp_pos.le
    rw [hmul, sq] at h1
    have h2 : ((2 * l).factorial : ℝ) * ((2 * l).factorial : ℝ) ≤
        ((pPolyRaw l).eval 0 ^ 2 * 2) * ((2 * l).factorial : ℝ) := by linarith
    exact le_of_mul_le_mul_right h2 hfac_pos
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h1 := mul_le_mul_of_nonneg_right hp0 hq_pos.le
    rw [hmul, sq] at h1
    have h2 : ((2 * l).factorial : ℝ) * ((2 * l).factorial : ℝ) ≤
        ((qPolyRaw l).eval 0 ^ 2 * 2) * ((2 * l).factorial : ℝ) := by linarith
    exact le_of_mul_le_mul_right h2 hfac_pos

lemma PPoly_sq_bound (l t : ℕ) (hl : 1 ≤ l) (ht : t ≤ 2 * l + 1) :
    ((PPoly l).eval (t : ℝ)) ^ 2 ≤ 2 * compProd (2 * l) t / ((2 * l).factorial : ℝ) := by
  by_cases hmem : t ∈ rootSetP l
  · rw [PPoly_eval_root hmem, zero_pow (by norm_num)]
    exact div_nonneg (mul_nonneg (by norm_num) (compProd_pos (2 * l) t).le) (by positivity)
  · have hP := rootSetP_bound l t ht
    rw [Finset.erase_eq_of_notMem hmem] at hP
    have hraw : ((pPolyRaw l).eval (t : ℝ)) ^ 2 ≤ 2 * compProd (2 * l) t := by
      unfold pPolyRaw
      rw [Polynomial.eval_prod, ← Finset.prod_pow]
      simpa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hP
    have h0 := (pPolyRaw_eval_zero_sq_bounds l hl).1
    have hden : ((2 * l).factorial : ℝ) ≤ 2 * ((pPolyRaw l).eval 0) ^ 2 := by linarith
    have hfac_pos : (0 : ℝ) < ((2 * l).factorial : ℝ) := by positivity
    have hsq : ((PPoly l).eval (t : ℝ)) ^ 2 = ((pPolyRaw l).eval (t : ℝ)) ^ 2 / (2 * ((pPolyRaw l).eval 0) ^ 2) := by
      unfold PPoly
      rw [Polynomial.eval_mul, Polynomial.eval_C, mul_pow]
      have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp [pPolyRaw_eval_zero_ne l]
      rw [hs]; ring
    rw [hsq]
    exact div_le_div₀ (mul_nonneg (by norm_num) (compProd_pos (2 * l) t).le) hraw hfac_pos hden

lemma QPoly_sq_bound (l t : ℕ) (hl : 1 ≤ l) (ht : t ≤ 2 * l + 1) :
    ((QPoly l).eval (t : ℝ)) ^ 2 ≤ 2 * compProd (2 * l) t / ((2 * l).factorial : ℝ) := by
  by_cases hmem : t ∈ rootSetQ l
  · rw [QPoly_eval_root hmem, zero_pow (by norm_num)]
    exact div_nonneg (mul_nonneg (by norm_num) (compProd_pos (2 * l) t).le) (by positivity)
  · have hQ := rootSetQ_bound l t hl ht
    rw [Finset.erase_eq_of_notMem hmem] at hQ
    have hraw : ((qPolyRaw l).eval (t : ℝ)) ^ 2 ≤ 2 * compProd (2 * l) t := by
      unfold qPolyRaw
      rw [Polynomial.eval_prod, ← Finset.prod_pow]
      simpa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hQ
    have h0 := (pPolyRaw_eval_zero_sq_bounds l hl).2
    have hden : ((2 * l).factorial : ℝ) ≤ 2 * ((qPolyRaw l).eval 0) ^ 2 := by linarith
    have hfac_pos : (0 : ℝ) < ((2 * l).factorial : ℝ) := by positivity
    have hsq : ((QPoly l).eval (t : ℝ)) ^ 2 = ((qPolyRaw l).eval (t : ℝ)) ^ 2 / (2 * ((qPolyRaw l).eval 0) ^ 2) := by
      unfold QPoly
      rw [Polynomial.eval_mul, Polynomial.eval_C, mul_pow]
      have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp [qPolyRaw_eval_zero_ne l]
      rw [hs]; ring
    rw [hsq]
    exact div_le_div₀ (mul_nonneg (by norm_num) (compProd_pos (2 * l) t).le) hraw hfac_pos hden

lemma PQ_pointwise_bound {l : ℕ} (hl : 1 ≤ l) (t : Fin (2 * l + 1 + 1)) :
    ((2 * l + 1).choose (t : ℕ) : ℝ) * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2) ≤
      16 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)) := by
  have ht : (t : ℕ) ≤ 2 * l + 1 := Nat.lt_succ_iff.mp t.isLt
  have hsum : ((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2 ≤
      4 * (compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ)) := by
    calc ((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2
        ≤ 2 * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ) +
          2 * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ) :=
          add_le_add (PPoly_sq_bound l t hl ht) (QPoly_sq_bound l t hl ht)
      _ = 4 * (compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ)) := by ring
  have hmul : ((2 * l + 1).choose (t : ℕ) : ℝ) * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2) ≤
      4 * (((2 * l + 1).choose (t : ℕ) : ℝ) * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ)) := by
    have hnn : 0 ≤ ((2 * l + 1).choose (t : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((2 * l + 1).choose (t : ℕ) : ℝ) * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2)
        ≤ ((2 * l + 1).choose (t : ℕ) : ℝ) * (4 * (compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum hnn
      _ = 4 * (((2 * l + 1).choose (t : ℕ) : ℝ) * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ)) := by ring
  have hch := choose_mul_compProd_le hl t
  calc ((2 * l + 1).choose (t : ℕ) : ℝ) * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2)
      ≤ 4 * (((2 * l + 1).choose (t : ℕ) : ℝ) * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ)) := hmul
    _ ≤ 4 * (4 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ))) :=
        mul_le_mul_of_nonneg_left hch (by norm_num)
    _ = 16 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)) := by ring

end KrawtchoukAndMod4

section TransducerAlgebra

noncomputable def pVal (m : ℕ) (t : Fin (2 * m + 2)) : ℝ :=
  (PPoly m).eval (t.1 : ℝ)

noncomputable def qVal (m : ℕ) (t : Fin (2 * m + 2)) : ℝ :=
  (QPoly m).eval (t.1 : ℝ)

noncomputable def aCoeff (m : ℕ) (t : Fin (2 * m + 2)) : ℝ :=
  ((-1 : ℝ) ^ t.1 * qVal m t - pVal m t) / Real.sqrt 2

noncomputable def bCoeff (m : ℕ) (t : Fin (2 * m + 2)) : ℝ :=
  (pVal m t + (-1 : ℝ) ^ t.1 * qVal m t) / Real.sqrt 2

noncomputable def LVal (m : ℕ) (a : Fin (2 * m + 2)) : ℝ :=
  ∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t a : ℝ) * pVal m t

noncomputable def UVal (m : ℕ) (a : Fin (2 * m + 2)) : ℝ :=
  ∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t a : ℝ) * ((-1 : ℝ) ^ t.1 * qVal m t)

lemma LVal_zero_of_gt {m : ℕ} {a : Fin (2 * m + 2)} (ha : m < a.1) : LVal m a = 0 :=
  L_vanish_of_gt m (PPoly m) (PPoly_deg m) a ha

lemma UVal_zero_of_le {m : ℕ} {a : Fin (2 * m + 2)} (ha : a.1 ≤ m) : UVal m a = 0 :=
  U_vanish_of_le m (QPoly m) (QPoly_deg m) a ha

lemma aCoeff_zero (m : ℕ) : aCoeff m 0 = 0 := by
  simp [aCoeff, pVal, qVal, PPoly_eval_zero, QPoly_eval_zero]

lemma bCoeff_zero (m : ℕ) : bCoeff m 0 = 1 := by
  simp only [bCoeff, Fin.val_zero, pow_zero, one_mul, pVal, qVal, Nat.cast_zero]
  rw [PPoly_eval_zero, QPoly_eval_zero]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hs]
  linarith

lemma abCoeff_interior_even (m : ℕ) (t : Fin (2 * m + 2)) (ht1 : 1 ≤ t.1) (ht2 : t.1 ≤ 2 * m)
    (hbit : t.1.testBit 1 = false) : aCoeff m t = bCoeff m t := by
  have hmod : t.1 % 4 = 0 ∨ t.1 % 4 = 1 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hbit
    simp only [pow_one, decide_eq_false_iff_not] at hbit
    omega
  have hmem : t.1 ∈ rootSetP m := by
    simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨ht1, ht2⟩, hmod⟩
  have hp0 : pVal m t = 0 := PPoly_eval_root hmem
  simp [aCoeff, bCoeff, hp0]

lemma abCoeff_interior_odd (m : ℕ) (t : Fin (2 * m + 2)) (ht1 : 1 ≤ t.1) (ht2 : t.1 ≤ 2 * m)
    (hbit : t.1.testBit 1 = true) : bCoeff m t = -aCoeff m t := by
  have hmod : t.1 % 4 = 2 ∨ t.1 % 4 = 3 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hbit
    simp only [pow_one, decide_eq_true_eq] at hbit
    omega
  have hmem : t.1 ∈ rootSetQ m := by
    simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨ht1, ht2⟩, hmod⟩
  have hq0 : qVal m t = 0 := QPoly_eval_root hmem
  simp [aCoeff, bCoeff, hq0]
  ring

lemma aCoeff_top_sq_sub_bCoeff_top_sq (m : ℕ) :
    (aCoeff m ⟨2 * m + 1, by omega⟩) ^ 2 - (bCoeff m ⟨2 * m + 1, by omega⟩) ^ 2 = 1 := by
  have hpow : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  have hmul := PPoly_mul_QPoly_eval_top m
  simp only [aCoeff, bCoeff, pVal, qVal, hpow]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hsne]
  rw [hs]
  linarith [hmul]

lemma aCoeff_top_ne_zero (m : ℕ) : aCoeff m ⟨2 * m + 1, by omega⟩ ≠ 0 := by
  intro h0
  have h := aCoeff_top_sq_sub_bCoeff_top_sq m
  rw [h0, zero_pow (by norm_num), zero_sub] at h
  nlinarith [sq_nonneg (bCoeff m ⟨2 * m + 1, by omega⟩)]

noncomputable def U_k_mat (m : ℕ) : Matrix Bool Bool ℂ :=
  let a : ℂ := (aCoeff m ⟨2 * m + 1, by omega⟩ : ℂ)
  let b : ℂ := (bCoeff m ⟨2 * m + 1, by omega⟩ : ℂ)
  Matrix.of fun row col =>
    match row, col with
    | false, false => b / a
    | false, true  => 1 / a
    | true, false  => -1 / a
    | true, true   => b / a

lemma U_k_mat_mem_unitaryGroup (m : ℕ) : U_k_mat m ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have ha_real : aCoeff m ⟨2 * m + 1, by omega⟩ ≠ 0 := aCoeff_top_ne_zero m
  have hsq_real : (aCoeff m ⟨2 * m + 1, by omega⟩) ^ 2 =
      (bCoeff m ⟨2 * m + 1, by omega⟩) ^ 2 + 1 := by
    linarith [aCoeff_top_sq_sub_bCoeff_top_sq m]
  have ha : (aCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha_real
  have hsq : (aCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) ^ 2 =
      (bCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) ^ 2 + 1 := by
    exact_mod_cast hsq_real
  ext row col
  cases row <;> cases col <;>
    simp only [U_k_mat, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Fintype.sum_bool,
      Matrix.one_apply, RCLike.star_def, map_div₀, map_one, map_neg, Complex.conj_ofReal,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
  · field_simp [ha]; linear_combination -hsq
  · field_simp [ha]; ring
  · field_simp [ha]; ring
  · field_simp [ha]; linear_combination -hsq

lemma U_k_mat_act_ket_true (m : ℕ) :
    act (U_k_mat m) ((aCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) • ket true) =
      ket false + (bCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) • ket true := by
  have ha : (aCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (aCoeff_top_ne_zero m)
  ext row
  cases row <;>
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Fintype.sum_bool, U_k_mat,
      Matrix.of_apply, ket, PiLp.single_apply, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false, mul_zero,
      zero_add, add_zero, mul_one]
  · field_simp [ha]
  · field_simp [ha]

noncomputable def U_op (m t : ℕ) : Matrix Bool Bool ℂ :=
  if t = 0 then pauliX
  else if t = 2 * m + 1 then U_k_mat m
  else if t.testBit 1 then pauliZ
  else 1

lemma pauliZ_mul_pauliZ : pauliZ * pauliZ = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_bool, pauliZ, Matrix.diagonal_apply]
  cases a <;> cases b <;> norm_num

lemma pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, pauliX,
    Matrix.of_apply]
  cases a <;> cases b <;> norm_num

lemma pauliZ_mem_unitaryGroup : pauliZ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, pauliZ,
    Matrix.diagonal_apply]
  cases a <;> cases b <;> norm_num

lemma U_op_eq_three_gates (m t : ℕ) (_hm : 1 ≤ m) :
    U_op m t =
      (if t = 2 * m + 1 then U_k_mat m * (if (2 * m + 1).testBit 1 then pauliZ else 1) else 1) *
      (if t.testBit 1 then pauliZ else 1) *
      (if t = 0 then pauliX else 1) := by
  by_cases ht0 : t = 0
  · subst ht0
    simp [U_op]
  · by_cases htk : t = 2 * m + 1
    · subst htk
      simp only [U_op, ht0, ↓reduceIte, mul_one]
      by_cases hb : (2 * m + 1).testBit 1 = true
      · simp [hb, Matrix.mul_assoc, pauliZ_mul_pauliZ]
      · simp [hb]
    · simp [U_op, ht0, htk]

lemma act_pauliX_ket_false : act pauliX (ket false) = ket true := by
  ext a; cases a <;> simp [act, pauliX, ket]

lemma act_pauliZ_ket_true : act pauliZ (ket true) = -ket true := by
  ext a; cases a <;> simp [act, pauliZ, ket]

lemma act_one_vec {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  ext y; simp [act]

lemma act_add {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act U (ψ + φ) = act U ψ + act U φ := by
  ext y; simp [act, Matrix.mulVec_add]

lemma act_smul {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act U (c • ψ) = c • act U ψ := by
  ext y; simp [act, Matrix.mulVec_smul]

lemma act_sum {ι κ : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ ι) :
    act U (∑ x ∈ s, f x) = ∑ x ∈ s, act U (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext y; simp [act]
  | insert a s ha ih => rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext y; simp [act, Matrix.mulVec_mulVec]

noncomputable def wCatVec (n m : ℕ) (A : Finset (Fin n)) (hA : A.card = 2 * m + 1) :
    EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun S : Qubits n =>
    (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
      ∑ t : Fin (2 * m + 2),
        (krawtchouk (2 * m + 1) t (intersectionIndex ⟨A, hA⟩ S) : ℂ) * (bCoeff m t : ℂ)

noncomputable def wCatAfter (n m : ℕ) (A : Finset (Fin n)) (hA : A.card = 2 * m + 1) :
    EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun S : Qubits n =>
    (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
      ∑ t : Fin (2 * m + 2),
        (krawtchouk (2 * m + 1) t (intersectionIndex ⟨A, hA⟩ S) : ℂ) * (aCoeff m t : ℂ)

lemma wCatVec_energy_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n m : ℕ), 1 ≤ m → 2 * m + 1 ≤ n →
      ∀ (A : Finset (Fin n)) (hA : A.card = 2 * m + 1),
      ‖wCatVec n m A hA‖ ^ 2 ≤ C₀ * Real.log (2 * m + 1 : ℕ) := by
  obtain ⟨H, hH_pos, hH⟩ := pointwise_correction_bound_to_log_energy
  refine ⟨8 * H, by positivity, ?_⟩
  intro n m hm hle A hA
  let Aex : ExactSupports n (2 * m + 1) := ⟨A, hA⟩
  have hnorm_sq : ‖wCatVec n m A hA‖ ^ 2 =
      (2 : ℝ) ^ (-(n : ℤ)) * ∑ S : Qubits n,
        ((LVal m (intersectionIndex Aex S) + UVal m (intersectionIndex Aex S)) / Real.sqrt 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hcoeff : ∀ S : Qubits n,
        ‖wCatVec n m A hA S‖ ^ 2 =
          (2 : ℝ) ^ (-(n : ℤ)) *
            ((LVal m (intersectionIndex Aex S) + UVal m (intersectionIndex Aex S)) / Real.sqrt 2) ^ 2 := by
      intro S
      have hreal_sum : (∑ t : Fin (2 * m + 2),
            (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℝ) * bCoeff m t) =
          (LVal m (intersectionIndex Aex S) + UVal m (intersectionIndex Aex S)) / Real.sqrt 2 := by
        simp only [LVal, UVal, bCoeff]
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
      have hsum_cast : (∑ t : Fin (2 * m + 2),
            (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (bCoeff m t : ℂ)) =
          (((LVal m (intersectionIndex Aex S) + UVal m (intersectionIndex Aex S)) / Real.sqrt 2 : ℝ) : ℂ) := by
        rw [← hreal_sum]
        push_cast
        rfl
      have hscale : (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
            (((LVal m (intersectionIndex Aex S) + UVal m (intersectionIndex Aex S)) / Real.sqrt 2 : ℝ) : ℂ) =
          ((((Real.sqrt 2)⁻¹ ^ n : ℝ) *
            ((LVal m (intersectionIndex Aex S) + UVal m (intersectionIndex Aex S)) / Real.sqrt 2) : ℝ) : ℂ) := by
        push_cast; rfl
      simp only [wCatVec]
      change ‖(((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
          ∑ t : Fin (2 * m + 2),
            (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (bCoeff m t : ℂ)‖ ^ 2 = _
      rw [hsum_cast, hscale, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
      have h2 : ((Real.sqrt 2)⁻¹ ^ n) ^ 2 = (2 : ℝ) ^ (-(n : ℤ)) := by
        rw [← pow_mul, mul_comm n 2, pow_mul, inv_pow, Real.sq_sqrt (by norm_num),
          zpow_neg, zpow_natCast, inv_pow]
      rw [h2]
    simp_rw [hcoeff, ← Finset.mul_sum]
  have hdisj : ∀ a : Fin (2 * m + 2),
      ((LVal m a + UVal m a) / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) * (LVal m a ^ 2 + UVal m a ^ 2) := by
    intro a
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    by_cases ha : a.1 ≤ m
    · rw [UVal_zero_of_le ha, add_zero, div_pow, hs]; ring
    · rw [LVal_zero_of_gt (Nat.lt_of_not_ge ha), zero_add, div_pow, hs]; ring
  rw [hnorm_sq]
  simp_rw [hdisj, ← Finset.mul_sum]
  have hmul1 : (2 : ℝ) ^ (-(n : ℤ)) * ((1 / 2 : ℝ) *
        ∑ S : Qubits n, (LVal m (intersectionIndex Aex S) ^ 2 + UVal m (intersectionIndex Aex S) ^ 2)) =
      (1 / 2 : ℝ) * ((2 : ℝ) ^ (-(n : ℤ)) *
        ∑ S : Qubits n, (LVal m (intersectionIndex Aex S) ^ 2 + UVal m (intersectionIndex Aex S) ^ 2)) := by
    ring
  rw [hmul1, normalized_intersection_sum n (2 * m + 1) hle Aex (fun a => LVal m a ^ 2 + UVal m a ^ 2)]
  have hparseval := lemma_4_2_two_channel (2 * m + 1) (pVal m) (qVal m)
  dsimp only at hparseval
  have hLU : (1 / (2 : ℝ) ^ (2 * m + 1)) *
      ∑ a : Fin (2 * m + 2), ((2 * m + 1).choose a : ℝ) * (LVal m a ^ 2 + UVal m a ^ 2) =
      ∑ t : Fin (2 * m + 2), ((2 * m + 1).choose t : ℝ) * (pVal m t ^ 2 + qVal m t ^ 2) := hparseval
  rw [hLU]
  have hpt : ∀ t : Fin (2 * m + 2),
      ((2 * m + 1).choose (t : ℕ) : ℝ) * (pVal m t ^ 2 + qVal m t ^ 2) ≤
        16 * ((2 * m + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * m + 1) - (t : ℕ) + 1 : ℕ)) :=
    fun t => PQ_pointwise_bound hm t
  have hsum_le := hH (2 * m + 1) (by omega) 16 (by norm_num)
    (fun t => ((2 * m + 1).choose (t : ℕ) : ℝ) * (pVal m t ^ 2 + qVal m t ^ 2)) hpt
  calc (1 / 2 : ℝ) * ∑ t : Fin (2 * m + 2), ((2 * m + 1).choose (t : ℕ) : ℝ) * (pVal m t ^ 2 + qVal m t ^ 2)
      ≤ (1 / 2 : ℝ) * (16 * H * Real.log ((2 * m + 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsum_le (by norm_num)
    _ = 8 * H * Real.log (2 * m + 1 : ℕ) := by ring

noncomputable def phaseMaj {n : ℕ} (A : Finset (Fin n)) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.diagonal fun S => if majorityBit A S then (-1 : ℂ) else 1

lemma act_phaseMaj_wCatVec {n m : ℕ} (A : Finset (Fin n)) (hA : A.card = 2 * m + 1) :
    act (phaseMaj A) (wCatVec n m A hA) = wCatAfter n m A hA := by
  let Aex : ExactSupports n (2 * m + 1) := ⟨A, hA⟩
  ext S
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, phaseMaj, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single S]
  · simp only [↓reduceIte]
    change (if majorityBit A S then (-1 : ℂ) else 1) *
        ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
          ∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (bCoeff m t : ℂ)) =
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
        ∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (aCoeff m t : ℂ)
    have hb_eq : (∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℝ) * bCoeff m t) =
        (LVal m (intersectionIndex Aex S) + UVal m (intersectionIndex Aex S)) / Real.sqrt 2 := by
      simp only [LVal, UVal, bCoeff, ← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun t _ => by ring
    have ha_eq : (∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℝ) * aCoeff m t) =
        (UVal m (intersectionIndex Aex S) - LVal m (intersectionIndex Aex S)) / Real.sqrt 2 := by
      simp only [LVal, UVal, aCoeff, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun t _ => by ring
    have hmaj : majorityBit A S = true ↔ (intersectionIndex Aex S : ℕ) ≤ m := by
      simp only [majorityBit, intersectionIndex, Aex, hA, decide_eq_true_eq]
      omega
    have hsign_real : (if majorityBit A S then (-1 : ℝ) else 1) *
          ((LVal m (intersectionIndex Aex S) + UVal m (intersectionIndex Aex S)) / Real.sqrt 2) =
        (UVal m (intersectionIndex Aex S) - LVal m (intersectionIndex Aex S)) / Real.sqrt 2 := by
      by_cases hle : (intersectionIndex Aex S : ℕ) ≤ m
      · have hm : majorityBit A S = true := hmaj.mpr hle
        rw [if_pos hm, UVal_zero_of_le hle]; ring
      · have hgt : m < (intersectionIndex Aex S : ℕ) := Nat.lt_of_not_ge hle
        have hm : majorityBit A S = false := Bool.eq_false_iff.mpr fun h => hle (hmaj.mp h)
        rw [if_neg (by simp [hm]), LVal_zero_of_gt hgt]; ring
    have hsign : (if majorityBit A S then (-1 : ℂ) else 1) *
          ∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (bCoeff m t : ℂ) =
        ∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (aCoeff m t : ℂ) := by
      have hc1 : (∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (bCoeff m t : ℂ)) =
          (((LVal m (intersectionIndex Aex S) + UVal m (intersectionIndex Aex S)) / Real.sqrt 2 : ℝ) : ℂ) := by
        rw [← hb_eq]; push_cast; rfl
      have hc2 : (∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (aCoeff m t : ℂ)) =
          (((UVal m (intersectionIndex Aex S) - LVal m (intersectionIndex Aex S)) / Real.sqrt 2 : ℝ) : ℂ) := by
        rw [← ha_eq]; push_cast; rfl
      rw [hc1, hc2]
      by_cases hm : majorityBit A S = true
      · simp only [hm, ↓reduceIte] at hsign_real ⊢
        exact_mod_cast hsign_real
      · have hmf : majorityBit A S = false := Bool.eq_false_iff.mpr hm
        simp only [hmf, Bool.false_eq_true, ↓reduceIte] at hsign_real ⊢
        exact_mod_cast hsign_real
    calc (if majorityBit A S then (-1 : ℂ) else 1) *
          ((((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
            ∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (bCoeff m t : ℂ))
        = (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
            ((if majorityBit A S then (-1 : ℂ) else 1) *
              ∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (bCoeff m t : ℂ)) := by ring
      _ = _ := by rw [hsign]
  · intro z _ hz; simp [hz.symm]
  · simp

private lemma hadamardN_mul_self (n : ℕ) : hadamardN n * hadamardN n = 1 := by
  ext y z
  have h2 : (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) =
      ((2 : ℂ)⁻¹) ^ n := by
    rw [← Complex.ofReal_mul, ← sq, ← pow_mul, mul_comm n 2, pow_mul, inv_pow,
      Real.sq_sqrt (by norm_num)]
    push_cast
    rfl
  have hdot : ∀ i : Qubits n, xor (dotBits i y) (dotBits i z) = dotBits i (y + z) := by
    intro i
    simp only [dotBits]
    change (∑ k, (i k && y k)) + (∑ k, (i k && z k)) = ∑ k, (i k && (y + z) k)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.add_apply]
    cases i k <;> cases y k <;> cases z k <;> rfl
  have hsum : ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) =
      if y = z then (2 ^ n : ℂ) else 0 := by
    by_cases hyz : y = z
    · subst hyz
      have h0 : ∀ k, (y + y) k = false := fun k => by simp only [Pi.add_apply]; cases y k <;> rfl
      have hdot0 : ∀ i : Qubits n, dotBits i (y + y) = false := fun i => by
        simp only [dotBits, h0, Bool.and_false]
        exact (Finset.sum_const_zero (s := Finset.univ) : (∑ _ : Fin n, (0 : Bool)) = 0)
      simp [hdot0]
    · rw [if_neg hyz]
      have hne : ∃ r : Fin n, (y + z) r = true := by
        by_contra hc
        push Not at hc
        apply hyz
        funext r
        have hr := hc r
        revert hr
        simp only [Pi.add_apply]
        cases y r <;> cases z r <;> decide
      obtain ⟨r, hr⟩ := hne
      let flip : Qubits n ≃ Qubits n :=
        { toFun := fun i => Function.update i r (!(i r))
          invFun := fun i => Function.update i r (!(i r))
          left_inv := fun i => by funext k; by_cases hk : k = r <;> simp [Function.update, hk]
          right_inv := fun i => by funext k; by_cases hk : k = r <;> simp [Function.update, hk] }
      have hflip : ∀ i : Qubits n, dotBits (flip i) (y + z) = !(dotBits i (y + z)) := by
        intro i
        simp only [dotBits]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r),
          ← Finset.add_sum_erase (Finset.univ) (fun k => i k && (y + z) k) (Finset.mem_univ r)]
        have hrest : ∑ k ∈ Finset.univ.erase r, (flip i k && (y + z) k) =
            ∑ k ∈ Finset.univ.erase r, (i k && (y + z) k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkr : k ≠ r := (Finset.mem_erase.mp hk).1
          simp [flip, Function.update_of_ne hkr]
        rw [hrest]
        have hhead : (flip i r && (y + z) r) = !(i r && (y + z) r) := by
          simp [flip, hr]
        rw [hhead]
        cases (i r && (y + z) r) <;> cases (∑ k ∈ Finset.univ.erase r, (i k && (y + z) k)) <;> decide
      have hpair : ∑ i : Qubits n, (if dotBits (flip i) (y + z) then (-1 : ℂ) else 1) =
          ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) :=
        Fintype.sum_equiv flip _ _ fun _ => rfl
      have hneg : ∑ i : Qubits n, (if dotBits (flip i) (y + z) then (-1 : ℂ) else 1) =
          - ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hflip i]
        cases dotBits i (y + z) <;> simp
      have h2s : (2 : ℂ) * ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) = 0 := by
        calc (2 : ℂ) * ∑ i : Qubits n, _
            = ∑ i : Qubits n, _ + ∑ i : Qubits n, _ := two_mul _
          _ = ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) +
              ∑ i : Qubits n, (if dotBits (flip i) (y + z) then (-1 : ℂ) else 1) := by rw [hpair]
          _ = 0 := by rw [hneg, add_neg_cancel]
      exact (mul_eq_zero.mp h2s).resolve_left (by norm_num)
  simp only [Matrix.mul_apply, hadamardN, Matrix.of_apply, Matrix.one_apply]
  have hterm : ∀ i : Qubits n,
      (if dotBits i y then -(((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) else (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ)) *
      (if dotBits z i then -(((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) else (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ)) =
      ((2 : ℂ)⁻¹) ^ n * (if dotBits i (y + z) then (-1 : ℂ) else 1) := by
    intro i
    have hdz : dotBits z i = dotBits i z := by simp only [dotBits, Bool.and_comm]
    rw [hdz, ← hdot i]
    cases dotBits i y <;> cases dotBits i z <;> simp [← h2]
  simp_rw [hterm, ← Finset.mul_sum, hsum]
  by_cases hyz : y = z
  · simp [hyz, inv_pow, pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0)]
  · simp [hyz]

lemma hadamardN_mem_unitaryGroup (n : ℕ) :
    hadamardN n ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, hadamardN_star, hadamardN_mul_self]

noncomputable def uniformSubsetKet (n : ℕ) (A : Finset (Fin n)) (t : ℕ) :
    EuclideanSpace ℂ (Qubits n) :=
  ∑ T ∈ A.powersetCard t, ket (fun i : Fin n => decide (i ∈ T))

lemma uniformSubsetKet_zero (n : ℕ) (A : Finset (Fin n)) :
    uniformSubsetKet n A 0 = zeroKet n := by
  simp [uniformSubsetKet, zeroKet, Finset.powersetCard_zero]

lemma uniformSubsetKet_self {n : ℕ} (A : Finset (Fin n)) :
    uniformSubsetKet n A A.card = ket (fun i : Fin n => decide (i ∈ A)) := by
  simp [uniformSubsetKet, Finset.powersetCard_self]

private lemma dotBits_indicator_eq_bool_sum {n : ℕ} (T : Finset (Fin n)) (S : Qubits n) :
    (if dotBits (fun i => decide (i ∈ T)) S then (-1 : ℂ) else 1) =
      (-1 : ℂ) ^ ((T.filter fun i => S i).card) := by
  have hsum : dotBits (fun i => decide (i ∈ T)) S =
      decide (Odd ((T.filter fun i => S i).card)) := by
    unfold dotBits
    have hbool : ∀ (s : Finset (Fin n)),
        (∑ k ∈ s, (decide (k ∈ T) && S k)) = decide (Odd ((s.filter fun k => k ∈ T ∧ S k = true).card)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => rfl
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, ih]
        by_cases hcond : a ∈ T ∧ S a = true
        · have hnot : a ∉ s.filter (fun k => k ∈ T ∧ S k = true) := fun h => ha (Finset.mem_filter.mp h).1
          rw [Finset.filter_insert, if_pos hcond, Finset.card_insert_of_notMem hnot]
          have hbit : (decide (a ∈ T) && S a) = true := by simp [hcond.1, hcond.2]
          rw [hbit]
          by_cases hodd : Odd ((s.filter fun k => k ∈ T ∧ S k = true).card)
          · have hnotodd : ¬ Odd ((s.filter fun k => k ∈ T ∧ S k = true).card + 1) := by
              rcases hodd with ⟨m, hm⟩; rw [hm]; exact Nat.not_odd_iff_even.mpr ⟨m + 1, by omega⟩
            simp [hodd, hnotodd]; rfl
          · have hodd' : Odd ((s.filter fun k => k ∈ T ∧ S k = true).card + 1) := by
              rw [Nat.not_odd_iff_even] at hodd
              rcases hodd with ⟨m, hm⟩; rw [hm]; exact ⟨m, by omega⟩
            simp [hodd, hodd']; rfl
        · rw [Finset.filter_insert, if_neg hcond]
          have hbit : (decide (a ∈ T) && S a) = false := by
            by_cases haT : a ∈ T <;> by_cases hSa : S a = true <;> simp_all
          rw [hbit]
          change false + decide (Odd _) = decide (Odd _)
          cases decide (Odd ((s.filter fun k => k ∈ T ∧ S k = true).card)) <;> rfl
    have hfilt : Finset.univ.filter (fun k => k ∈ T ∧ S k = true) = T.filter fun i => S i := by
      ext k; simp
    rw [hbool Finset.univ, hfilt]
  rw [hsum]
  rcases Nat.even_or_odd ((T.filter fun i => S i).card) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hnot : ¬ Odd (m + m) := Nat.not_odd_iff_even.mpr ⟨m, rfl⟩
    rw [hm, decide_eq_false hnot, if_neg Bool.false_ne_true, ← two_mul, pow_mul]
    norm_num
  · have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
    rw [hm, decide_eq_true hodd, if_pos rfl, pow_add, pow_mul]
    norm_num

lemma act_hadamardN_chiVec {n : ℕ} (T : Finset (Fin n)) :
    act (hadamardN n)
        (WithLp.toLp 2 fun S : Qubits n =>
          (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * (-1 : ℂ) ^ ((T.filter fun i => S i).card)) =
      ket (fun i : Fin n => decide (i ∈ T)) := by
  let indT : Qubits n := fun i => decide (i ∈ T)
  have hcol : (WithLp.toLp 2 fun S : Qubits n =>
        (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * (-1 : ℂ) ^ ((T.filter fun i => S i).card)) =
      WithLp.toLp 2 fun S : Qubits n => hadamardN n S indT := by
    ext S
    simp only [hadamardN, Matrix.of_apply]
    rw [← dotBits_indicator_eq_bool_sum T S]
    split_ifs <;> ring
  rw [hcol]
  ext j
  change (hadamardN n * hadamardN n) j indT = ket indT j
  rw [hadamardN_mul_self]
  simp [ket, Matrix.one_apply, PiLp.single_apply]

private lemma act_hadamardN_krawtchouk_combo {n m : ℕ} (A : Finset (Fin n)) (hA : A.card = 2 * m + 1)
    (c : Fin (2 * m + 2) → ℝ) :
    act (hadamardN n)
        (WithLp.toLp 2 fun S : Qubits n =>
          (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
            ∑ t : Fin (2 * m + 2),
              (krawtchouk (2 * m + 1) t (intersectionIndex ⟨A, hA⟩ S) : ℂ) * (c t : ℂ)) =
      ∑ t : Fin (2 * m + 2), (c t : ℂ) • uniformSubsetKet n A t.1 := by
  let chiVec : Finset (Fin n) → EuclideanSpace ℂ (Qubits n) := fun T =>
    WithLp.toLp 2 fun S : Qubits n =>
      (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * (-1 : ℂ) ^ ((T.filter fun i => S i).card)
  have hvec_eq :
      (WithLp.toLp 2 fun S : Qubits n =>
        (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
          ∑ t : Fin (2 * m + 2),
            (krawtchouk (2 * m + 1) t (intersectionIndex ⟨A, hA⟩ S) : ℂ) * (c t : ℂ)) =
      ∑ t : Fin (2 * m + 2), (c t : ℂ) • ∑ T ∈ A.powersetCard t.1, chiVec T := by
    ext S
    have hk := krawtchouk_eq_powersetCard_sum A hA
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      chiVec]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hkt : (krawtchouk (2 * m + 1) t (intersectionIndex ⟨A, hA⟩ S) : ℂ) =
        ∑ T ∈ A.powersetCard t.1, (-1 : ℂ) ^ ((T.filter fun i => S i).card) := by
      have hktZ := hk t S
      exact_mod_cast hktZ
    change (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) *
          ((krawtchouk (2 * m + 1) t (intersectionIndex ⟨A, hA⟩ S) : ℂ) * (c t : ℂ)) =
        (c t : ℂ) * ∑ T ∈ A.powersetCard t.1,
          (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * (-1 : ℂ) ^ ((T.filter fun i => S i).card)
    rw [hkt, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => by ring
  rw [hvec_eq, act_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [act_smul, act_sum]
  congr 1
  unfold uniformSubsetKet
  refine Finset.sum_congr rfl fun T _ => act_hadamardN_chiVec T

lemma act_hadamardN_wCatAfter {n m : ℕ} (A : Finset (Fin n)) (hA : A.card = 2 * m + 1) :
    act (hadamardN n) (wCatAfter n m A hA) =
      ∑ t : Fin (2 * m + 2), (aCoeff m t : ℂ) • uniformSubsetKet n A t.1 :=
  act_hadamardN_krawtchouk_combo A hA (aCoeff m)

lemma act_hadamardN_wCatVec {n m : ℕ} (A : Finset (Fin n)) (hA : A.card = 2 * m + 1) :
    act (hadamardN n) (wCatVec n m A hA) =
      ∑ t : Fin (2 * m + 2), (bCoeff m t : ℂ) • uniformSubsetKet n A t.1 :=
  act_hadamardN_krawtchouk_combo A hA (bCoeff m)

noncomputable def H_hat (n : ℕ) : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ :=
  controlled (hadamardN n)

noncomputable def U_tilde (n m : ℕ) : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ :=
  Matrix.of fun (d₁, q₁) (d₂, q₂) =>
    if q₁ = q₂ then U_op m (hammingWeight q₁) d₁ d₂ else 0

noncomputable def U_ideal (n m : ℕ) : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ :=
  H_hat n * U_tilde n m * H_hat n

noncomputable def liftDQ_false {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Bool × Qubits n) :=
  WithLp.toLp 2 fun p : Bool × Qubits n => if p.1 then 0 else ψ p.2

noncomputable def liftDQ_true {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Bool × Qubits n) :=
  WithLp.toLp 2 fun p : Bool × Qubits n => if p.1 then ψ p.2 else 0

lemma liftDQ_false_ket {n : ℕ} (q : Qubits n) :
    liftDQ_false (ket q) = ket (false, q) := by
  ext p
  rcases p with ⟨b, q'⟩
  cases b <;> simp [liftDQ_false, ket, PiLp.single_apply]

lemma liftDQ_true_ket {n : ℕ} (q : Qubits n) :
    liftDQ_true (ket q) = ket (true, q) := by
  ext p
  rcases p with ⟨b, q'⟩
  cases b <;> simp [liftDQ_true, ket, PiLp.single_apply]

lemma liftDQ_true_add {n : ℕ} (ψ φ : EuclideanSpace ℂ (Qubits n)) :
    liftDQ_true (ψ + φ) = liftDQ_true ψ + liftDQ_true φ := by
  ext p; rcases p with ⟨b, q⟩; cases b <;> simp [liftDQ_true]

lemma liftDQ_true_smul {n : ℕ} (c : ℂ) (ψ : EuclideanSpace ℂ (Qubits n)) :
    liftDQ_true (c • ψ) = c • liftDQ_true ψ := by
  ext p; rcases p with ⟨b, q⟩; cases b <;> simp [liftDQ_true]

lemma liftDQ_true_sum {n : ℕ} {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℂ (Qubits n)) :
    liftDQ_true (∑ x ∈ s, f x) = ∑ x ∈ s, liftDQ_true (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext p; rcases p with ⟨b, q⟩; cases b <;> simp [liftDQ_true]
  | insert a s ha ih => rw [Finset.sum_insert ha, liftDQ_true_add, ih, Finset.sum_insert ha]

lemma act_H_hat_false {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    act (H_hat n) (liftDQ_false ψ) = liftDQ_false ψ := by
  ext p
  rcases p with ⟨b, q⟩
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, H_hat, controlled, Matrix.of_apply,
    liftDQ_false, Fintype.sum_prod_type]
  cases b
  · rw [Finset.sum_eq_single false]
    · simp only [↓reduceIte, Matrix.one_apply]
      rw [Finset.sum_eq_single q]
      · simp
      · intro q' _ hq'; simp [hq'.symm]
      · simp
    · intro b' _ hb'; simp [hb'.symm]
    · simp
  · refine Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun q' _ => ?_
    cases b' <;> simp

lemma act_H_hat_true {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    act (H_hat n) (liftDQ_true ψ) = liftDQ_true (act (hadamardN n) ψ) := by
  ext p
  rcases p with ⟨b, q⟩
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, H_hat, controlled, Matrix.of_apply,
    liftDQ_true, Fintype.sum_prod_type]
  cases b
  · refine Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun q' _ => ?_
    cases b' <;> simp
  · rw [Finset.sum_eq_single true]
    · simp
    · intro b' _ hb'; simp [hb'.symm]
    · simp

lemma act_U_tilde_ket {n m : ℕ} (d : Bool) (q : Qubits n) :
    act (U_tilde n m) (ket (d, q)) =
      ∑ d' : Bool, (U_op m (hammingWeight q) d' d) • ket (d', q) := by
  ext p
  rcases p with ⟨b, q'⟩
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, U_tilde, Matrix.of_apply,
    ket, PiLp.single_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single d]
  · rw [Finset.sum_eq_single q]
    · by_cases hq : q' = q
      · subst hq
        rw [Finset.sum_eq_single b]
        · simp
        · intro d' _ hd'; simp [hd'.symm]
        · simp
      · simp [hq]
    · intro q'' _ hq''; simp [hq'']
    · simp
  · intro d'' _ hd''; refine Finset.sum_eq_zero fun q'' _ => ?_; simp [hd'']
  · simp

lemma hammingWeight_indicator {n : ℕ} (T : Finset (Fin n)) :
    hammingWeight (fun i : Fin n => decide (i ∈ T)) = T.card := by
  simp [hammingWeight]

lemma U_op_mem_unitaryGroup (m t : ℕ) : U_op m t ∈ Matrix.unitaryGroup Bool ℂ := by
  unfold U_op
  split_ifs
  · exact pauliX_mem_unitaryGroup
  · exact U_k_mat_mem_unitaryGroup m
  · exact pauliZ_mem_unitaryGroup
  · exact Submonoid.one_mem _

lemma H_hat_mul_self (n : ℕ) : H_hat n * H_hat n = 1 := by
  ext ⟨b₁, q₁⟩ ⟨b₂, q₂⟩
  simp only [H_hat, controlled, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type]
  by_cases hb : b₁ = b₂
  · subst hb
    cases b₁
    · simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, true_and]
      rw [Finset.sum_eq_single false]
      · simp
      · intro b' _ hb'; simp [hb'.symm]
      · simp
    · simp only [↓reduceIte, Prod.mk.injEq, true_and]
      rw [Finset.sum_eq_single true]
      · simp only [↓reduceIte]
        have hsq := congrFun (congrFun (hadamardN_mul_self n) q₁) q₂
        simpa [Matrix.mul_apply, Matrix.one_apply] using hsq
      · intro b' _ hb'; simp [hb'.symm]
      · simp
  · simp only [Prod.mk.injEq, hb, false_and, ↓reduceIte]
    refine Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun q' _ => ?_
    by_cases h1 : b₁ = b'
    · subst h1; simp [hb]
    · simp [h1]

lemma H_hat_mem_unitaryGroup (n : ℕ) : H_hat n ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star (H_hat n) = H_hat n := by
    ext ⟨b₁, q₁⟩ ⟨b₂, q₂⟩
    simp only [Matrix.star_apply, H_hat, controlled, Matrix.of_apply]
    by_cases hb : b₁ = b₂
    · subst hb
      cases b₁
      · simp [Matrix.one_apply, eq_comm]
      · have hs := congrFun (congrFun (hadamardN_star n) q₁) q₂
        simp only [Matrix.star_apply] at hs
        simpa using hs
    · simp [hb, ne_comm.mp hb]
  rw [hstar, H_hat_mul_self]

lemma U_ideal_transduces {n m : ℕ} (_hm : 1 ≤ m) (_hle : 2 * m + 1 ≤ n)
    (A : Finset (Fin n)) (hA : A.card = 2 * m + 1) :
    act (U_ideal n m) (ket (false, fun _ => false) + liftDQ_true (wCatAfter n m A hA)) =
      ket (false, fun i => decide (i ∈ A)) + liftDQ_true (wCatVec n m A hA) := by
  have h1 : act (H_hat n) (ket (false, fun _ => false) + liftDQ_true (wCatAfter n m A hA)) =
      ket (false, fun _ => false) +
        ∑ t : Fin (2 * m + 2), (aCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1) := by
    rw [act_add, ← liftDQ_false_ket, act_H_hat_false, liftDQ_false_ket, act_H_hat_true,
      act_hadamardN_wCatAfter, liftDQ_true_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [liftDQ_true_smul]
  have hU_0 : act (U_tilde n m) (ket (false, fun _ => false)) =
      (bCoeff m 0 : ℂ) • liftDQ_true (uniformSubsetKet n A 0) := by
    have hw0 : hammingWeight (fun _ : Fin n => false) = 0 := by simp [hammingWeight]
    rw [act_U_tilde_ket, hw0]
    simp only [U_op, ↓reduceIte]
    rw [Fintype.sum_bool, bCoeff_zero, Complex.ofReal_one, one_smul, uniformSubsetKet_zero,
      zeroKet, liftDQ_true_ket]
    have hf : pauliX false false = 0 := by simp [pauliX]
    have ht : pauliX true false = 1 := by simp [pauliX]
    simp [hf, ht]
  have hU_int : ∀ t : Fin (2 * m + 2), 1 ≤ t.1 → t.1 ≤ 2 * m →
      act (U_tilde n m) ((aCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1)) =
        (bCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1) := by
    intro t ht1 ht2
    rw [act_smul, uniformSubsetKet, liftDQ_true_sum, act_sum]
    have hterm : ∀ T ∈ A.powersetCard t.1,
        act (U_tilde n m) (liftDQ_true (ket (fun i => decide (i ∈ T)))) =
          (if t.1.testBit 1 then (-1 : ℂ) else 1) • liftDQ_true (ket (fun i => decide (i ∈ T))) := by
      intro T hT
      have hTcard : T.card = t.1 := (Finset.mem_powersetCard.mp hT).2
      rw [liftDQ_true_ket, act_U_tilde_ket, hammingWeight_indicator, hTcard, Fintype.sum_bool]
      have ht0 : t.1 ≠ 0 := by omega
      have htk : t.1 ≠ 2 * m + 1 := by omega
      by_cases hbit : t.1.testBit 1 = true
      · simp only [U_op, ht0, htk, hbit, ↓reduceIte]
        have hf : pauliZ false true = 0 := by simp [pauliZ]
        have ht : pauliZ true true = -1 := by simp [pauliZ]
        simp [hf, ht]
      · have hbf : t.1.testBit 1 = false := Bool.eq_false_iff.mpr hbit
        simp only [U_op, ht0, htk, hbf, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply,
          zero_smul, one_smul, add_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, smul_smul]
    congr 1
    by_cases hbit : t.1.testBit 1 = true
    · simp only [hbit, ↓reduceIte, mul_neg, mul_one]
      have hb := abCoeff_interior_odd m t ht1 ht2 hbit
      exact_mod_cast hb.symm
    · have hbf : t.1.testBit 1 = false := Bool.eq_false_iff.mpr hbit
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, mul_one]
      have hab := abCoeff_interior_even m t ht1 ht2 hbf
      exact_mod_cast hab
  have hU_top :
      act (U_tilde n m) ((aCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) • liftDQ_true (uniformSubsetKet n A (2 * m + 1))) =
        ket (false, fun i => decide (i ∈ A)) +
          (bCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) • liftDQ_true (uniformSubsetKet n A (2 * m + 1)) := by
    let indA : Qubits n := fun i => decide (i ∈ A)
    have hself : uniformSubsetKet n A (2 * m + 1) = ket indA := by
      rw [← hA]; exact uniformSubsetKet_self A
    rw [hself, liftDQ_true_ket, act_smul, act_U_tilde_ket, hammingWeight_indicator, hA, Fintype.sum_bool]
    have hne0 : 2 * m + 1 ≠ 0 := by omega
    simp only [U_op, hne0, ↓reduceIte]
    have ha_ne : (aCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (aCoeff_top_ne_zero m)
    have h0 : (aCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) * U_k_mat m false true = 1 := by
      simp [U_k_mat]
      exact mul_inv_cancel₀ ha_ne
    have h1' : (aCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) * U_k_mat m true true =
        (bCoeff m ⟨2 * m + 1, by omega⟩ : ℂ) := by
      simp [U_k_mat]
      field_simp [ha_ne]
    rw [smul_add, smul_smul, smul_smul, h0, h1', one_smul]
    abel
  let topIdx : Fin (2 * m + 2) := ⟨2 * m + 1, by omega⟩
  have hsplit_a : (∑ t : Fin (2 * m + 2), (aCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1)) =
      (aCoeff m topIdx : ℂ) • liftDQ_true (uniformSubsetKet n A (2 * m + 1)) +
        ∑ t ∈ (Finset.univ.erase (0 : Fin (2 * m + 2))).erase topIdx,
          (aCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin (2 * m + 2)))]
    have h0a : (aCoeff m 0 : ℂ) • liftDQ_true (uniformSubsetKet n A (0 : Fin (2 * m + 2)).1) = 0 := by
      simp [aCoeff_zero]
    rw [h0a, zero_add]
    have hmem_top : topIdx ∈ Finset.univ.erase (0 : Fin (2 * m + 2)) := by
      rw [Finset.mem_erase]
      exact ⟨by intro h; have := congrArg Fin.val h; simp [topIdx] at this, Finset.mem_univ _⟩
    exact (Finset.add_sum_erase (Finset.univ.erase (0 : Fin (2 * m + 2))) _ hmem_top).symm
  have hsplit_b : (∑ t : Fin (2 * m + 2), (bCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1)) =
      (bCoeff m 0 : ℂ) • liftDQ_true (uniformSubsetKet n A 0) +
      (bCoeff m topIdx : ℂ) • liftDQ_true (uniformSubsetKet n A (2 * m + 1)) +
        ∑ t ∈ (Finset.univ.erase (0 : Fin (2 * m + 2))).erase topIdx,
          (bCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin (2 * m + 2)))]
    have hmem_top : topIdx ∈ Finset.univ.erase (0 : Fin (2 * m + 2)) := by
      rw [Finset.mem_erase]
      exact ⟨by intro h; have := congrArg Fin.val h; simp [topIdx] at this, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase (Finset.univ.erase (0 : Fin (2 * m + 2))) _ hmem_top]
    simp only [Fin.val_zero, topIdx]
    abel
  have hU_mid :
      act (U_tilde n m)
        (∑ t ∈ (Finset.univ.erase (0 : Fin (2 * m + 2))).erase topIdx,
          (aCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1)) =
      ∑ t ∈ (Finset.univ.erase (0 : Fin (2 * m + 2))).erase topIdx,
        (bCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1) := by
    rw [act_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_erase, Finset.mem_erase] at ht
    have ht0 : t.1 ≠ 0 := fun h => ht.2.1 (Fin.ext h)
    have htk : t.1 ≠ 2 * m + 1 := fun h => ht.1 (Fin.ext h)
    have ht1 : 1 ≤ t.1 := Nat.pos_of_ne_zero ht0
    have ht2 : t.1 ≤ 2 * m := by have := t.isLt; omega
    exact hU_int t ht1 ht2
  have h2 : act (U_tilde n m) (act (H_hat n) (ket (false, fun _ => false) + liftDQ_true (wCatAfter n m A hA))) =
      ket (false, fun i => decide (i ∈ A)) +
        ∑ t : Fin (2 * m + 2), (bCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1) := by
    rw [h1, hsplit_a, act_add, act_add, hU_0, hU_top, hU_mid, hsplit_b]
    abel
  have h3 : act (H_hat n) (ket (false, fun i => decide (i ∈ A)) +
        ∑ t : Fin (2 * m + 2), (bCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1)) =
      ket (false, fun i => decide (i ∈ A)) + liftDQ_true (wCatVec n m A hA) := by
    have hsum_eq : (∑ t : Fin (2 * m + 2), (bCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1)) =
        liftDQ_true (act (hadamardN n) (wCatVec n m A hA)) := by
      rw [act_hadamardN_wCatVec, liftDQ_true_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [liftDQ_true_smul]
    rw [hsum_eq, act_add, ← liftDQ_false_ket, act_H_hat_false, liftDQ_false_ket, act_H_hat_true,
      ← act_mul, hadamardN_mul_self, act_one_vec]
  calc act (U_ideal n m) (ket (false, fun _ => false) + liftDQ_true (wCatAfter n m A hA))
      = act (H_hat n) (act (U_tilde n m) (act (H_hat n)
          (ket (false, fun _ => false) + liftDQ_true (wCatAfter n m A hA)))) := by
        simp [U_ideal, act_mul]
    _ = act (H_hat n) (ket (false, fun i => decide (i ∈ A)) +
          ∑ t : Fin (2 * m + 2), (bCoeff m t : ℂ) • liftDQ_true (uniformSubsetKet n A t.1)) := by
        rw [h2]
    _ = ket (false, fun i => decide (i ∈ A)) + liftDQ_true (wCatVec n m A hA) := h3

end TransducerAlgebra

end Thm49Algebra


/-
  Walk & Circuit Assembly (parameterized over PrimitiveSuite matching SPEC.md).
  Designed to be concatenated after `Algebra.lean` (or with `Thm49Algebra` in scope).
-/

namespace Thm49Walk

open QAlgorithms QuantumLTF.Majority QuantumLTF.Membership QuantumLTF.Membership.Supplement
open Thm49Algebra

/-! ### Bit-order LSB helpers -/

def natToBitsLSB (ℓ val : ℕ) : Qubits ℓ :=
  fun j => val.testBit j.val

lemma natToBitsLSB_zero (ℓ : ℕ) : natToBitsLSB ℓ 0 = fun _ => false := by
  funext j; simp [natToBitsLSB]

lemma natToBitsLSB_inj_of_lt {ℓ a b : ℕ} (ha : a < 2 ^ ℓ) (hb : b < 2 ^ ℓ)
    (h : natToBitsLSB ℓ a = natToBitsLSB ℓ b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < ℓ
  · exact congrFun h ⟨i, hi⟩
  · have hi_le : ℓ ≤ i := Nat.le_of_not_lt hi
    have ha_lt : a < 2 ^ i := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi_le)
    have hb_lt : b < 2 ^ i := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi_le)
    rw [Nat.testBit_lt_two_pow ha_lt, Nat.testBit_lt_two_pow hb_lt]

/-! ### Basic Gate & OracleCircuit composition helpers -/

lemma gate_ofMatrix1_isUnitary {M : Matrix Bool Bool ℂ}
    (hM : M ∈ Matrix.unitaryGroup Bool ℂ) : (Gate.ofMatrix1 M).IsUnitary := by
  dsimp only [Gate.IsUnitary, Gate.ofMatrix1]
  rw [Matrix.mem_unitaryGroup_iff]
  let e : Qubits 1 ≃ Bool :=
    { toFun := fun b => b 0
      invFun := fun x _ => x
      left_inv := fun b => funext fun i => by fin_cases i; rfl
      right_inv := fun _ => rfl }
  have hstar : star (M.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) =
      (star M).submatrix e e := by
    ext i j; simp [e, Matrix.star_apply]
  have hmul : (M.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) *
      (star M).submatrix e e = (M * star M).submatrix e e := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, e]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hstar, hmul, Matrix.mem_unitaryGroup_iff.mp hM]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [e]
  · have he : e i ≠ e j := fun h => hij (e.injective h)
    simp [Matrix.submatrix_apply, hij, he]

lemma gate_ofMatrix2_isUnitary {M : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) : (Gate.ofMatrix2 M).IsUnitary := by
  dsimp only [Gate.IsUnitary, Gate.ofMatrix2]
  rw [Matrix.mem_unitaryGroup_iff]
  let e : Qubits 2 ≃ Bool × Bool :=
    { toFun := fun b => (b 0, b 1)
      invFun := fun p i => if i.1 = 0 then p.1 else p.2
      left_inv := fun b => funext fun i => by fin_cases i <;> rfl
      right_inv := fun p => by cases p; rfl }
  have hstar : star (M.submatrix (fun b : Qubits 2 => (b 0, b 1)) (fun b => (b 0, b 1))) =
      (star M).submatrix e e := by
    ext i j; simp [e, Matrix.star_apply]
  have hmul : (M.submatrix (fun b : Qubits 2 => (b 0, b 1)) (fun b => (b 0, b 1))) *
      (star M).submatrix e e = (M * star M).submatrix e e := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, e]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hstar, hmul, Matrix.mem_unitaryGroup_iff.mp hM]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [e]
  · have he : e i ≠ e j := fun h => hij (e.injective h)
    simp [Matrix.submatrix_apply, hij, he]

lemma gate_ofMatrix1_mem_gates12 {M : Matrix Bool Bool ℂ}
    (hM : M ∈ Matrix.unitaryGroup Bool ℂ) : Gate.ofMatrix1 M ∈ gates12 :=
  ⟨gate_ofMatrix1_isUnitary hM, by simp [Gate.ofMatrix1], by simp [Gate.ofMatrix1]⟩

lemma gate_ofMatrix2_mem_gates12 {M : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) : Gate.ofMatrix2 M ∈ gates12 :=
  ⟨gate_ofMatrix2_isUnitary hM, by simp [Gate.ofMatrix2], by simp [Gate.ofMatrix2]⟩

lemma hadamard_mem_unitaryGroup : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hHs : star hadamard = hadamard := by
    ext a b; cases a <;> cases b <;> simp [hadamard, Matrix.star_apply, Complex.conj_ofReal]
  rw [hHs, hadamard_mul_self]

lemma hadamard_mul_pauliX_mem_unitaryGroup :
    hadamard * pauliX ∈ Matrix.unitaryGroup Bool ℂ :=
  Submonoid.mul_mem _ hadamard_mem_unitaryGroup pauliX_mem_unitaryGroup

lemma embedOp_comp {k m₀ m : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin m₀) (emb : Fin m₀ ↪ Fin m) :
    embedOp (embedOp M w) emb = embedOp M (w.trans emb) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  by_cases hout : ∀ a : Fin m, a ∉ Set.range (w.trans emb) → y a = z a
  · rw [if_pos hout]
    have hout_emb : ∀ a : Fin m, a ∉ Set.range emb → y a = z a := by
      intro a ha
      exact hout a fun ⟨i, hi⟩ => ha ⟨w i, hi⟩
    rw [if_pos hout_emb]
    have hout_w : ∀ b : Fin m₀, b ∉ Set.range w → (y ∘ emb) b = (z ∘ emb) b := by
      intro b hb
      apply hout (emb b)
      rintro ⟨i, hi⟩
      exact hb ⟨i, emb.injective hi⟩
    rw [if_pos hout_w]
    rfl
  · rw [if_neg hout]
    split_ifs with h1 h2
    · exfalso
      apply hout
      intro a ha
      by_cases hae : a ∈ Set.range emb
      · obtain ⟨b, rfl⟩ := hae
        have hb : b ∉ Set.range w := fun ⟨i, hi⟩ => ha ⟨i, by simp [hi]⟩
        exact h2 b hb
      · exact h1 a hae
    · rfl
    · rfl

lemma embedOp_mul {k m : ℕ} (A B : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin m) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  classical
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  let updateW : Qubits k → Qubits m := fun x i =>
    if h : ∃ j, w j = i then x (Classical.choose h) else z i
  have hup_comp : ∀ x : Qubits k, updateW x ∘ w = x := fun x => by
    funext j
    simp [updateW]
  have hup_out : ∀ (x : Qubits k) (i : Fin m), i ∉ Set.range w → updateW x i = z i := by
    intro x i hi
    have hnot : ¬ ∃ j, w j = i := fun ⟨j, hj⟩ => hi ⟨j, hj⟩
    simp [updateW, hnot]
  have hup_inj : Function.Injective updateW := by
    intro x₁ x₂ h
    have := congrArg (· ∘ w) h
    simpa [hup_comp] using this
  by_cases hout : ∀ a : Fin m, a ∉ Set.range w → y a = z a
  · rw [if_pos hout]
    have hsum : (∑ u : Qubits m,
          (if ∀ a, a ∉ Set.range w → y a = u a then A (y ∘ w) (u ∘ w) else 0) *
          (if ∀ a, a ∉ Set.range w → u a = z a then B (u ∘ w) (z ∘ w) else 0)) =
        ∑ u ∈ Finset.univ.image updateW,
          (if ∀ a, a ∉ Set.range w → y a = u a then A (y ∘ w) (u ∘ w) else 0) *
          (if ∀ a, a ∉ Set.range w → u a = z a then B (u ∘ w) (z ∘ w) else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro u _ hu
      have hne : ¬ ∀ a, a ∉ Set.range w → u a = z a := by
        intro huz
        apply hu
        rw [Finset.mem_image]
        refine ⟨u ∘ w, Finset.mem_univ _, ?_⟩
        funext i
        by_cases hi : i ∈ Set.range w
        · obtain ⟨j, rfl⟩ := hi
          simp [updateW]
        · have hnot : ¬ ∃ j, w j = i := fun ⟨j, hj⟩ => hi ⟨j, hj⟩
          simp [updateW, hnot, huz i hi]
      rw [if_neg hne, mul_zero]
    rw [hsum, Finset.sum_image (fun x₁ _ x₂ _ h => hup_inj h)]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hyu : ∀ a, a ∉ Set.range w → y a = updateW x a := fun a ha =>
      (hout a ha).trans (hup_out x a ha).symm
    have huz : ∀ a, a ∉ Set.range w → updateW x a = z a := fun a ha => hup_out x a ha
    rw [if_pos hyu, if_pos huz, hup_comp]
  · rw [if_neg hout]
    symm
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases h1 : ∀ a, a ∉ Set.range w → y a = u a
    · have h2 : ¬ ∀ a, a ∉ Set.range w → u a = z a := fun h2 =>
        hout fun a ha => (h1 a ha).trans (h2 a ha)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma embedOp_mem_unitaryGroup {k m : ℕ} {M : Matrix (Qubits k) (Qubits k) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Qubits k) ℂ) (w : Fin k ↪ Fin m) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star (embedOp M w) = embedOp (star M) w := by
    ext y z
    simp only [Matrix.star_apply, embedOp, Matrix.of_apply]
    by_cases h : ∀ a, a ∉ Set.range w → y a = z a
    · have h' : ∀ a, a ∉ Set.range w → z a = y a := fun a ha => (h a ha).symm
      rw [if_pos h', if_pos h]
    · have h' : ¬ ∀ a, a ∉ Set.range w → z a = y a := fun h' => h fun a ha => (h' a ha).symm
      rw [if_neg h', if_neg h]
      simp
  rw [hstar, ← embedOp_mul, Matrix.mem_unitaryGroup_iff.mp hM, embedOp_one]

def embedCircuit {S : Set Gate} {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (c : Circuit S m₀) :
    Circuit S m :=
  c.map fun g => ⟨g.gate, g.mem, g.wires.trans emb⟩

lemma embedCircuit_unitary {S : Set Gate} {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (c : Circuit S m₀) :
    (embedCircuit emb c).unitary = embedOp c.unitary emb := by
  unfold embedCircuit Circuit.unitary
  induction c with
  | nil => simp [embedOp_one]
  | cons g gs ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one] at ih ⊢
    rw [ih, embedOp_mul, embedOp_comp]

lemma circuit_unitary_mem_unitaryGroup {m : ℕ} (c : Circuit gates12 m) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits m) ℂ := by
  unfold Circuit.unitary
  induction c with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one] at ih ⊢
    exact Submonoid.mul_mem _ ih (embedOp_mem_unitaryGroup g.mem.1 g.wires)

lemma oracleCircuit_unitary_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c₁ c₂ : OracleCircuit S a m)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    (c₁ ++ c₂).unitary orc = c₂.unitary orc * c₁.unitary orc := by
  simp [OracleCircuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma oracleCircuit_unitary_lift {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : Circuit S m) (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary (c.map OracleStep.gate : OracleCircuit S a m) orc = c.unitary := by
  simp [OracleCircuit.unitary, Circuit.unitary, Function.comp_def, OracleStep.mat]

lemma oracleCircuit_queryCount_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c₁ c₂ : OracleCircuit S a m) (k : Fin r) :
    (c₁ ++ c₂).queryCount k = c₁.queryCount k + c₂.queryCount k := by
  simp [OracleCircuit.queryCount, List.countP_append]

lemma oracleCircuit_queryCount_lift {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : Circuit S m) (k : Fin r) :
    OracleCircuit.queryCount (c.map OracleStep.gate : OracleCircuit S a m) k = 0 := by
  simp [OracleCircuit.queryCount, List.countP_map, Function.comp_def, OracleStep.IsQueryTo]

lemma oracleCircuit_gateCount_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c₁ c₂ : OracleCircuit S a m) :
    (c₁ ++ c₂).gateCount = c₁.gateCount + c₂.gateCount := by
  simp [OracleCircuit.gateCount, List.countP_append]

lemma oracleCircuit_gateCount_lift {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : Circuit S m) :
    OracleCircuit.gateCount (c.map OracleStep.gate : OracleCircuit S a m) = c.length := by
  simp [OracleCircuit.gateCount, List.countP_map, Function.comp_def]

lemma oracleCircuit_queryCount_cons {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (st : OracleStep S a m) (c : OracleCircuit S a m) (k : Fin r) :
    OracleCircuit.queryCount (st :: c : OracleCircuit S a m) k =
      OracleCircuit.queryCount ([st] : OracleCircuit S a m) k + OracleCircuit.queryCount c k := by
  simpa using oracleCircuit_queryCount_append [st] c k

lemma oracleCircuit_gateCount_cons {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (st : OracleStep S a m) (c : OracleCircuit S a m) :
    OracleCircuit.gateCount (st :: c : OracleCircuit S a m) =
      OracleCircuit.gateCount ([st] : OracleCircuit S a m) + OracleCircuit.gateCount c := by
  simpa using oracleCircuit_gateCount_append [st] c

lemma act_embedOp_basis_map {m₀ m' : ℕ} (emb : Fin m₀ ↪ Fin m')
    (U₀ : Matrix (Qubits m₀) (Qubits m₀) ℂ) (z : Qubits m') (x' : Qubits m₀)
    (hact : act U₀ (ket (z ∘ emb)) = ket x') (z' : Qubits m')
    (hz'_in : z' ∘ emb = x')
    (hz'_out : ∀ i : Fin m', i ∉ Set.range emb → z' i = z i) :
    act (embedOp U₀ emb) (ket z) = ket z' := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, embedOp, Matrix.of_apply,
    ket, PiLp.single_apply]
  rw [Finset.sum_eq_single z]
  · simp only [↓reduceIte, mul_one]
    have hU : U₀ (y ∘ emb) (z ∘ emb) = if y ∘ emb = x' then 1 else 0 := by
      have hy := congrFun (congrArg WithLp.ofLp hact) (y ∘ emb)
      simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply] at hy
      rw [Finset.sum_eq_single (z ∘ emb)] at hy
      · simpa using hy
      · intro u _ hu; simp [hu]
      · simp
    by_cases hyz : y = z'
    · rw [hyz] at hU ⊢
      rw [if_pos hz'_out, hU, hz'_in, if_pos rfl, if_pos rfl]
    · rw [if_neg hyz]
      split_ifs with hout
      · rw [hU]
        split_ifs with hUeq
        · exfalso; apply hyz; funext i
          by_cases hi : i ∈ Set.range emb
          · obtain ⟨j, rfl⟩ := hi
            have h1 := congrFun hUeq j
            have h2 := congrFun hz'_in j
            exact h1.trans h2.symm
          · exact (hout i hi).trans (hz'_out i hi).symm
        · rfl
      · rfl
  · intro u _ hu; simp [hu]
  · simp

lemma act_embedOp_basis_sum {m₀ m' : ℕ} {κ : Type*} [Fintype κ]
    (emb : Fin m₀ ↪ Fin m') (U₀ : Matrix (Qubits m₀) (Qubits m₀) ℂ)
    (z : Qubits m') (α : κ → ℂ) (x' : κ → Qubits m₀) (z' : κ → Qubits m')
    (hact : act U₀ (ket (z ∘ emb)) = ∑ j : κ, α j • ket (x' j))
    (hz'_in : ∀ j : κ, z' j ∘ emb = x' j)
    (hz'_out : ∀ (j : κ) (i : Fin m'), i ∉ Set.range emb → z' j i = z i) :
    act (embedOp U₀ emb) (ket z) = ∑ j : κ, α j • ket (z' j) := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, embedOp, Matrix.of_apply,
    ket, PiLp.single_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single z]
  · simp only [↓reduceIte, mul_one]
    have hU : U₀ (y ∘ emb) (z ∘ emb) = ∑ j : κ, α j * (if y ∘ emb = x' j then 1 else 0) := by
      have hy := congrFun (congrArg WithLp.ofLp hact) (y ∘ emb)
      simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
        WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hy
      rw [Finset.sum_eq_single (z ∘ emb)] at hy
      · simpa using hy
      · intro u _ hu; simp [hu]
      · simp
    by_cases hout : ∀ i : Fin m', i ∉ Set.range emb → y i = z i
    · rw [if_pos hout, hU]
      refine Finset.sum_congr rfl fun j _ => ?_
      have heq : (y = z' j) ↔ (y ∘ emb = x' j) := by
        constructor
        · intro h; rw [h, hz'_in j]
        · intro h; funext i
          by_cases hi : i ∈ Set.range emb
          · obtain ⟨b, rfl⟩ := hi; exact (congrFun h b).trans (congrFun (hz'_in j) b).symm
          · exact (hout i hi).trans (hz'_out j i hi).symm
      by_cases hj : y = z' j
      · rw [if_pos hj, if_pos (heq.mp hj)]
      · rw [if_neg hj, if_neg (fun h => hj (heq.mpr h))]
    · rw [if_neg hout]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have hne : y ≠ z' j := by
        intro h; apply hout; intro i hi; rw [h, hz'_out j i hi]
      rw [if_neg hne, mul_zero]
  · intro u _ hu; simp [hu]
  · simp

/-! ### `nonOracleDepth` basic bounds (proved directly) -/

private def stepWireSet {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (st : OracleStep S a m) : Finset (Fin m) :=
  match st with
  | .gate g => Finset.univ.image g.wires
  | .query _ _ ctl wires _ =>
      Finset.univ.image wires ∪ (match ctl with | none => ∅ | some c => {c})

private def stepCost {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (st : OracleStep S a m) : ℕ :=
  match st with
  | .gate _ => 1
  | .query _ _ _ _ _ => 0

private def stepTimeUpdate {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (τ : Fin m → ℕ) (st : OracleStep S a m) : Fin m → ℕ :=
  let t := (stepWireSet st).sup τ + stepCost st
  fun j => if j ∈ stepWireSet st then t else τ j

private lemma stepTimeUpdate_mono {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    {τ₁ τ₂ : Fin m → ℕ} (h : ∀ j, τ₁ j ≤ τ₂ j) (st : OracleStep S a m) :
    ∀ j, stepTimeUpdate τ₁ st j ≤ stepTimeUpdate τ₂ st j := by
  intro j
  dsimp only [stepTimeUpdate]
  have hsup : (stepWireSet st).sup τ₁ ≤ (stepWireSet st).sup τ₂ :=
    Finset.sup_le fun x hx => le_trans (h x) (Finset.le_sup hx)
  split_ifs
  · omega
  · exact h j

private lemma stepTimeUpdate_shift {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (τ : Fin m → ℕ) (B : ℕ) (st : OracleStep S a m) :
    ∀ j, stepTimeUpdate (fun i => τ i + B) st j = stepTimeUpdate τ st j + B := by
  intro j
  dsimp only [stepTimeUpdate]
  by_cases hj : j ∈ stepWireSet st
  · rw [if_pos hj, if_pos hj]
    have hne : (stepWireSet st).Nonempty := ⟨j, hj⟩
    have hsup : (stepWireSet st).sup (fun i => τ i + B) = (stepWireSet st).sup τ + B := by
      apply le_antisymm
      · refine Finset.sup_le fun x hx => ?_
        exact Nat.add_le_add_right (Finset.le_sup hx) B
      · obtain ⟨x, hx⟩ := hne
        have h1 : (stepWireSet st).sup τ + B ≤ (stepWireSet st).sup (fun i => τ i + B) := by
          have hs : (stepWireSet st).sup τ ≤ (stepWireSet st).sup (fun i => τ i + B) - B := by
            refine Finset.sup_le fun y hy => ?_
            have := Finset.le_sup (f := fun i => τ i + B) hy
            omega
          have hle : B ≤ (stepWireSet st).sup (fun i => τ i + B) := by
            have := Finset.le_sup (f := fun i => τ i + B) hx
            omega
          omega
        exact h1
    rw [hsup]
    omega
  · rw [if_neg hj, if_neg hj]

private lemma foldl_stepTimeUpdate_mono {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) {τ₁ τ₂ : Fin m → ℕ} (h : ∀ j, τ₁ j ≤ τ₂ j) :
    ∀ j, c.foldl stepTimeUpdate τ₁ j ≤ c.foldl stepTimeUpdate τ₂ j := by
  induction c generalizing τ₁ τ₂ with
  | nil => exact h
  | cons st rest ih =>
    intro j
    exact ih (stepTimeUpdate_mono h st) j

private lemma foldl_stepTimeUpdate_shift {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) (τ : Fin m → ℕ) (B : ℕ) :
    ∀ j, c.foldl stepTimeUpdate (fun i => τ i + B) j = c.foldl stepTimeUpdate τ j + B := by
  induction c generalizing τ with
  | nil => intro j; rfl
  | cons st rest ih =>
    intro j
    simp only [List.foldl_cons]
    have heq : stepTimeUpdate (fun i => τ i + B) st = fun i => stepTimeUpdate τ st i + B :=
      funext (stepTimeUpdate_shift τ B st)
    rw [heq]
    exact ih (stepTimeUpdate τ st) j

lemma nonOracleDepth_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c₁ c₂ : OracleCircuit S a m) :
    nonOracleDepth (c₁ ++ c₂) ≤ nonOracleDepth c₁ + nonOracleDepth c₂ := by
  change Finset.univ.sup ((c₁ ++ c₂).foldl stepTimeUpdate (fun _ => 0)) ≤
      Finset.univ.sup (c₁.foldl stepTimeUpdate (fun _ => 0)) +
      Finset.univ.sup (c₂.foldl stepTimeUpdate (fun _ => 0))
  rw [List.foldl_append]
  let τ₁ := c₁.foldl stepTimeUpdate (fun _ => 0)
  let B := Finset.univ.sup τ₁
  have hle : ∀ j, τ₁ j ≤ 0 + B := fun j => by
    rw [Nat.zero_add]; exact Finset.le_sup (Finset.mem_univ j)
  refine Finset.sup_le fun j _ => ?_
  have h1 := foldl_stepTimeUpdate_mono c₂ hle j
  have h2 := foldl_stepTimeUpdate_shift c₂ (fun _ => 0) B j
  rw [h2] at h1
  have h3 : c₂.foldl stepTimeUpdate (fun _ => 0) j ≤
      Finset.univ.sup (c₂.foldl stepTimeUpdate (fun _ => 0)) :=
    Finset.le_sup (Finset.mem_univ j)
  dsimp only [τ₁, B] at h1 h3 ⊢
  omega

lemma nonOracleDepth_cons {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (st : OracleStep S a m) (c : OracleCircuit S a m) :
    nonOracleDepth (st :: c) ≤
      nonOracleDepth ([st] : OracleCircuit S a m) + nonOracleDepth c := by
  simpa using nonOracleDepth_append [st] c

lemma nonOracleDepth_query_single {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (k : Fin r) (adj : Bool) (ctl : Option (Fin m)) (wires : Fin (a k) ↪ Fin m)
    (hc : ∀ c, ctl = some c → c ∉ Set.range wires) :
    nonOracleDepth ([OracleStep.query k adj ctl wires hc] : OracleCircuit S a m) = 0 := by
  change Finset.univ.sup (stepTimeUpdate (S := S) (r := r) (a := a) (fun _ => 0) (.query k adj ctl wires hc)) = 0
  have h0 : ∀ j, stepTimeUpdate (S := S) (r := r) (a := a) (fun _ => 0) (.query k adj ctl wires hc) j = 0 := by
    intro j
    dsimp only [stepTimeUpdate, stepCost]
    have hsup : (stepWireSet (S := S) (r := r) (a := a) (.query k adj ctl wires hc)).sup (fun _ => 0) = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact Finset.sup_le fun _ _ => le_rfl
    rw [hsup]
    split_ifs <;> rfl
  simp [h0]

lemma nonOracleDepth_le_length {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : OracleCircuit S a m) :
    nonOracleDepth c ≤ c.length := by
  induction c with
  | nil => simp [nonOracleDepth]
  | cons st rest ih =>
    have hsplit : st :: rest = [st] ++ rest := rfl
    rw [hsplit]
    have h1 := nonOracleDepth_append [st] rest
    have hsingle : nonOracleDepth ([st] : OracleCircuit S a m) ≤ 1 := by
      change Finset.univ.sup (stepTimeUpdate (S := S) (r := r) (a := a) (fun _ => 0) st) ≤ 1
      refine Finset.sup_le fun j _ => ?_
      dsimp only [stepTimeUpdate]
      have hsup : (stepWireSet st).sup (fun _ => 0) = 0 := by
        apply Nat.eq_zero_of_le_zero
        exact Finset.sup_le fun _ _ => le_rfl
      rw [hsup, zero_add]
      split_ifs
      · cases st <;> simp [stepCost]
      · exact Nat.zero_le _
    simp only [List.length_append, List.length_singleton]
    omega

lemma nonOracleDepth_disjoint_gates_le_one {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c : Circuit S m)
    (hdisj : c.Pairwise fun g₁ g₂ => Disjoint (Set.range g₁.wires) (Set.range g₂.wires)) :
    nonOracleDepth (c.map OracleStep.gate : OracleCircuit S a m) ≤ 1 := by
  have hfold : ∀ (l : Circuit S m) (τ : Fin m → ℕ),
      l.Pairwise (fun g₁ g₂ => Disjoint (Set.range g₁.wires) (Set.range g₂.wires)) →
      (∀ g ∈ l, ∀ i ∈ Set.range g.wires, τ i = 0) →
      ∀ j, (l.map OracleStep.gate : OracleCircuit S a m).foldl stepTimeUpdate τ j ≤ max (τ j) 1 := by
    intro l
    induction l with
    | nil => intro τ _ _ j; change τ j ≤ max (τ j) 1; exact le_max_left _ _
    | cons g gs ih =>
      intro τ hpw hτ j
      rw [List.pairwise_cons] at hpw
      simp only [List.map_cons, List.foldl_cons]
      have hsup0 : (stepWireSet (S := S) (r := r) (a := a) (.gate g)).sup τ = 0 := by
        apply Nat.eq_zero_of_le_zero
        refine Finset.sup_le fun i hi => ?_
        simp only [stepWireSet, Finset.mem_image, Finset.mem_univ, true_and] at hi
        obtain ⟨x, rfl⟩ := hi
        exact le_of_eq (hτ g (List.mem_cons_self) (g.wires x) ⟨x, rfl⟩)
      let τ' := stepTimeUpdate (S := S) (r := r) (a := a) τ (.gate g)
      have hτ'_gs : ∀ g' ∈ gs, ∀ i ∈ Set.range g'.wires, τ' i = 0 := by
        intro g' hg' i hi
        have hdis := hpw.1 g' hg'
        have hnot : i ∉ Set.range g.wires := fun hg => Set.disjoint_left.mp hdis hg hi
        have hnotW : i ∉ stepWireSet (S := S) (r := r) (a := a) (.gate g) := by
          simp only [stepWireSet, Finset.mem_image, Finset.mem_univ, true_and]
          rintro ⟨x, rfl⟩; exact hnot ⟨x, rfl⟩
        dsimp only [τ', stepTimeUpdate]
        rw [if_neg hnotW]
        exact hτ g' (List.mem_cons_of_mem g hg') i hi
      refine le_trans (ih τ' hpw.2 hτ'_gs j) ?_
      dsimp only [τ', stepTimeUpdate, stepCost]
      rw [hsup0, zero_add]
      split_ifs <;> omega
  change Finset.univ.sup ((c.map OracleStep.gate : OracleCircuit S a m).foldl stepTimeUpdate (fun _ => 0)) ≤ 1
  refine Finset.sup_le fun j _ => ?_
  have h := hfold c (fun _ => 0) hdisj (fun _ _ _ _ => rfl) j
  simpa using h

/-! ### Abstract Primitive Suite (to be instantiated from `Primitives.lean`) -/

def packCH (n anc : ℕ) (c : Bool) (x : Qubits n) (a : Qubits anc) : Qubits (1 + n + anc) :=
  fun i =>
    if h0 : i.1 = 0 then c
    else if h1 : i.1 < 1 + n then x ⟨i.1 - 1, by omega⟩
    else a ⟨i.1 - (1 + n), by omega⟩

def packEq (L anc : ℕ) (addr : Qubits L) (tgt : Bool) (a : Qubits anc) : Qubits (L + 1 + anc) :=
  fun i =>
    if h0 : i.1 < L then addr ⟨i.1, h0⟩
    else if h1 : i.1 = L then tgt
    else a ⟨i.1 - (L + 1), by omega⟩

def packHC (n ℓ anc : ℕ) (x : Qubits n) (w : Qubits ℓ) (a : Qubits anc) : Qubits (n + ℓ + anc) :=
  fun i =>
    if h0 : i.1 < n then x ⟨i.1, h0⟩
    else if h1 : i.1 < n + ℓ then w ⟨i.1 - n, by omega⟩
    else a ⟨i.1 - (n + ℓ), by omega⟩

structure PrimitiveSuite where
  -- 1. Toffoli gate on 3 wires
  toffoliCirc : Circuit gates12 3
  toffoliDepth : ℕ
  toffoli_hdepth : ∀ (r : ℕ) (a : Fin r → ℕ),
    nonOracleDepth (toffoliCirc.map OracleStep.gate : OracleCircuit gates12 a 3) ≤ toffoliDepth
  toffoli_act : ∀ (b₀ b₁ b₂ : Bool),
    act toffoliCirc.unitary (ket fun i : Fin 3 =>
      if i.1 = 0 then b₀ else if i.1 = 1 then b₁ else b₂) =
      ket fun i : Fin 3 =>
        if i.1 = 0 then b₀ else if i.1 = 1 then b₁ else xor b₂ (b₀ && b₁)
  -- 2. Controlled H^{⊗n}
  ancCH : ℕ → ℕ
  chCirc : (n : ℕ) → Circuit gates12 (1 + n + ancCH n)
  chDepth : ℕ → ℕ
  ch_hdepth : ∀ (n : ℕ) (r : ℕ) (a : Fin r → ℕ),
    nonOracleDepth ((chCirc n).map OracleStep.gate : OracleCircuit gates12 a (1 + n + ancCH n)) ≤ chDepth n
  C_ch : ℝ
  hC_ch_pos : 0 < C_ch
  ch_bound : ∀ n : ℕ, 2 ≤ n →
    ((chCirc n).length : ℝ) ≤ C_ch * n ∧ (chDepth n : ℝ) ≤ C_ch * Real.log n
  ch_act : ∀ (n : ℕ) (c : Bool) (x : Qubits n),
    act (chCirc n).unitary (ket (packCH n (ancCH n) c x (fun _ => false))) =
      if c then
        ∑ y : Qubits n, (hadamardN n y x) • ket (packCH n (ancCH n) true y (fun _ => false))
      else
        ket (packCH n (ancCH n) false x (fun _ => false))
  -- 3. Multi-controlled 1-qubit unitary on equality
  ancEq : ℕ → ℕ
  eqCirc : (L : ℕ) → Qubits L → (U : Matrix Bool Bool ℂ) → U ∈ Matrix.unitaryGroup Bool ℂ →
    Circuit gates12 (L + 1 + ancEq L)
  eqDepth : ℕ → ℕ
  eq_hdepth : ∀ (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (r : ℕ) (a : Fin r → ℕ),
    nonOracleDepth ((eqCirc L pat U hU).map OracleStep.gate : OracleCircuit gates12 a (L + 1 + ancEq L)) ≤ eqDepth L
  C_eq : ℝ
  hC_eq_pos : 0 < C_eq
  eq_bound : ∀ (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ),
    ((eqCirc L pat U hU).length : ℝ) ≤ C_eq * (L + 1) ∧
    (eqDepth L : ℝ) ≤ C_eq * (Nat.clog 2 (L + 1) + 1 : ℕ)
  eq_act : ∀ (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (addr : Qubits L) (tgt : Bool),
    act (eqCirc L pat U hU).unitary (ket (packEq L (ancEq L) addr tgt (fun _ => false))) =
      if addr = pat then
        ∑ b' : Bool, (U b' tgt) • ket (packEq L (ancEq L) addr b' (fun _ => false))
      else
        ket (packEq L (ancEq L) addr tgt (fun _ => false))
  -- 4. Hamming counter + its adjoint
  ancHC : ℕ → ℕ
  hcCirc : (n : ℕ) → Circuit gates12 (n + Nat.clog 2 (n + 1) + ancHC n)
  hcAdjCirc : (n : ℕ) → Circuit gates12 (n + Nat.clog 2 (n + 1) + ancHC n)
  hcDepth : ℕ → ℕ
  hc_hdepth : ∀ (n : ℕ) (r : ℕ) (a : Fin r → ℕ),
    nonOracleDepth ((hcCirc n).map OracleStep.gate :
      OracleCircuit gates12 a (n + Nat.clog 2 (n + 1) + ancHC n)) ≤ hcDepth n ∧
    nonOracleDepth ((hcAdjCirc n).map OracleStep.gate :
      OracleCircuit gates12 a (n + Nat.clog 2 (n + 1) + ancHC n)) ≤ hcDepth n
  hcAdj_length : ∀ n, (hcAdjCirc n).length = (hcCirc n).length
  hcAdj_unitary : ∀ n, (hcAdjCirc n).unitary = star (hcCirc n).unitary
  C_hc : ℝ
  hC_hc_pos : 0 < C_hc
  hc_bound : ∀ n : ℕ, 2 ≤ n →
    ((hcCirc n).length : ℝ) ≤ C_hc * n * Real.log n ∧ (hcDepth n : ℝ) ≤ C_hc * Real.log n
  hc_act : ∀ (n : ℕ) (x : Qubits n),
    act (hcCirc n).unitary (ket (packHC n (Nat.clog 2 (n + 1)) (ancHC n) x (fun _ => false) (fun _ => false))) =
      ket (packHC n (Nat.clog 2 (n + 1)) (ancHC n) x
        (natToBitsLSB (Nat.clog 2 (n + 1)) (hammingWeight x)) (fun _ => false))

/-! ### Self-contained `ctrl0X` (XOR clock bits conditioned on `D = false`) and `hadamard` layers -/

def ctrl0XMat : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 ∧ p.2 = (if q.1 then q.2 else !(q.2)) then 1 else 0

lemma ctrl0XMat_mem_unitaryGroup : ctrl0XMat ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext p q
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [Matrix.mul_apply, Matrix.star_apply, ctrl0XMat, Matrix.of_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Fintype.sum_bool]
  cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> simp

section FullCircuit

variable (ps : PrimitiveSuite)

noncomputable def ancMax (r n : ℕ) : ℕ :=
  max (ps.ancCH n) (max (ps.ancEq (r + 1)) (max (ps.ancEq r)
    (max (ps.ancEq (1 + Nat.clog 2 (n + 1))) (max (ps.ancEq 2) (ps.ancHC n)))))

noncomputable def regM' (r n : ℕ) : ℕ :=
  r + 1 + n + Nat.clog 2 (n + 1) + 3 + ancMax ps r n

section FixedParams

variable {ps} {r n : ℕ}

local notation "ℓ" => Nat.clog 2 (n + 1)
local notation "Amax" => ancMax ps r n
local notation "M'" => regM' ps r n

def regC : Fin r ↪ Fin M' :=
  ⟨fun i => ⟨i.1, by dsimp only [regM']; omega⟩, fun i j h => Fin.ext (by
    have := congrArg Fin.val h; dsimp at this; omega)⟩

def wireD : Fin M' := ⟨r, by dsimp only [regM']; omega⟩

def regQ : Fin n ↪ Fin M' :=
  ⟨fun i => ⟨r + 1 + i.1, by dsimp only [regM']; omega⟩, fun i j h => Fin.ext (by
    have := congrArg Fin.val h; dsimp at this; omega)⟩

def regW : Fin ℓ ↪ Fin M' :=
  ⟨fun i => ⟨r + 1 + n + i.1, by dsimp only [regM']; omega⟩, fun i j h => Fin.ext (by
    have := congrArg Fin.val h; dsimp at this; omega)⟩

def wireFC : Fin M' := ⟨r + 1 + n + ℓ, by dsimp only [regM']; omega⟩
def wireFH : Fin M' := ⟨r + 1 + n + ℓ + 1, by dsimp only [regM']; omega⟩
def wireFQ : Fin M' := ⟨r + 1 + n + ℓ + 2, by dsimp only [regM']; omega⟩

def regAnc : Fin Amax ↪ Fin M' :=
  ⟨fun i => ⟨r + 1 + n + ℓ + 3 + i.1, by dsimp only [regM']; omega⟩, fun i j h => Fin.ext (by
    have := congrArg Fin.val h; dsimp at this; omega)⟩

@[simp] lemma regC_val (i : Fin r) : (regC (ps := ps) (r := r) (n := n) i).1 = i.1 := rfl
@[simp] lemma wireD_val : (wireD (ps := ps) (r := r) (n := n)).1 = r := rfl
@[simp] lemma regQ_val (i : Fin n) : (regQ (ps := ps) (r := r) (n := n) i).1 = r + 1 + i.1 := rfl
@[simp] lemma regW_val (i : Fin ℓ) : (regW (ps := ps) (r := r) (n := n) i).1 = r + 1 + n + i.1 := rfl
@[simp] lemma wireFC_val : (wireFC (ps := ps) (r := r) (n := n)).1 = r + 1 + n + ℓ := rfl
@[simp] lemma wireFH_val : (wireFH (ps := ps) (r := r) (n := n)).1 = r + 1 + n + ℓ + 1 := rfl
@[simp] lemma wireFQ_val : (wireFQ (ps := ps) (r := r) (n := n)).1 = r + 1 + n + ℓ + 2 := rfl
@[simp] lemma regAnc_val (i : Fin Amax) :
    (regAnc (ps := ps) (r := r) (n := n) i).1 = r + 1 + n + ℓ + 3 + i.1 := rfl

def packState (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) : Qubits M' :=
  fun i =>
    if h0 : i.1 < r then c ⟨i.1, h0⟩
    else if h1 : i.1 = r then d
    else if h2 : i.1 < r + 1 + n then q ⟨i.1 - (r + 1), by omega⟩
    else if h3 : i.1 < r + 1 + n + ℓ then w ⟨i.1 - (r + 1 + n), by omega⟩
    else if h4 : i.1 = r + 1 + n + ℓ then fc
    else if h5 : i.1 = r + 1 + n + ℓ + 1 then fh
    else if h6 : i.1 = r + 1 + n + ℓ + 2 then fq
    else a ⟨i.1 - (r + 1 + n + ℓ + 3), by dsimp only [regM'] at *; omega⟩

lemma packState_C (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) (i : Fin r) :
    packState c d q w fc fh fq a (regC i) = c i := by
  simp only [packState, regC_val, i.isLt, ↓reduceDIte]

lemma packState_D (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) :
    packState c d q w fc fh fq a wireD = d := by
  simp only [packState, wireD_val, lt_self_iff_false, ↓reduceDIte]

lemma packState_Q (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) (i : Fin n) :
    packState c d q w fc fh fq a (regQ i) = q i := by
  have hi := i.isLt
  have h0 : ¬ (r + 1 + i.1 < r) := by omega
  have h1 : r + 1 + i.1 ≠ r := by omega
  have h2 : r + 1 + i.1 < r + 1 + n := by omega
  simp only [packState, regQ_val, h0, h1, h2, ↓reduceDIte]
  congr 1; ext; rw [Fin.val_mk]; omega

lemma packState_W (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) (i : Fin ℓ) :
    packState c d q w fc fh fq a (regW i) = w i := by
  have hi := i.isLt
  have h0 : ¬ (r + 1 + n + i.1 < r) := by omega
  have h1 : r + 1 + n + i.1 ≠ r := by omega
  have h2 : ¬ (r + 1 + n + i.1 < r + 1 + n) := by omega
  have h3 : r + 1 + n + i.1 < r + 1 + n + ℓ := by omega
  simp only [packState, regW_val, h0, h1, h2, h3, ↓reduceDIte]
  congr 1; ext; rw [Fin.val_mk]; omega

lemma packState_FC (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) :
    packState c d q w fc fh fq a wireFC = fc := by
  have h0 : ¬ (r + 1 + n + ℓ < r) := by omega
  have h1 : r + 1 + n + ℓ ≠ r := by omega
  have h2 : ¬ (r + 1 + n + ℓ < r + 1 + n) := by omega
  have h3 : ¬ (r + 1 + n + ℓ < r + 1 + n + ℓ) := by omega
  simp only [packState, wireFC_val, h0, h1, h2, h3, ↓reduceDIte]

lemma packState_FH (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) :
    packState c d q w fc fh fq a wireFH = fh := by
  have h0 : ¬ (r + 1 + n + ℓ + 1 < r) := by omega
  have h1 : r + 1 + n + ℓ + 1 ≠ r := by omega
  have h2 : ¬ (r + 1 + n + ℓ + 1 < r + 1 + n) := by omega
  have h3 : ¬ (r + 1 + n + ℓ + 1 < r + 1 + n + ℓ) := by omega
  have h4 : r + 1 + n + ℓ + 1 ≠ r + 1 + n + ℓ := by omega
  simp only [packState, wireFH_val, h0, h1, h2, h3, h4, ↓reduceDIte]

lemma packState_FQ (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) :
    packState c d q w fc fh fq a wireFQ = fq := by
  have h0 : ¬ (r + 1 + n + ℓ + 2 < r) := by omega
  have h1 : r + 1 + n + ℓ + 2 ≠ r := by omega
  have h2 : ¬ (r + 1 + n + ℓ + 2 < r + 1 + n) := by omega
  have h3 : ¬ (r + 1 + n + ℓ + 2 < r + 1 + n + ℓ) := by omega
  have h4 : r + 1 + n + ℓ + 2 ≠ r + 1 + n + ℓ := by omega
  have h5 : r + 1 + n + ℓ + 2 ≠ r + 1 + n + ℓ + 1 := by omega
  simp only [packState, wireFQ_val, h0, h1, h2, h3, h4, h5, ↓reduceDIte]

lemma packState_Anc (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) (i : Fin Amax) :
    packState c d q w fc fh fq a (regAnc i) = a i := by
  have h0 : ¬ (r + 1 + n + ℓ + 3 + i.1 < r) := by omega
  have h1 : r + 1 + n + ℓ + 3 + i.1 ≠ r := by omega
  have h2 : ¬ (r + 1 + n + ℓ + 3 + i.1 < r + 1 + n) := by omega
  have h3 : ¬ (r + 1 + n + ℓ + 3 + i.1 < r + 1 + n + ℓ) := by omega
  have h4 : r + 1 + n + ℓ + 3 + i.1 ≠ r + 1 + n + ℓ := by omega
  have h5 : r + 1 + n + ℓ + 3 + i.1 ≠ r + 1 + n + ℓ + 1 := by omega
  have h6 : r + 1 + n + ℓ + 3 + i.1 ≠ r + 1 + n + ℓ + 2 := by omega
  simp only [packState, regAnc_val, h0, h1, h2, h3, h4, h5, h6, ↓reduceDIte]
  congr 1; ext; rw [Fin.val_mk]; omega

lemma packState_eq_of_C (c₁ c₂ : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) (i : Fin M')
    (hi : ∀ k : Fin r, regC k = i → c₁ k = c₂ k) :
    packState c₁ d q w fc fh fq a i = packState c₂ d q w fc fh fq a i := by
  by_cases h0 : i.1 < r
  · simp only [packState, h0, ↓reduceDIte]
    exact hi ⟨i.1, h0⟩ (Fin.ext rfl)
  · simp only [packState, h0, ↓reduceDIte]

lemma packState_eq_of_D (c : Qubits r) (d₁ d₂ : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) (i : Fin M') (hi : i ≠ wireD) :
    packState c d₁ q w fc fh fq a i = packState c d₂ q w fc fh fq a i := by
  by_cases h0 : i.1 < r
  · simp only [packState, h0, ↓reduceDIte]
  · by_cases h1 : i.1 = r
    · exact absurd (Fin.ext h1 : i = wireD) hi
    · simp only [packState, h0, ↓reduceDIte, h1]

lemma packState_eq_of_Q (c : Qubits r) (d : Bool) (q₁ q₂ : Qubits n) (w : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) (i : Fin M') (hi : ∀ j : Fin n, regQ j ≠ i) :
    packState c d q₁ w fc fh fq a i = packState c d q₂ w fc fh fq a i := by
  by_cases h0 : i.1 < r
  · simp only [packState, h0, ↓reduceDIte]
  · by_cases h1 : i.1 = r
    · simp only [packState, ↓reduceDIte, h1]
    · by_cases h2 : i.1 < r + 1 + n
      · exact absurd (Fin.ext (by simp only [regQ_val]; omega) : regQ ⟨i.1 - (r + 1), by omega⟩ = i)
          (hi ⟨i.1 - (r + 1), by omega⟩)
      · simp only [packState, ↓reduceDIte, h1, h2]

lemma packState_eq_of_W (c : Qubits r) (d : Bool) (q : Qubits n) (w₁ w₂ : Qubits ℓ)
    (fc fh fq : Bool) (a : Qubits Amax) (i : Fin M') (hi : ∀ j : Fin ℓ, regW j ≠ i) :
    packState c d q w₁ fc fh fq a i = packState c d q w₂ fc fh fq a i := by
  by_cases h0 : i.1 < r
  · simp only [packState, h0, ↓reduceDIte]
  · by_cases h1 : i.1 = r
    · simp only [packState, ↓reduceDIte, h1]
    · by_cases h2 : i.1 < r + 1 + n
      · simp only [packState, ↓reduceDIte, h1, h2]
      · by_cases h3 : i.1 < r + 1 + n + ℓ
        · exact absurd (Fin.ext (by simp only [regW_val]; omega) : regW ⟨i.1 - (r + 1 + n), by omega⟩ = i)
            (hi ⟨i.1 - (r + 1 + n), by omega⟩)
        · simp only [packState, ↓reduceDIte, h1, h2, h3]

lemma packState_eq_of_FC (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc₁ fc₂ fh fq : Bool) (a : Qubits Amax) (i : Fin M') (hi : i ≠ wireFC) :
    packState c d q w fc₁ fh fq a i = packState c d q w fc₂ fh fq a i := by
  by_cases h0 : i.1 < r
  · simp only [packState, h0, ↓reduceDIte]
  · by_cases h1 : i.1 = r
    · simp only [packState, ↓reduceDIte, h1]
    · by_cases h2 : i.1 < r + 1 + n
      · simp only [packState, ↓reduceDIte, h1, h2]
      · by_cases h3 : i.1 < r + 1 + n + ℓ
        · simp only [packState, ↓reduceDIte, h1, h2, h3]
        · by_cases h4 : i.1 = r + 1 + n + ℓ
          · exact absurd (Fin.ext h4 : i = wireFC) hi
          · simp only [packState, ↓reduceDIte, h1, h2, h3, h4]

lemma packState_eq_of_FH (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh₁ fh₂ fq : Bool) (a : Qubits Amax) (i : Fin M') (hi : i ≠ wireFH) :
    packState c d q w fc fh₁ fq a i = packState c d q w fc fh₂ fq a i := by
  by_cases h0 : i.1 < r
  · simp only [packState, h0, ↓reduceDIte]
  · by_cases h1 : i.1 = r
    · simp only [packState, ↓reduceDIte, h1]
    · by_cases h2 : i.1 < r + 1 + n
      · simp only [packState, ↓reduceDIte, h1, h2]
      · by_cases h3 : i.1 < r + 1 + n + ℓ
        · simp only [packState, ↓reduceDIte, h1, h2, h3]
        · by_cases h4 : i.1 = r + 1 + n + ℓ
          · simp only [packState, ↓reduceDIte, h4]
          · by_cases h5 : i.1 = r + 1 + n + ℓ + 1
            · exact absurd (Fin.ext h5 : i = wireFH) hi
            · simp only [packState, ↓reduceDIte, h1, h2, h3, h4, h5]

lemma packState_eq_of_FQ (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ)
    (fc fh fq₁ fq₂ : Bool) (a : Qubits Amax) (i : Fin M') (hi : i ≠ wireFQ) :
    packState c d q w fc fh fq₁ a i = packState c d q w fc fh fq₂ a i := by
  by_cases h0 : i.1 < r
  · simp only [packState, h0, ↓reduceDIte]
  · by_cases h1 : i.1 = r
    · simp only [packState, ↓reduceDIte, h1]
    · by_cases h2 : i.1 < r + 1 + n
      · simp only [packState, ↓reduceDIte, h1, h2]
      · by_cases h3 : i.1 < r + 1 + n + ℓ
        · simp only [packState, ↓reduceDIte, h1, h2, h3]
        · by_cases h4 : i.1 = r + 1 + n + ℓ
          · simp only [packState, ↓reduceDIte, h4]
          · by_cases h5 : i.1 = r + 1 + n + ℓ + 1
            · simp only [packState, ↓reduceDIte, h5]
            · by_cases h6 : i.1 = r + 1 + n + ℓ + 2
              · exact absurd (Fin.ext h6 : i = wireFQ) hi
              · simp only [packState, ↓reduceDIte, h1, h2, h3, h4, h5, h6]

lemma packState_zero :
    packState (ps := ps) (r := r) (n := n)
      (fun _ => false) false (fun _ => false) (fun _ => false) false false false (fun _ => false) =
    fun _ => false := by
  funext i
  simp only [packState]
  split_ifs <;> rfl

lemma packState_inj {c₁ c₂ : Qubits r} {d₁ d₂ : Bool} {q₁ q₂ : Qubits n} {w₁ w₂ : Qubits ℓ}
    {fc₁ fc₂ fh₁ fh₂ fq₁ fq₂ : Bool} {a₁ a₂ : Qubits Amax}
    (h : packState (ps := ps) c₁ d₁ q₁ w₁ fc₁ fh₁ fq₁ a₁ =
         packState (ps := ps) c₂ d₂ q₂ w₂ fc₂ fh₂ fq₂ a₂) :
    c₁ = c₂ ∧ d₁ = d₂ ∧ q₁ = q₂ ∧ w₁ = w₂ ∧ fc₁ = fc₂ ∧ fh₁ = fh₂ ∧ fq₁ = fq₂ ∧ a₁ = a₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; have := congrFun h (regC i); rwa [packState_C, packState_C] at this
  · have := congrFun h wireD; rwa [packState_D, packState_D] at this
  · funext i; have := congrFun h (regQ i); rwa [packState_Q, packState_Q] at this
  · funext i; have := congrFun h (regW i); rwa [packState_W, packState_W] at this
  · have := congrFun h wireFC; rwa [packState_FC, packState_FC] at this
  · have := congrFun h wireFH; rwa [packState_FH, packState_FH] at this
  · have := congrFun h wireFQ; rwa [packState_FQ, packState_FQ] at this
  · funext i; have := congrFun h (regAnc i); rwa [packState_Anc, packState_Anc] at this

def coreEmb (p : Qubits r × Bool × Qubits n) : Qubits M' :=
  packState (ps := ps) p.1 p.2.1 p.2.2 (fun _ => false) false false false (fun _ => false)

lemma coreEmb_inj : Function.Injective (coreEmb (ps := ps) (r := r) (n := n)) := by
  intro p₁ p₂ h
  rcases p₁ with ⟨c₁, d₁, q₁⟩; rcases p₂ with ⟨c₂, d₂, q₂⟩
  obtain ⟨hc, hd, hq, _⟩ := packState_inj h
  exact Prod.ext hc (Prod.ext hd hq)

def coreEmbHom : (Qubits r × Bool × Qubits n) ↪ Qubits M' :=
  ⟨coreEmb, coreEmb_inj⟩

@[simp] lemma coreEmbHom_apply (p : Qubits r × Bool × Qubits n) :
    coreEmbHom (ps := ps) (r := r) (n := n) p = coreEmb (ps := ps) (r := r) (n := n) p := rfl

end FixedParams

end FullCircuit

section DepthEmbed

lemma nonOracleDepth_embedCircuit {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m₀ m : ℕ}
    (emb : Fin m₀ ↪ Fin m) (c : Circuit S m₀) :
    nonOracleDepth ((embedCircuit emb c).map OracleStep.gate : OracleCircuit S a m) ≤
      nonOracleDepth (c.map OracleStep.gate : OracleCircuit S a m₀) := by
  have hinv : ∀ (l : Circuit S m₀) (τ₀ : Fin m₀ → ℕ) (τ : Fin m → ℕ),
      (∀ i : Fin m₀, τ (emb i) = τ₀ i) →
      (∀ j : Fin m, j ∉ Set.range emb → τ j = 0) →
      let τ₀' := (l.map OracleStep.gate : OracleCircuit S a m₀).foldl stepTimeUpdate τ₀
      let τ' := ((embedCircuit emb l).map OracleStep.gate : OracleCircuit S a m).foldl stepTimeUpdate τ
      (∀ i : Fin m₀, τ' (emb i) = τ₀' i) ∧ (∀ j : Fin m, j ∉ Set.range emb → τ' j = 0) := by
    intro l
    induction l with
    | nil => intro τ₀ τ h1 h2; exact ⟨h1, h2⟩
    | cons g gs ih =>
      intro τ₀ τ h1 h2
      simp only [embedCircuit, List.map_cons, List.foldl_cons]
      let st₀ : OracleStep S a m₀ := OracleStep.gate g
      let st : OracleStep S a m := OracleStep.gate ⟨g.gate, g.mem, g.wires.trans emb⟩
      have hws : stepWireSet st = (stepWireSet st₀).image emb := by
        ext x
        simp only [st, st₀, stepWireSet, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨u, rfl⟩; exact ⟨g.wires u, ⟨u, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨u, rfl⟩, rfl⟩; exact ⟨u, rfl⟩
      have hsup : (stepWireSet st).sup τ = (stepWireSet st₀).sup τ₀ := by
        rw [hws, Finset.sup_image]
        refine Finset.sup_congr rfl fun i _ => h1 i
      refine ih (stepTimeUpdate τ₀ st₀) (stepTimeUpdate τ st) ?_ ?_
      · intro i
        dsimp only [stepTimeUpdate]
        have hmem : emb i ∈ stepWireSet st ↔ i ∈ stepWireSet st₀ := by
          rw [hws, Finset.mem_image]
          constructor
          · rintro ⟨x, hx, hxi⟩; rwa [← emb.injective hxi]
          · intro hi; exact ⟨i, hi, rfl⟩
        rw [hsup]
        by_cases hi : i ∈ stepWireSet st₀
        · rw [if_pos (hmem.mpr hi), if_pos hi]; rfl
        · rw [if_neg (fun h => hi (hmem.mp h)), if_neg hi, h1 i]
      · intro j hj
        dsimp only [stepTimeUpdate]
        have hnot : j ∉ stepWireSet st := by
          rw [hws, Finset.mem_image]
          rintro ⟨x, _, rfl⟩
          exact hj ⟨x, rfl⟩
        rw [if_neg hnot]
        exact h2 j hj
  have hmain := hinv c (fun _ => 0) (fun _ => 0) (fun _ => rfl) (fun _ _ => rfl)
  change Finset.univ.sup (((embedCircuit emb c).map OracleStep.gate : OracleCircuit S a m).foldl
      stepTimeUpdate (fun _ => 0)) ≤
    Finset.univ.sup ((c.map OracleStep.gate : OracleCircuit S a m₀).foldl stepTimeUpdate (fun _ => 0))
  refine Finset.sup_le fun j _ => ?_
  by_cases hj : j ∈ Set.range emb
  · obtain ⟨i, rfl⟩ := hj
    rw [hmain.1 i]
    exact Finset.le_sup (Finset.mem_univ i)
  · rw [hmain.2 j hj]
    exact Nat.zero_le _

end DepthEmbed

section SubCircuitEmbeddings

variable {ps : PrimitiveSuite} {r n : ℕ}

local notation "ℓ" => Nat.clog 2 (n + 1)
local notation "Amax" => ancMax ps r n
local notation "M'" => regM' ps r n

/-! ### Embeddings of primitive registers into `Fin M'` -/

def embToffoli : Fin 3 ↪ Fin M' :=
  let f : Fin 3 → Fin M' := fun i => if i.1 = 0 then wireFC else if i.1 = 1 then wireD else wireFH
  ⟨f, fun a b hab => by
    have hv : (f a).1 = (f b).1 := congrArg Fin.val hab
    fin_cases a <;> fin_cases b <;>
      simp [f, wireFC_val, wireD_val, wireFH_val] at hv <;>
      first | rfl | omega⟩

@[simp] lemma embToffoli_apply (i : Fin 3) :
    embToffoli (ps := ps) (r := r) (n := n) i =
      if i.1 = 0 then wireFC else if i.1 = 1 then wireD else wireFH := rfl

def embCH (hn : 1 ≤ n) : Fin (1 + n + ps.ancCH n) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 = 0 then wireFH
    else if h1 : i.1 < 1 + n then regQ ⟨i.1 - 1, by omega⟩
    else regAnc ⟨i.1 - (1 + n), by
      have _hi := i.isLt
      have hle : ps.ancCH n ≤ Amax := le_max_left _ _
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;>
      simp only [wireFH_val, regQ_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embCH_apply (hn : 1 ≤ n) (i : Fin (1 + n + ps.ancCH n)) :
    embCH (ps := ps) (r := r) (n := n) hn i =
      if h0 : i.1 = 0 then wireFH
      else if h1 : i.1 < 1 + n then regQ ⟨i.1 - 1, by omega⟩
      else regAnc ⟨i.1 - (1 + n), by
        have _hi := i.isLt
        have hle : ps.ancCH n ≤ Amax := le_max_left _ _
        omega⟩ := rfl

def embEqFQ : Fin ((r + 1) + 1 + ps.ancEq (r + 1)) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 < r then regC ⟨i.1, h0⟩
    else if h1 : i.1 = r then wireD
    else if h2 : i.1 = r + 1 then wireFQ
    else regAnc ⟨i.1 - (r + 2), by
      have _hi := i.isLt
      have hle : ps.ancEq (r + 1) ≤ Amax := le_trans (le_max_left _ _) (le_max_right _ _)
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;>
      simp only [regC_val, wireD_val, wireFQ_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embEqFQ_apply (i : Fin ((r + 1) + 1 + ps.ancEq (r + 1))) :
    embEqFQ (ps := ps) (r := r) (n := n) i =
      if h0 : i.1 < r then regC ⟨i.1, h0⟩
      else if h1 : i.1 = r then wireD
      else if h2 : i.1 = r + 1 then wireFQ
      else regAnc ⟨i.1 - (r + 2), by
        have _hi := i.isLt
        have hle : ps.ancEq (r + 1) ≤ Amax := le_trans (le_max_left _ _) (le_max_right _ _)
        omega⟩ := rfl

def embEqFC : Fin (r + 1 + ps.ancEq r) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 < r then regC ⟨i.1, h0⟩
    else if h1 : i.1 = r then wireFC
    else regAnc ⟨i.1 - (r + 1), by
      have _hi := i.isLt
      have hle : ps.ancEq r ≤ Amax :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;>
      simp only [regC_val, wireFC_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embEqFC_apply (i : Fin (r + 1 + ps.ancEq r)) :
    embEqFC (ps := ps) (r := r) (n := n) i =
      if h0 : i.1 < r then regC ⟨i.1, h0⟩
      else if h1 : i.1 = r then wireFC
      else regAnc ⟨i.1 - (r + 1), by
        have _hi := i.isLt
        have hle : ps.ancEq r ≤ Amax :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
        omega⟩ := rfl

def embHC : Fin (n + ℓ + ps.ancHC n) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 < n then regQ ⟨i.1, h0⟩
    else if h1 : i.1 < n + ℓ then regW ⟨i.1 - n, by omega⟩
    else regAnc ⟨i.1 - (n + ℓ), by
      have _hi := i.isLt
      have hle : ps.ancHC n ≤ Amax :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_max_right _ _))))
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;>
      simp only [regQ_val, regW_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embHC_apply (i : Fin (n + ℓ + ps.ancHC n)) :
    embHC (ps := ps) (r := r) (n := n) i =
      if h0 : i.1 < n then regQ ⟨i.1, h0⟩
      else if h1 : i.1 < n + ℓ then regW ⟨i.1 - n, by omega⟩
      else regAnc ⟨i.1 - (n + ℓ), by
        have _hi := i.isLt
        have hle : ps.ancHC n ≤ Amax :=
          le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _))))
        omega⟩ := rfl

def embEqWFull : Fin ((1 + ℓ) + 1 + ps.ancEq (1 + ℓ)) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 = 0 then wireFC
    else if h1 : i.1 < 1 + ℓ then regW ⟨i.1 - 1, by omega⟩
    else if h2 : i.1 = 1 + ℓ then wireD
    else regAnc ⟨i.1 - (2 + ℓ), by
      have _hi := i.isLt
      have hle : ps.ancEq (1 + ℓ) ≤ Amax :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_max_right _ _)))
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;>
      simp only [wireFC_val, regW_val, wireD_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embEqWFull_apply (i : Fin ((1 + ℓ) + 1 + ps.ancEq (1 + ℓ))) :
    embEqWFull (ps := ps) (r := r) (n := n) i =
      if h0 : i.1 = 0 then wireFC
      else if h1 : i.1 < 1 + ℓ then regW ⟨i.1 - 1, by omega⟩
      else if h2 : i.1 = 1 + ℓ then wireD
      else regAnc ⟨i.1 - (2 + ℓ), by
        have _hi := i.isLt
        have hle : ps.ancEq (1 + ℓ) ≤ Amax :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_max_right _ _)))
        omega⟩ := rfl

def embEqWBit1 (hℓ : 2 ≤ ℓ) : Fin (2 + 1 + ps.ancEq 2) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 = 0 then wireFC
    else if h1 : i.1 = 1 then regW ⟨1, by omega⟩
    else if h2 : i.1 = 2 then wireD
    else regAnc ⟨i.1 - 3, by
      have hi := i.isLt
      have hle : ps.ancEq 2 ≤ Amax :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_max_right _ _))))
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;>
      simp only [wireFC_val, regW_val, wireD_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embEqWBit1_apply (hℓ : 2 ≤ ℓ) (i : Fin (2 + 1 + ps.ancEq 2)) :
    embEqWBit1 (ps := ps) (r := r) (n := n) hℓ i =
      if h0 : i.1 = 0 then wireFC
      else if h1 : i.1 = 1 then regW ⟨1, by omega⟩
      else if h2 : i.1 = 2 then wireD
      else regAnc ⟨i.1 - 3, by
        have hi := i.isLt
        have hle : ps.ancEq 2 ≤ Amax :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _))))
        omega⟩ := rfl

/-! ### Self-contained `ctrl0XCirc` (XOR `pat` into `regC` iff `wireD = false`) -/

def ctrl0XPairEmb (j : Fin r) : Fin 2 ↪ Fin M' :=
  let f : Fin 2 → Fin M' := fun i => if i.1 = 0 then wireD else regC j
  ⟨f, fun a b hab => by
    have hj := j.isLt
    have hv : (f a).1 = (f b).1 := congrArg Fin.val hab
    fin_cases a <;> fin_cases b <;>
      simp [f, wireD_val, regC_val] at hv <;>
      first | rfl | omega⟩

@[simp] lemma ctrl0XPairEmb_apply (j : Fin r) (i : Fin 2) :
    ctrl0XPairEmb (ps := ps) (r := r) (n := n) j i = if i.1 = 0 then wireD else regC j := rfl

def ctrl0XStepGate (pat : Qubits r) (j : Fin r) : GateApp gates12 M' :=
  ⟨Gate.ofMatrix2 (if pat j then ctrl0XMat else 1),
    gate_ofMatrix2_mem_gates12 (by split_ifs; exact ctrl0XMat_mem_unitaryGroup; exact Submonoid.one_mem _),
    ctrl0XPairEmb j⟩

def ctrl0XCirc (pat : Qubits r) : Circuit gates12 M' :=
  List.ofFn (ctrl0XStepGate pat)

lemma ctrl0XCirc_length (pat : Qubits r) : (ctrl0XCirc (ps := ps) (r := r) (n := n) pat).length = r := by
  simp [ctrl0XCirc]

lemma act_ctrl0XStepGate (pat : Qubits r) (j : Fin r) (c : Qubits r) (d : Bool) (q : Qubits n)
    (w : Qubits ℓ) (fc fh fq : Bool) (a : Qubits Amax) :
    act (embedOp (ctrl0XStepGate pat j).gate.mat (ctrl0XStepGate pat j).wires)
        (ket (packState (ps := ps) c d q w fc fh fq a)) =
      ket (packState (ps := ps)
        (fun i => if i = j then (if d then c i else xor (c i) (pat j)) else c i)
        d q w fc fh fq a) := by
  let z := packState (ps := ps) c d q w fc fh fq a
  let z' := packState (ps := ps)
    (fun i => if i = j then (if d then c i else xor (c i) (pat j)) else c i) d q w fc fh fq a
  refine act_embedOp_basis_map (ctrl0XPairEmb j) (ctrl0XStepGate pat j).gate.mat z (z' ∘ ctrl0XPairEmb j) ?_ z' rfl ?_
  · ext x
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ctrl0XStepGate, Gate.ofMatrix2,
      Matrix.submatrix_apply, ket, PiLp.single_apply]
    rw [Finset.sum_eq_single (z ∘ ctrl0XPairEmb j)]
    · simp only [↓reduceIte, mul_one]
      have h0 : (z ∘ ctrl0XPairEmb j) 0 = d := by
        simp only [Function.comp_apply, ctrl0XPairEmb_apply]; exact packState_D _ _ _ _ _ _ _ _
      have h1 : (z ∘ ctrl0XPairEmb j) 1 = c j := by
        simp only [Function.comp_apply, ctrl0XPairEmb_apply]; exact packState_C _ _ _ _ _ _ _ _ j
      have hz'0 : (z' ∘ ctrl0XPairEmb j) 0 = d := by
        simp only [Function.comp_apply, ctrl0XPairEmb_apply]; exact packState_D _ _ _ _ _ _ _ _
      have hz'1 : (z' ∘ ctrl0XPairEmb j) 1 = if d then c j else xor (c j) (pat j) := by
        rw [Function.comp_apply, ctrl0XPairEmb_apply]
        simp [z', packState_C]
      have heq_x : (x = z' ∘ ctrl0XPairEmb j) ↔
          (x 0 = d ∧ x 1 = (if d then c j else xor (c j) (pat j))) := by
        constructor
        · intro h; rw [h, hz'0, hz'1]; exact ⟨rfl, rfl⟩
        · rintro ⟨hx0, hx1⟩; funext i; fin_cases i
          · change x 0 = (z' ∘ ctrl0XPairEmb j) 0; rw [hx0, hz'0]
          · change x 1 = (z' ∘ ctrl0XPairEmb j) 1; rw [hx1, hz'1]
      by_cases hpat : pat j = true
      · have heq_x' : (x = z' ∘ ctrl0XPairEmb j) ↔
            (x 0 = d ∧ x 1 = (if d then c j else !(c j))) := by
          simpa [hpat] using heq_x
        simp only [hpat, ↓reduceIte, ctrl0XMat, Matrix.of_apply, h0, h1]
        by_cases hx : x = z' ∘ ctrl0XPairEmb j
        · rw [if_pos hx, if_pos (heq_x'.mp hx)]
        · rw [if_neg hx, if_neg (fun h => hx (heq_x'.mpr h))]
      · have hpf : pat j = false := Bool.eq_false_iff.mpr hpat
        simp only [hpf, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply, Prod.mk.injEq, h0, h1]
        by_cases hx : x = z' ∘ ctrl0XPairEmb j
        · rw [if_pos hx]; have hx' := heq_x.mp hx; simp [hpf, hx']
        · rw [if_neg hx]; rw [if_neg]; rintro ⟨hx0, hx1⟩; apply hx; apply heq_x.mpr; simp [hpf, hx0, hx1]
    · intro u _ hu; simp [hu]
    · simp
  · intro i hi
    refine packState_eq_of_C (ps := ps) _ c d q w fc fh fq a i fun k hk => ?_
    by_cases hkj : k = j
    · subst hkj; exact absurd hk (fun h => hi ⟨1, h⟩)
    · simp [hkj]

lemma act_ctrl0XCirc (pat : Qubits r) (c : Qubits r) (d : Bool) (q : Qubits n)
    (w : Qubits ℓ) (fc fh fq : Bool) (a : Qubits Amax) :
    act (ctrl0XCirc (ps := ps) (r := r) (n := n) pat).unitary
        (ket (packState (ps := ps) c d q w fc fh fq a)) =
      ket (packState (ps := ps) (fun i => if d then c i else xor (c i) (pat i))
        d q w fc fh fq a) := by
  have hpref : ∀ (k : ℕ) (hk : k ≤ r),
      act (Circuit.unitary (List.ofFn fun j : Fin k => ctrl0XStepGate (ps := ps) (r := r) (n := n) pat
          (Fin.castLE hk j)))
        (ket (packState (ps := ps) c d q w fc fh fq a)) =
      ket (packState (ps := ps)
        (fun i => if i.1 < k then (if d then c i else xor (c i) (pat i)) else c i)
        d q w fc fh fq a) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [Circuit.unitary, act_one_vec]
    | succ k ih =>
      intro hk
      have hk_le : k ≤ r := Nat.le_of_lt hk
      have hfn : (List.ofFn fun j : Fin (k + 1) => ctrl0XStepGate (ps := ps) (r := r) (n := n) pat
            (Fin.castLE hk j)) =
          (List.ofFn fun j : Fin k => ctrl0XStepGate (ps := ps) (r := r) (n := n) pat
            (Fin.castLE hk_le j)) ++
          [ctrl0XStepGate (ps := ps) (r := r) (n := n) pat ⟨k, hk⟩] := by
        rw [List.ofFn_succ', List.concat_eq_append]
        rfl
      have hunit : Circuit.unitary (List.ofFn fun j : Fin (k + 1) => ctrl0XStepGate (ps := ps) (r := r) (n := n) pat
            (Fin.castLE hk j)) =
          embedOp (ctrl0XStepGate pat ⟨k, hk⟩).gate.mat (ctrl0XStepGate pat ⟨k, hk⟩).wires *
          Circuit.unitary (List.ofFn fun j : Fin k => ctrl0XStepGate (ps := ps) (r := r) (n := n) pat
            (Fin.castLE hk_le j)) := by
        rw [hfn]
        simp [Circuit.unitary]
      rw [hunit, act_mul, ih hk_le, act_ctrl0XStepGate]
      congr 1
      ext idx
      by_cases h0 : idx.1 < r
      · simp only [packState, h0, ↓reduceDIte]
        by_cases hik : idx.1 < k
        · have hik1 : idx.1 < k + 1 := by omega
          have hne : (⟨idx.1, h0⟩ : Fin r) ≠ ⟨k, hk⟩ := fun h => by
            have hval : idx.1 = k := congrArg Fin.val h
            omega
          simp [hik, hik1, hne]
        · by_cases hiek : idx.1 = k
          · have hlt : idx.1 < k + 1 := by omega
            have heq : (⟨idx.1, h0⟩ : Fin r) = ⟨k, hk⟩ := Fin.ext hiek
            simp [hik, hlt, heq]
          · have hn1 : ¬ idx.1 < k + 1 := by omega
            have hne : (⟨idx.1, h0⟩ : Fin r) ≠ ⟨k, hk⟩ := fun h => by
              have := congrArg Fin.val h; exact hiek this
            simp [hik, hn1, hne]
      · simp [packState, h0]
  have hfull := hpref r le_rfl
  simpa [ctrl0XCirc, Fin.isLt] using hfull

/-! ### Self-contained `hadamardLayerC` (parallel `H` on all `r` clock qubits) -/

def singleWireEmb (w : Fin M') : Fin 1 ↪ Fin M' :=
  ⟨fun _ => w, fun a b _ => Subsingleton.elim a b⟩

@[simp] lemma singleWireEmb_apply (w : Fin M') (i : Fin 1) :
    singleWireEmb (ps := ps) (r := r) (n := n) w i = w := rfl

noncomputable def hadamardGateAt (w : Fin M') : GateApp gates12 M' :=
  ⟨Gate.ofMatrix1 hadamard, gate_ofMatrix1_mem_gates12 hadamard_mem_unitaryGroup, singleWireEmb w⟩

noncomputable def hadamardLayerC : Circuit gates12 M' :=
  List.ofFn fun j : Fin r => hadamardGateAt (regC j)

lemma hadamardLayerC_length : (hadamardLayerC (ps := ps) (r := r) (n := n)).length = r := by
  simp [hadamardLayerC]

lemma hadamardLayerC_depth_le_one {a : Fin 1 → ℕ} :
    nonOracleDepth ((hadamardLayerC (ps := ps) (r := r) (n := n)).map OracleStep.gate :
      OracleCircuit gates12 a M') ≤ 1 := by
  refine nonOracleDepth_disjoint_gates_le_one _ ?_
  rw [hadamardLayerC, List.pairwise_ofFn]
  intro i j hij
  rw [Set.disjoint_left]
  rintro x ⟨_, rfl⟩ ⟨_, hx⟩
  simp only [hadamardGateAt] at hx
  exact hij.ne (regC.injective hx.symm)

private lemma hadamard_ket_false :
    act hadamard (ket false) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ket false + ket true) := by
  ext b
  cases b <;> simp [act, hadamard, ket]

private def qubitsSnocEquiv (M : ℕ) : Qubits (M + 1) ≃ Qubits M × Bool where
  toFun z := (Fin.init z, z (Fin.last M))
  invFun p := Fin.snoc (α := fun _ => Bool) p.1 p.2
  left_inv z := Fin.snoc_init_self z
  right_inv p := by ext <;> simp

lemma act_hadamardGateAt_false (j : Fin r) (c : Qubits r) (hc : c j = false) (d : Bool) (q : Qubits n)
    (w : Qubits ℓ) (fc fh fq : Bool) (a : Qubits Amax) :
    act (embedOp (hadamardGateAt (ps := ps) (r := r) (n := n) (regC j)).gate.mat
          (hadamardGateAt (regC j)).wires)
        (ket (packState (ps := ps) c d q w fc fh fq a)) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        (ket (packState (ps := ps) (Function.update c j false) d q w fc fh fq a) +
         ket (packState (ps := ps) (Function.update c j true) d q w fc fh fq a)) := by
  let z := packState (ps := ps) c d q w fc fh fq a
  let z' : Bool → Qubits M' := fun b =>
    packState (ps := ps) (Function.update c j b) d q w fc fh fq a
  change act (embedOp (Gate.ofMatrix1 hadamard).mat
    (singleWireEmb (ps := ps) (r := r) (n := n) (regC j))) (ket z) = _
  trans (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ket (z' true) + ket (z' false))
  · rw [smul_add]
    have hsum_eq : (∑ b : Bool, (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (z' b)) =
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (z' true) +
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (z' false) := Fintype.sum_bool _
    rw [← hsum_eq]
    refine act_embedOp_basis_sum (singleWireEmb (ps := ps) (r := r) (n := n) (regC j))
      (Gate.ofMatrix1 hadamard).mat z
      (fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ))
      (fun b _ => b) z' ?_ ?_ ?_
    · ext u
      have hz0 : (z ∘ singleWireEmb (ps := ps) (r := r) (n := n) (regC j)) = fun _ : Fin 1 => false := by
        funext i
        simp only [Function.comp_apply, singleWireEmb_apply, z, packState_C, hc]
      rw [hz0]
      simp only [Gate.ofMatrix1, act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct,
        Matrix.submatrix_apply, ket, PiLp.single_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single (fun _ : Fin 1 => false)]
      · simp only [↓reduceIte, mul_one]
        have hne : (fun _ : Fin 1 => true) ≠ (fun _ : Fin 1 => false) := fun h => by
          simpa using congrFun h 0
        cases h0 : u 0
        · have huf : u = fun _ => false := funext fun i => by fin_cases i; exact h0
          subst huf
          simp [hadamard, hne.symm]
        · have hut : u = fun _ => true := funext fun i => by fin_cases i; exact h0
          subst hut
          simp [hadamard, hne]
      · intro x _ hx; simp [hx]
      · simp
    · intro b; funext i
      simp only [Function.comp_apply, z', singleWireEmb_apply, packState_C, Function.update_self]
    · intro b i hi
      refine packState_eq_of_C (ps := ps) _ c d q w fc fh fq a i fun k hk => ?_
      by_cases hkj : k = j
      · subst hkj; exact absurd hk (fun h => hi ⟨0, by simp [singleWireEmb_apply, h]⟩)
      · simp [hkj]
  · rw [add_comm]

noncomputable def natToBitsLSBEquiv (r : ℕ) : Fin (2 ^ r) ≃ Qubits r :=
  Equiv.ofBijective (fun c => natToBitsLSB r c.1)
    ((Fintype.bijective_iff_injective_and_card (fun c : Fin (2 ^ r) => natToBitsLSB r c.1)).2
      ⟨fun c₁ c₂ h => Fin.ext (natToBitsLSB_inj_of_lt c₁.isLt c₂.isLt h), by simp⟩)

lemma act_hadamardLayerC :
    act (hadamardLayerC (ps := ps) (r := r) (n := n)).unitary (zeroKet M') =
      (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
        ∑ c : Fin (2 ^ r), ket (coreEmbHom (natToBitsLSB r c.1, false, fun _ => false)) := by
  let extZero : (k : ℕ) → k ≤ r → Qubits k → Qubits r := fun k hk s i =>
    if hi : i.1 < k then s ⟨i.1, hi⟩ else false
  have hpref : ∀ (k : ℕ) (hk : k ≤ r),
      act (Circuit.unitary (List.ofFn fun j : Fin k => hadamardGateAt (ps := ps) (r := r) (n := n)
          (regC (Fin.castLE hk j)))) (zeroKet M') =
        (((Real.sqrt 2)⁻¹ ^ k : ℝ) : ℂ) •
          ∑ s : Qubits k, ket (packState (ps := ps) (extZero k hk s) false (fun _ => false)
            (fun _ => false) false false false (fun _ => false)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hext : ∀ s : Qubits 0, extZero 0 hk s = fun _ => false := fun s => by
        funext i; simp [extZero]
      simp only [Circuit.unitary, List.ofFn_zero, List.map_nil, List.reverse_nil, List.prod_nil,
        act_one_vec, pow_zero, Complex.ofReal_one, one_smul]
      rw [Fintype.sum_unique, hext _, packState_zero]
      rfl
    | succ k ih =>
      intro hk
      have hk_le : k ≤ r := Nat.le_of_lt hk
      have hfn : (List.ofFn fun j : Fin (k + 1) => hadamardGateAt (ps := ps) (r := r) (n := n)
            (regC (Fin.castLE hk j))) =
          (List.ofFn fun j : Fin k => hadamardGateAt (ps := ps) (r := r) (n := n)
            (regC (Fin.castLE hk_le j))) ++
          [hadamardGateAt (ps := ps) (r := r) (n := n) (regC ⟨k, hk⟩)] := by
        rw [List.ofFn_succ', List.concat_eq_append]
        rfl
      have hunit : Circuit.unitary (List.ofFn fun j : Fin (k + 1) => hadamardGateAt (ps := ps) (r := r) (n := n)
            (regC (Fin.castLE hk j))) =
          embedOp (hadamardGateAt (regC ⟨k, hk⟩)).gate.mat (hadamardGateAt (regC ⟨k, hk⟩)).wires *
          Circuit.unitary (List.ofFn fun j : Fin k => hadamardGateAt (ps := ps) (r := r) (n := n)
            (regC (Fin.castLE hk_le j))) := by
        rw [hfn]; simp [Circuit.unitary]
      rw [hunit, act_mul, ih hk_le, act_smul, act_sum]
      have hterm : ∀ s : Qubits k,
          act (embedOp (hadamardGateAt (ps := ps) (r := r) (n := n) (regC ⟨k, hk⟩)).gate.mat
                (hadamardGateAt (regC ⟨k, hk⟩)).wires)
              (ket (packState (ps := ps) (extZero k hk_le s) false (fun _ => false)
                (fun _ => false) false false false (fun _ => false))) =
            (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
              (ket (packState (ps := ps) (extZero (k + 1) hk (Fin.snoc s false)) false (fun _ => false)
                  (fun _ => false) false false false (fun _ => false)) +
               ket (packState (ps := ps) (extZero (k + 1) hk (Fin.snoc s true)) false (fun _ => false)
                  (fun _ => false) false false false (fun _ => false))) := by
        intro s
        have hfalse : extZero k hk_le s ⟨k, hk⟩ = false := by simp [extZero]
        rw [act_hadamardGateAt_false ⟨k, hk⟩ (extZero k hk_le s) hfalse]
        have hup : ∀ b : Bool, Function.update (extZero k hk_le s) ⟨k, hk⟩ b =
            extZero (k + 1) hk (Fin.snoc s b) := by
          intro b; funext i
          by_cases hik : i.1 < k
          · have hne : i ≠ ⟨k, hk⟩ := fun h => by
              have hval : i.1 = k := congrArg Fin.val h
              omega
            have hik1 : i.1 < k + 1 := by omega
            simp only [Function.update_of_ne hne, extZero, hik, ↓reduceDIte, hik1]
            change s ⟨i.1, hik⟩ = Fin.snoc (α := fun _ => Bool) s b (⟨i.1, hik⟩ : Fin k).castSucc
            rw [Fin.snoc_castSucc]
          · by_cases hiek : i.1 = k
            · have heq : i = ⟨k, hk⟩ := Fin.ext hiek
              subst heq
              simp only [Function.update_self, extZero, Nat.lt_succ_self, ↓reduceDIte]
              change b = Fin.snoc (α := fun _ => Bool) s b (Fin.last k)
              rw [Fin.snoc_last]
            · have hne : i ≠ ⟨k, hk⟩ := fun h => hiek (congrArg Fin.val h)
              have hn1 : ¬ i.1 < k + 1 := by omega
              simp [Function.update_of_ne hne, extZero, hik, hn1]
        rw [hup false, hup true]
      simp_rw [hterm, ← Finset.smul_sum, smul_smul]
      have hpow : (((Real.sqrt 2)⁻¹ ^ k : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) =
          (((Real.sqrt 2)⁻¹ ^ (k + 1) : ℝ) : ℂ) := by
        push_cast; rw [pow_succ]
      rw [hpow]
      congr 1
      symm
      rw [Fintype.sum_equiv (qubitsSnocEquiv k) _
        (fun p : Qubits k × Bool => ket (packState (ps := ps) (extZero (k + 1) hk (Fin.snoc p.1 p.2))
          false (fun _ => false) (fun _ => false) false false false (fun _ => false)))
        (fun s => by simp [qubitsSnocEquiv, Fin.snoc_init_self])]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [Finset.sum_add_distrib, add_comm]
  have hfull := hpref r le_rfl
  have hsqrt : ((Real.sqrt 2)⁻¹ ^ r : ℝ) = (Real.sqrt (2 ^ r : ℕ))⁻¹ := by
    rw [inv_pow]
    congr 1
    rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg 2) r), ← pow_mul, mul_comm r 2, pow_mul,
      Real.sq_sqrt (by norm_num)]
    push_cast; rfl
  have hext_full : ∀ s : Qubits r, extZero r le_rfl s = s := fun s => by
    funext i; simp [extZero, i.isLt]
  simp only [hadamardLayerC] at *
  have hcirc : (List.ofFn fun j : Fin r => hadamardGateAt (ps := ps) (r := r) (n := n) (regC j)) =
      (List.ofFn fun j : Fin r => hadamardGateAt (ps := ps) (r := r) (n := n)
        (regC (Fin.castLE le_rfl j))) := rfl
  rw [hcirc, hfull, hsqrt]
  congr 1
  simp_rw [hext_full]
  symm
  exact Fintype.sum_equiv (natToBitsLSBEquiv r) _
    (fun s : Qubits r => ket (packState (ps := ps) s false (fun _ => false)
      (fun _ => false) false false false (fun _ => false)))
    (fun c => rfl)

/-! ### Semantics of the 8 sub-blocks inside `Fin M'` -/

lemma act_eqFQCirc (pat : Qubits (r + 1)) (c : Qubits r) (d : Bool) (q : Qubits n)
    (w : Qubits ℓ) (fc fh fq : Bool) :
    act (embedCircuit (embEqFQ (ps := ps) (r := r) (n := n))
          (ps.eqCirc (r + 1) pat pauliX pauliX_mem_unitaryGroup)).unitary
        (ket (packState (ps := ps) c d q w fc fh fq (fun _ => false))) =
      ket (packState (ps := ps) c d q w fc fh
        (if (fun i : Fin (r + 1) => if h : i.1 < r then c ⟨i.1, h⟩ else d) = pat
         then !fq else fq) (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let addr : Qubits (r + 1) := fun i => if h : i.1 < r then c ⟨i.1, h⟩ else d
  let z := packState (ps := ps) c d q w fc fh fq (fun _ => false)
  let z' := packState (ps := ps) c d q w fc fh (if addr = pat then !fq else fq) (fun _ => false)
  let x' := packEq (r + 1) (ps.ancEq (r + 1)) addr (if addr = pat then !fq else fq) (fun _ => false)
  refine act_embedOp_basis_map (embEqFQ (ps := ps) (r := r) (n := n))
    (ps.eqCirc (r + 1) pat pauliX pauliX_mem_unitaryGroup).unitary z x' ?_ z' ?_ ?_
  · have hcomp : z ∘ embEqFQ (ps := ps) (r := r) (n := n) =
        packEq (r + 1) (ps.ancEq (r + 1)) addr fq (fun _ => false) := by
      funext i
      by_cases h0 : i.1 < r
      · have h0' : i.1 < r + 1 := by omega
        rw [Function.comp_apply, embEqFQ_apply, dif_pos h0]
        dsimp only [z]; rw [packState_C, packEq, dif_pos h0']
        dsimp only [addr]; rw [dif_pos h0]
      · by_cases h1 : i.1 = r
        · have h1' : i.1 < r + 1 := by omega
          rw [Function.comp_apply, embEqFQ_apply, dif_neg h0, dif_pos h1]
          dsimp only [z]; rw [packState_D, packEq, dif_pos h1']
          dsimp only [addr]; rw [dif_neg h0]
        · by_cases h2 : i.1 = r + 1
          · have hn : ¬ i.1 < r + 1 := by omega
            rw [Function.comp_apply, embEqFQ_apply, dif_neg h0, dif_neg h1, dif_pos h2]
            dsimp only [z]; rw [packState_FQ, packEq, dif_neg hn, dif_pos h2]
          · have hn : ¬ i.1 < r + 1 := by omega
            rw [Function.comp_apply, embEqFQ_apply, dif_neg h0, dif_neg h1, dif_neg h2]
            dsimp only [z]; rw [packState_Anc, packEq, dif_neg hn, dif_neg h2]
    rw [hcomp, ps.eq_act]
    by_cases hmatch : addr = pat
    · rw [if_pos hmatch, Fintype.sum_bool]
      cases fq
      · simp [x', hmatch, pauliX, Bool.not_false]
      · simp [x', hmatch, pauliX, Bool.not_true]
    · rw [if_neg hmatch]; simp [x', hmatch]
  · funext i
    by_cases h0 : i.1 < r
    · have h0' : i.1 < r + 1 := by omega
      rw [Function.comp_apply, embEqFQ_apply, dif_pos h0]
      dsimp only [z']; rw [packState_C]
      dsimp only [x']; rw [packEq, dif_pos h0']
      dsimp only [addr]; rw [dif_pos h0]
    · by_cases h1 : i.1 = r
      · have h1' : i.1 < r + 1 := by omega
        rw [Function.comp_apply, embEqFQ_apply, dif_neg h0, dif_pos h1]
        dsimp only [z']; rw [packState_D]
        dsimp only [x']; rw [packEq, dif_pos h1']
        dsimp only [addr]; rw [dif_neg h0]
      · by_cases h2 : i.1 = r + 1
        · have hn : ¬ i.1 < r + 1 := by omega
          rw [Function.comp_apply, embEqFQ_apply, dif_neg h0, dif_neg h1, dif_pos h2]
          dsimp only [z']; rw [packState_FQ]
          dsimp only [x']; rw [packEq, dif_neg hn, dif_pos h2]
        · have hn : ¬ i.1 < r + 1 := by omega
          rw [Function.comp_apply, embEqFQ_apply, dif_neg h0, dif_neg h1, dif_neg h2]
          dsimp only [z']; rw [packState_Anc]
          dsimp only [x']; rw [packEq, dif_neg hn, dif_neg h2]
  · intro i hi
    exact packState_eq_of_FQ (ps := ps) c d q w fc fh _ fq (fun _ => false) i fun h =>
      hi ⟨⟨r + 1, by omega⟩, by simp [embEqFQ_apply, h]⟩

lemma act_eqFCCirc (pat : Qubits r) (c : Qubits r) (d : Bool) (q : Qubits n)
    (w : Qubits ℓ) (fc fh fq : Bool) :
    act (embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
          (ps.eqCirc r pat pauliX pauliX_mem_unitaryGroup)).unitary
        (ket (packState (ps := ps) c d q w fc fh fq (fun _ => false))) =
      ket (packState (ps := ps) c d q w (if c = pat then !fc else fc) fh fq (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let z := packState (ps := ps) c d q w fc fh fq (fun _ => false)
  let z' := packState (ps := ps) c d q w (if c = pat then !fc else fc) fh fq (fun _ => false)
  let x' := packEq r (ps.ancEq r) c (if c = pat then !fc else fc) (fun _ => false)
  refine act_embedOp_basis_map (embEqFC (ps := ps) (r := r) (n := n))
    (ps.eqCirc r pat pauliX pauliX_mem_unitaryGroup).unitary z x' ?_ z' ?_ ?_
  · have hcomp : z ∘ embEqFC (ps := ps) (r := r) (n := n) =
        packEq r (ps.ancEq r) c fc (fun _ => false) := by
      funext i
      by_cases h0 : i.1 < r
      · rw [Function.comp_apply, embEqFC_apply, dif_pos h0]
        dsimp only [z]; rw [packState_C, packEq, dif_pos h0]
      · by_cases h1 : i.1 = r
        · rw [Function.comp_apply, embEqFC_apply, dif_neg h0, dif_pos h1]
          dsimp only [z]; rw [packState_FC, packEq, dif_neg h0, dif_pos h1]
        · rw [Function.comp_apply, embEqFC_apply, dif_neg h0, dif_neg h1]
          dsimp only [z]; rw [packState_Anc, packEq, dif_neg h0, dif_neg h1]
    rw [hcomp, ps.eq_act]
    by_cases hmatch : c = pat
    · rw [if_pos hmatch, Fintype.sum_bool]
      cases fc
      · simp [x', hmatch, pauliX, Bool.not_false]
      · simp [x', hmatch, pauliX, Bool.not_true]
    · rw [if_neg hmatch]; simp [x', hmatch]
  · funext i
    by_cases h0 : i.1 < r
    · rw [Function.comp_apply, embEqFC_apply, dif_pos h0]
      dsimp only [z']; rw [packState_C]
      dsimp only [x']; rw [packEq, dif_pos h0]
    · by_cases h1 : i.1 = r
      · rw [Function.comp_apply, embEqFC_apply, dif_neg h0, dif_pos h1]
        dsimp only [z']; rw [packState_FC]
        dsimp only [x']; rw [packEq, dif_neg h0, dif_pos h1]
      · rw [Function.comp_apply, embEqFC_apply, dif_neg h0, dif_neg h1]
        dsimp only [z']; rw [packState_Anc]
        dsimp only [x']; rw [packEq, dif_neg h0, dif_neg h1]
  · intro i hi
    exact packState_eq_of_FC (ps := ps) c d q w _ fc fh fq (fun _ => false) i fun h =>
      hi ⟨⟨r, by omega⟩, by simp [embEqFC_apply, h]⟩

lemma act_toffoliFHC (c : Qubits r) (d : Bool) (q : Qubits n)
    (w : Qubits ℓ) (fc fh fq : Bool) (a : Qubits Amax) :
    act (embedCircuit (embToffoli (ps := ps) (r := r) (n := n)) ps.toffoliCirc).unitary
        (ket (packState (ps := ps) c d q w fc fh fq a)) =
      ket (packState (ps := ps) c d q w fc (xor fh (fc && d)) fq a) := by
  rw [embedCircuit_unitary]
  let z := packState (ps := ps) c d q w fc fh fq a
  let z' := packState (ps := ps) c d q w fc (xor fh (fc && d)) fq a
  let x' : Qubits 3 := fun i => if i.1 = 0 then fc else if i.1 = 1 then d else xor fh (fc && d)
  refine act_embedOp_basis_map (embToffoli (ps := ps) (r := r) (n := n))
    ps.toffoliCirc.unitary z x' ?_ z' ?_ ?_
  · have hcomp : z ∘ embToffoli (ps := ps) (r := r) (n := n) =
        fun i : Fin 3 => if i.1 = 0 then fc else if i.1 = 1 then d else fh := by
      funext i; fin_cases i
      · simp [z, embToffoli_apply, packState_FC]
      · simp [z, embToffoli_apply, packState_D]
      · simp [z, embToffoli_apply, packState_FH]
    rw [hcomp]
    exact ps.toffoli_act fc d fh
  · funext i; fin_cases i
    · simp [z', x', embToffoli_apply, packState_FC]
    · simp [z', x', embToffoli_apply, packState_D]
    · simp [z', x', embToffoli_apply, packState_FH]
  · intro i hi
    exact packState_eq_of_FH (ps := ps) c d q w fc _ fh fq a i fun h =>
      hi ⟨2, by simp [embToffoli_apply, h]⟩

lemma act_chQCirc (hn : 1 ≤ n) (c : Qubits r) (d : Bool) (q : Qubits n)
    (w : Qubits ℓ) (fc fh fq : Bool) :
    act (embedCircuit (embCH (ps := ps) (r := r) (n := n) hn) (ps.chCirc n)).unitary
        (ket (packState (ps := ps) c d q w fc fh fq (fun _ => false))) =
      if fh then
        ∑ q' : Qubits n, (hadamardN n q' q) •
          ket (packState (ps := ps) c d q' w fc true fq (fun _ => false))
      else
        ket (packState (ps := ps) c d q w fc false fq (fun _ => false)) := by
  rw [embedCircuit_unitary]
  cases hfh : fh
  · simp only [Bool.false_eq_true, ↓reduceIte]
    let z := packState (ps := ps) c d q w fc false fq (fun _ => false)
    let z' := packState (ps := ps) c d q w fc false fq (fun _ => false)
    let x' := packCH n (ps.ancCH n) false q (fun _ => false)
    refine act_embedOp_basis_map (embCH (ps := ps) (r := r) (n := n) hn)
      (ps.chCirc n).unitary z x' ?_ z' ?_ (fun _ _ => rfl)
    · have hcomp : z ∘ embCH (ps := ps) (r := r) (n := n) hn =
          packCH n (ps.ancCH n) false q (fun _ => false) := by
        funext i
        by_cases h0 : i.1 = 0
        · rw [Function.comp_apply, embCH_apply, dif_pos h0]; dsimp only [z]
          rw [packState_FH, packCH, dif_pos h0]
        · by_cases h1 : i.1 < 1 + n
          · rw [Function.comp_apply, embCH_apply, dif_neg h0, dif_pos h1]; dsimp only [z]
            rw [packState_Q, packCH, dif_neg h0, dif_pos h1]
          · rw [Function.comp_apply, embCH_apply, dif_neg h0, dif_neg h1]; dsimp only [z]
            rw [packState_Anc, packCH, dif_neg h0, dif_neg h1]
      rw [hcomp, ps.ch_act]; simp [x']
    · funext i
      by_cases h0 : i.1 = 0
      · rw [Function.comp_apply, embCH_apply, dif_pos h0]; dsimp only [z', x']
        rw [packState_FH, packCH, dif_pos h0]
      · by_cases h1 : i.1 < 1 + n
        · rw [Function.comp_apply, embCH_apply, dif_neg h0, dif_pos h1]; dsimp only [z', x']
          rw [packState_Q, packCH, dif_neg h0, dif_pos h1]
        · rw [Function.comp_apply, embCH_apply, dif_neg h0, dif_neg h1]; dsimp only [z', x']
          rw [packState_Anc, packCH, dif_neg h0, dif_neg h1]
  · simp only [↓reduceIte]
    let z := packState (ps := ps) c d q w fc true fq (fun _ => false)
    let z' : Qubits n → Qubits M' := fun q' =>
      packState (ps := ps) c d q' w fc true fq (fun _ => false)
    refine act_embedOp_basis_sum (embCH (ps := ps) (r := r) (n := n) hn)
      (ps.chCirc n).unitary z (fun q' => hadamardN n q' q)
      (fun q' => packCH n (ps.ancCH n) true q' (fun _ => false)) z' ?_ ?_ ?_
    · have hcomp : z ∘ embCH (ps := ps) (r := r) (n := n) hn =
          packCH n (ps.ancCH n) true q (fun _ => false) := by
        funext i
        by_cases h0 : i.1 = 0
        · rw [Function.comp_apply, embCH_apply, dif_pos h0]; dsimp only [z]
          rw [packState_FH, packCH, dif_pos h0]
        · by_cases h1 : i.1 < 1 + n
          · rw [Function.comp_apply, embCH_apply, dif_neg h0, dif_pos h1]; dsimp only [z]
            rw [packState_Q, packCH, dif_neg h0, dif_pos h1]
          · rw [Function.comp_apply, embCH_apply, dif_neg h0, dif_neg h1]; dsimp only [z]
            rw [packState_Anc, packCH, dif_neg h0, dif_neg h1]
      rw [hcomp, ps.ch_act]; simp
    · intro q'; funext i
      by_cases h0 : i.1 = 0
      · rw [Function.comp_apply, embCH_apply, dif_pos h0]; dsimp only [z']
        rw [packState_FH, packCH, dif_pos h0]
      · by_cases h1 : i.1 < 1 + n
        · rw [Function.comp_apply, embCH_apply, dif_neg h0, dif_pos h1]; dsimp only [z']
          rw [packState_Q, packCH, dif_neg h0, dif_pos h1]
        · rw [Function.comp_apply, embCH_apply, dif_neg h0, dif_neg h1]; dsimp only [z']
          rw [packState_Anc, packCH, dif_neg h0, dif_neg h1]
    · intro q' i hi
      exact packState_eq_of_Q (ps := ps) c d q' q w fc true fq (fun _ => false) i fun j hj =>
        hi ⟨⟨1 + j.1, by omega⟩, by simp [embCH_apply, hj]⟩

lemma act_hcQCirc (c : Qubits r) (d : Bool) (q : Qubits n)
    (fc fh fq : Bool) :
    act (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcCirc n)).unitary
        (ket (packState (ps := ps) c d q (fun _ => false) fc fh fq (fun _ => false))) =
      ket (packState (ps := ps) c d q (natToBitsLSB ℓ (hammingWeight q)) fc fh fq (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let z := packState (ps := ps) c d q (fun _ => false) fc fh fq (fun _ => false)
  let z' := packState (ps := ps) c d q (natToBitsLSB ℓ (hammingWeight q)) fc fh fq (fun _ => false)
  let x' := packHC n ℓ (ps.ancHC n) q (natToBitsLSB ℓ (hammingWeight q)) (fun _ => false)
  refine act_embedOp_basis_map (embHC (ps := ps) (r := r) (n := n))
    (ps.hcCirc n).unitary z x' ?_ z' ?_ ?_
  · have hcomp : z ∘ embHC (ps := ps) (r := r) (n := n) =
        packHC n ℓ (ps.ancHC n) q (fun _ => false) (fun _ => false) := by
      funext i
      simp only [Function.comp_apply, embHC_apply, packHC, z]
      split_ifs with h0 h1
      · simp only [packState_Q]
      · simp only [packState_W]
      · simp only [packState_Anc]
    rw [hcomp, ps.hc_act]
  · funext i
    simp only [Function.comp_apply, embHC_apply, packHC, z', x']
    split_ifs with h0 h1
    · simp only [packState_Q]
    · simp only [packState_W]
    · simp only [packState_Anc]
  · intro i hi
    exact packState_eq_of_W (ps := ps) c d q _ (fun _ => false) fc fh fq (fun _ => false) i fun j hj =>
      hi ⟨⟨n + j.1, by omega⟩, by simp [embHC_apply, hj]⟩

lemma act_hcQAdjCirc (c : Qubits r) (d : Bool) (q : Qubits n)
    (fc fh fq : Bool) :
    act (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcAdjCirc n)).unitary
        (ket (packState (ps := ps) c d q (natToBitsLSB ℓ (hammingWeight q)) fc fh fq (fun _ => false))) =
      ket (packState (ps := ps) c d q (fun _ => false) fc fh fq (fun _ => false)) := by
  have hunit : (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcAdjCirc n)).unitary =
      star (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcCirc n)).unitary := by
    rw [embedCircuit_unitary, embedCircuit_unitary, ps.hcAdj_unitary]
    ext y z
    simp only [embedOp, Matrix.of_apply, Matrix.star_apply]
    by_cases h : ∀ a, a ∉ Set.range (embHC (ps := ps) (r := r) (n := n)) → y a = z a
    · have h' : ∀ a, a ∉ Set.range (embHC (ps := ps) (r := r) (n := n)) → z a = y a :=
        fun a ha => (h a ha).symm
      rw [if_pos h, if_pos h']
    · have h' : ¬ ∀ a, a ∉ Set.range (embHC (ps := ps) (r := r) (n := n)) → z a = y a :=
        fun h' => h fun a ha => (h' a ha).symm
      rw [if_neg h, if_neg h']; simp
  have hmem : (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcCirc n)).unitary ∈
      Matrix.unitaryGroup (Qubits M') ℂ :=
    circuit_unitary_mem_unitaryGroup _
  have hmul : star (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcCirc n)).unitary *
      (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcCirc n)).unitary = 1 :=
    (Matrix.mem_unitaryGroup_iff'.mp hmem)
  rw [← act_hcQCirc (ps := ps) c d q fc fh fq, ← act_mul, hunit, hmul, act_one_vec]

lemma act_eqWFullCirc (pat : Qubits (1 + ℓ)) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ) (fc fh fq : Bool) :
    act (embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
          (ps.eqCirc (1 + ℓ) pat U hU)).unitary
        (ket (packState (ps := ps) c d q w fc fh fq (fun _ => false))) =
      if (fun i : Fin (1 + ℓ) => if h : i.1 = 0 then fc else w ⟨i.1 - 1, by omega⟩) = pat then
        ∑ d' : Bool, (U d' d) • ket (packState (ps := ps) c d' q w fc fh fq (fun _ => false))
      else
        ket (packState (ps := ps) c d q w fc fh fq (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let addr : Qubits (1 + ℓ) := fun i => if h : i.1 = 0 then fc else w ⟨i.1 - 1, by omega⟩
  let z := packState (ps := ps) c d q w fc fh fq (fun _ => false)
  have hcomp : z ∘ embEqWFull (ps := ps) (r := r) (n := n) =
      packEq (1 + ℓ) (ps.ancEq (1 + ℓ)) addr d (fun _ => false) := by
    funext i
    by_cases h0 : i.1 = 0
    · have h0' : i.1 < 1 + ℓ := by omega
      rw [Function.comp_apply, embEqWFull_apply, dif_pos h0]
      dsimp only [z]; rw [packState_FC, packEq, dif_pos h0']
      dsimp only [addr]; rw [dif_pos h0]
    · by_cases h1 : i.1 < 1 + ℓ
      · rw [Function.comp_apply, embEqWFull_apply, dif_neg h0, dif_pos h1]
        dsimp only [z]; rw [packState_W, packEq, dif_pos h1]
        dsimp only [addr]; rw [dif_neg h0]
      · by_cases h2 : i.1 = 1 + ℓ
        · rw [Function.comp_apply, embEqWFull_apply, dif_neg h0, dif_neg h1, dif_pos h2]
          dsimp only [z]; rw [packState_D, packEq, dif_neg h1, dif_pos h2]
        · rw [Function.comp_apply, embEqWFull_apply, dif_neg h0, dif_neg h1, dif_neg h2]
          dsimp only [z]; rw [packState_Anc, packEq, dif_neg h1, dif_neg h2]
  by_cases hmatch : addr = pat
  · rw [if_pos hmatch]
    let z' : Bool → Qubits M' := fun d' => packState (ps := ps) c d' q w fc fh fq (fun _ => false)
    refine act_embedOp_basis_sum (embEqWFull (ps := ps) (r := r) (n := n))
      (ps.eqCirc (1 + ℓ) pat U hU).unitary z (fun d' => U d' d)
      (fun d' => packEq (1 + ℓ) (ps.ancEq (1 + ℓ)) addr d' (fun _ => false)) z' ?_ ?_ ?_
    · rw [hcomp, ps.eq_act, if_pos hmatch]
    · intro d'; funext i
      by_cases h0 : i.1 = 0
      · have h0' : i.1 < 1 + ℓ := by omega
        rw [Function.comp_apply, embEqWFull_apply, dif_pos h0]
        dsimp only [z']; rw [packState_FC, packEq, dif_pos h0']
        dsimp only [addr]; rw [dif_pos h0]
      · by_cases h1 : i.1 < 1 + ℓ
        · rw [Function.comp_apply, embEqWFull_apply, dif_neg h0, dif_pos h1]
          dsimp only [z']; rw [packState_W, packEq, dif_pos h1]
          dsimp only [addr]; rw [dif_neg h0]
        · by_cases h2 : i.1 = 1 + ℓ
          · rw [Function.comp_apply, embEqWFull_apply, dif_neg h0, dif_neg h1, dif_pos h2]
            dsimp only [z']; rw [packState_D, packEq, dif_neg h1, dif_pos h2]
          · rw [Function.comp_apply, embEqWFull_apply, dif_neg h0, dif_neg h1, dif_neg h2]
            dsimp only [z']; rw [packState_Anc, packEq, dif_neg h1, dif_neg h2]
    · intro d' i hi
      exact packState_eq_of_D (ps := ps) c _ d q w fc fh fq (fun _ => false) i fun h =>
        hi ⟨⟨1 + ℓ, by omega⟩, by simp [embEqWFull_apply, h]⟩
  · rw [if_neg hmatch]
    let x' := packEq (1 + ℓ) (ps.ancEq (1 + ℓ)) addr d (fun _ => false)
    refine act_embedOp_basis_map (embEqWFull (ps := ps) (r := r) (n := n))
      (ps.eqCirc (1 + ℓ) pat U hU).unitary z x' ?_ z ?_ ?_
    · rw [hcomp, ps.eq_act, if_neg hmatch]
    · exact hcomp
    · intro i _; rfl

lemma act_eqWBit1Circ (hℓ : 2 ≤ ℓ) (pat : Qubits 2) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (c : Qubits r) (d : Bool) (q : Qubits n) (w : Qubits ℓ) (fc fh fq : Bool) :
    act (embedCircuit (embEqWBit1 (ps := ps) (r := r) (n := n) hℓ)
          (ps.eqCirc 2 pat U hU)).unitary
        (ket (packState (ps := ps) c d q w fc fh fq (fun _ => false))) =
      if (fun i : Fin 2 => if i.1 = 0 then fc else w ⟨1, by omega⟩) = pat then
        ∑ d' : Bool, (U d' d) • ket (packState (ps := ps) c d' q w fc fh fq (fun _ => false))
      else
        ket (packState (ps := ps) c d q w fc fh fq (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let addr : Qubits 2 := fun i => if i.1 = 0 then fc else w ⟨1, by omega⟩
  let z := packState (ps := ps) c d q w fc fh fq (fun _ => false)
  have hcomp : z ∘ embEqWBit1 (ps := ps) (r := r) (n := n) hℓ =
      packEq 2 (ps.ancEq 2) addr d (fun _ => false) := by
    funext i
    by_cases h0 : i.1 = 0
    · have h0' : i.1 < 2 := by omega
      rw [Function.comp_apply, embEqWBit1_apply, dif_pos h0]
      dsimp only [z]; rw [packState_FC, packEq, dif_pos h0']
      dsimp only [addr]; rw [if_pos h0]
    · by_cases h1 : i.1 = 1
      · have h1' : i.1 < 2 := by omega
        rw [Function.comp_apply, embEqWBit1_apply, dif_neg h0, dif_pos h1]
        dsimp only [z]; rw [packState_W, packEq, dif_pos h1']
        dsimp only [addr]; rw [if_neg h0]
      · by_cases h2 : i.1 = 2
        · have hn : ¬ i.1 < 2 := by omega
          rw [Function.comp_apply, embEqWBit1_apply, dif_neg h0, dif_neg h1, dif_pos h2]
          dsimp only [z]; rw [packState_D, packEq, dif_neg hn, dif_pos h2]
        · have hn : ¬ i.1 < 2 := by omega
          rw [Function.comp_apply, embEqWBit1_apply, dif_neg h0, dif_neg h1, dif_neg h2]
          dsimp only [z]; rw [packState_Anc, packEq, dif_neg hn, dif_neg h2]
  by_cases hmatch : addr = pat
  · rw [if_pos hmatch]
    let z' : Bool → Qubits M' := fun d' => packState (ps := ps) c d' q w fc fh fq (fun _ => false)
    refine act_embedOp_basis_sum (embEqWBit1 (ps := ps) (r := r) (n := n) hℓ)
      (ps.eqCirc 2 pat U hU).unitary z (fun d' => U d' d)
      (fun d' => packEq 2 (ps.ancEq 2) addr d' (fun _ => false)) z' ?_ ?_ ?_
    · rw [hcomp, ps.eq_act, if_pos hmatch]
    · intro d'; funext i
      by_cases h0 : i.1 = 0
      · have h0' : i.1 < 2 := by omega
        rw [Function.comp_apply, embEqWBit1_apply, dif_pos h0]
        dsimp only [z']; rw [packState_FC, packEq, dif_pos h0']
        dsimp only [addr]; rw [if_pos h0]
      · by_cases h1 : i.1 = 1
        · have h1' : i.1 < 2 := by omega
          rw [Function.comp_apply, embEqWBit1_apply, dif_neg h0, dif_pos h1]
          dsimp only [z']; rw [packState_W, packEq, dif_pos h1']
          dsimp only [addr]; rw [if_neg h0]
        · by_cases h2 : i.1 = 2
          · have hn : ¬ i.1 < 2 := by omega
            rw [Function.comp_apply, embEqWBit1_apply, dif_neg h0, dif_neg h1, dif_pos h2]
            dsimp only [z']; rw [packState_D, packEq, dif_neg hn, dif_pos h2]
          · have hn : ¬ i.1 < 2 := by omega
            rw [Function.comp_apply, embEqWBit1_apply, dif_neg h0, dif_neg h1, dif_neg h2]
            dsimp only [z']; rw [packState_Anc, packEq, dif_neg hn, dif_neg h2]
    · intro d' i hi
      exact packState_eq_of_D (ps := ps) c _ d q w fc fh fq (fun _ => false) i fun h =>
        hi ⟨⟨2, by omega⟩, by simp [embEqWBit1_apply, h]⟩
  · rw [if_neg hmatch]
    let x' := packEq 2 (ps.ancEq 2) addr d (fun _ => false)
    refine act_embedOp_basis_map (embEqWBit1 (ps := ps) (r := r) (n := n) hℓ)
      (ps.eqCirc 2 pat U hU).unitary z x' ?_ z ?_ ?_
    · rw [hcomp, ps.eq_act, if_neg hmatch]
    · exact hcomp
    · intro i _; rfl

end SubCircuitEmbeddings

section StepAndWalk

variable {ps : PrimitiveSuite} {r n : ℕ}

local notation "ℓ" => Nat.clog 2 (n + 1)
local notation "Amax" => ancMax ps r n
local notation "M'" => regM' ps r n

private lemma circuit_unitary_append {S : Set Gate} {m : ℕ} (c₁ c₂ : Circuit S m) :
    (c₁ ++ c₂).unitary = c₂.unitary * c₁.unitary := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

private lemma circuit_unitary_mem_unitaryGroup_general {m : ℕ} (c : Circuit gates12 m) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits m) ℂ :=
  circuit_unitary_mem_unitaryGroup c

private lemma hammingWeight_le (q : Qubits n) : hammingWeight q ≤ n := by
  simpa [hammingWeight] using Finset.card_le_univ (Finset.univ.filter fun i => q i = true)

private lemma nat_lt_two_pow_clog (n : ℕ) : n < 2 ^ Nat.clog 2 (n + 1) := by
  have h : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (b := 2) (by norm_num) (n + 1)
  omega

def patW0 (n : ℕ) : Qubits (1 + Nat.clog 2 (n + 1)) :=
  fun i => if i.1 = 0 then true else false

def patW1 : Qubits 2 := fun _ => true

def patWk (n k : ℕ) : Qubits (1 + Nat.clog 2 (n + 1)) :=
  fun i => if h : i.1 = 0 then true else natToBitsLSB (Nat.clog 2 (n + 1)) k ⟨i.1 - 1, by omega⟩

noncomputable def U_k_adj_Z (m : ℕ) : Matrix Bool Bool ℂ :=
  U_k_mat m * (if (2 * m + 1).testBit 1 then pauliZ else 1)

lemma U_k_adj_Z_mem_unitaryGroup (m : ℕ) : U_k_adj_Z m ∈ Matrix.unitaryGroup Bool ℂ :=
  Submonoid.mul_mem _ (U_k_mat_mem_unitaryGroup m) (by
    split_ifs
    · exact pauliZ_mem_unitaryGroup
    · exact Submonoid.one_mem _)

noncomputable def uTildeCirc (m : ℕ) (hℓ : 2 ≤ ℓ) : Circuit gates12 M' :=
  embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
    (ps.eqCirc (1 + ℓ) (patW0 n) pauliX pauliX_mem_unitaryGroup) ++
  embedCircuit (embEqWBit1 (ps := ps) (r := r) (n := n) hℓ)
    (ps.eqCirc 2 patW1 pauliZ pauliZ_mem_unitaryGroup) ++
  embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
    (ps.eqCirc (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m))

lemma uTildeCirc_length (m : ℕ) (hℓ : 2 ≤ ℓ) :
    (uTildeCirc (ps := ps) (r := r) (n := n) m hℓ).length =
      (ps.eqCirc (1 + ℓ) (patW0 n) pauliX pauliX_mem_unitaryGroup).length +
      (ps.eqCirc 2 patW1 pauliZ pauliZ_mem_unitaryGroup).length +
      (ps.eqCirc (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m)).length := by
  simp [uTildeCirc, List.length_append, embedCircuit]; ring

lemma act_uTildeCirc {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n) (hℓ : 2 ≤ ℓ)
    (c : Qubits r) (d : Bool) (q : Qubits n) (fc : Bool) :
    act (uTildeCirc (ps := ps) (r := r) (n := n) m hℓ).unitary
        (ket (packState (ps := ps) c d q (natToBitsLSB ℓ (hammingWeight q)) fc false false (fun _ => false))) =
      if fc then
        ∑ d' : Bool, (U_op m (hammingWeight q) d' d) •
          ket (packState (ps := ps) c d' q (natToBitsLSB ℓ (hammingWeight q)) true false false (fun _ => false))
      else
        ket (packState (ps := ps) c d q (natToBitsLSB ℓ (hammingWeight q)) false false false (fun _ => false)) := by
  let wq := natToBitsLSB ℓ (hammingWeight q)
  have hlt_q : hammingWeight q < 2 ^ ℓ := lt_of_le_of_lt (hammingWeight_le q) (nat_lt_two_pow_clog n)
  have hlt_k : 2 * m + 1 < 2 ^ ℓ := lt_of_le_of_lt hle (nat_lt_two_pow_clog n)
  have hlt_0 : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  have haddr0 : (fun i : Fin (1 + ℓ) => if h : i.1 = 0 then fc else wq ⟨i.1 - 1, by omega⟩) = patW0 n ↔
      (fc = true ∧ hammingWeight q = 0) := by
    constructor
    · intro h
      have hfc := congrFun h ⟨0, by omega⟩
      simp only [patW0, ↓reduceDIte, ↓reduceIte] at hfc
      refine ⟨hfc, ?_⟩
      apply natToBitsLSB_inj_of_lt hlt_q hlt_0
      funext j
      have hj := congrFun h ⟨1 + j.1, by omega⟩
      simpa [patW0, natToBitsLSB_zero] using hj
    · rintro ⟨hfc, hq0⟩
      funext i
      by_cases hi : i.1 = 0
      · simp [hi, patW0, hfc]
      · simp [hi, patW0, wq, hq0, natToBitsLSB_zero]
  have haddr1 : (fun i : Fin 2 => if i.1 = 0 then fc else wq ⟨1, by omega⟩) = patW1 ↔
      (fc = true ∧ (hammingWeight q).testBit 1 = true) := by
    constructor
    · intro h
      have hfc := congrFun h ⟨0, by omega⟩
      have hbit := congrFun h ⟨1, by omega⟩
      simp only [patW1] at hfc hbit
      exact ⟨hfc, by simpa [wq, natToBitsLSB] using hbit⟩
    · rintro ⟨hfc, hbit⟩
      funext i; fin_cases i
      · simp [patW1, hfc]
      · simp [patW1, wq, natToBitsLSB, hbit]
  have haddrk : (fun i : Fin (1 + ℓ) => if h : i.1 = 0 then fc else wq ⟨i.1 - 1, by omega⟩) =
      patWk n (2 * m + 1) ↔ (fc = true ∧ hammingWeight q = 2 * m + 1) := by
    constructor
    · intro h
      have hfc := congrFun h ⟨0, by omega⟩
      simp only [patWk, ↓reduceDIte] at hfc
      refine ⟨hfc, ?_⟩
      apply natToBitsLSB_inj_of_lt hlt_q hlt_k
      funext j
      have hj := congrFun h ⟨1 + j.1, by omega⟩
      simpa [patWk] using hj
    · rintro ⟨hfc, hqk⟩
      funext i
      by_cases hi : i.1 = 0
      · simp [hi, patWk, hfc]
      · simp [hi, patWk, wq, hqk]
  simp only [uTildeCirc, circuit_unitary_append, act_mul]
  cases fc
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hf0 : ¬ ((fun i : Fin (1 + ℓ) => if h : i.1 = 0 then false else wq ⟨i.1 - 1, by omega⟩) = patW0 n) := by
      rw [haddr0]; simp
    have hf1 : ¬ ((fun i : Fin 2 => if i.1 = 0 then false else wq ⟨1, by omega⟩) = patW1) := by
      rw [haddr1]; simp
    have hfk : ¬ ((fun i : Fin (1 + ℓ) => if h : i.1 = 0 then false else wq ⟨i.1 - 1, by omega⟩) = patWk n (2 * m + 1)) := by
      rw [haddrk]; simp
    rw [act_eqWFullCirc, if_neg hf0, act_eqWBit1Circ, if_neg hf1, act_eqWFullCirc, if_neg hfk]
  · simp only [↓reduceIte]
    have hstep1 :
        act (embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
              (ps.eqCirc (1 + ℓ) (patW0 n) pauliX pauliX_mem_unitaryGroup)).unitary
            (ket (packState (ps := ps) c d q wq true false false (fun _ => false))) =
          ∑ d₁ : Bool, ((if hammingWeight q = 0 then pauliX else 1) d₁ d) •
            ket (packState (ps := ps) c d₁ q wq true false false (fun _ => false)) := by
      rw [act_eqWFullCirc]
      by_cases hq0 : hammingWeight q = 0
      · have hm0 : (fun i : Fin (1 + ℓ) => if h : i.1 = 0 then true else wq ⟨i.1 - 1, by omega⟩) = patW0 n :=
          haddr0.mpr ⟨rfl, hq0⟩
        rw [if_pos hm0, if_pos hq0]
      · have hm0 : (fun i : Fin (1 + ℓ) => if h : i.1 = 0 then true else wq ⟨i.1 - 1, by omega⟩) ≠ patW0 n :=
          fun h => hq0 (haddr0.mp h).2
        rw [if_neg hm0, if_neg hq0, Fintype.sum_bool]
        cases d <;> simp
    have hstep2 : ∀ d₁ : Bool,
        act (embedCircuit (embEqWBit1 (ps := ps) (r := r) (n := n) hℓ)
              (ps.eqCirc 2 patW1 pauliZ pauliZ_mem_unitaryGroup)).unitary
            (ket (packState (ps := ps) c d₁ q wq true false false (fun _ => false))) =
          ∑ d₂ : Bool, ((if (hammingWeight q).testBit 1 then pauliZ else 1) d₂ d₁) •
            ket (packState (ps := ps) c d₂ q wq true false false (fun _ => false)) := by
      intro d₁
      rw [act_eqWBit1Circ]
      by_cases hb : (hammingWeight q).testBit 1 = true
      · have hm1 : (fun i : Fin 2 => if i.1 = 0 then true else wq ⟨1, by omega⟩) = patW1 :=
          haddr1.mpr ⟨rfl, hb⟩
        rw [if_pos hm1, if_pos hb]
      · have hm1 : (fun i : Fin 2 => if i.1 = 0 then true else wq ⟨1, by omega⟩) ≠ patW1 :=
          fun h => hb (haddr1.mp h).2
        rw [if_neg hm1, if_neg hb, Fintype.sum_bool]
        cases d₁ <;> simp
    have hstep3 : ∀ d₂ : Bool,
        act (embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
              (ps.eqCirc (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m))).unitary
            (ket (packState (ps := ps) c d₂ q wq true false false (fun _ => false))) =
          ∑ d' : Bool, ((if hammingWeight q = 2 * m + 1 then U_k_adj_Z m else 1) d' d₂) •
            ket (packState (ps := ps) c d' q wq true false false (fun _ => false)) := by
      intro d₂
      rw [act_eqWFullCirc]
      by_cases hqk : hammingWeight q = 2 * m + 1
      · have hmk : (fun i : Fin (1 + ℓ) => if h : i.1 = 0 then true else wq ⟨i.1 - 1, by omega⟩) =
            patWk n (2 * m + 1) := haddrk.mpr ⟨rfl, hqk⟩
        rw [if_pos hmk, if_pos hqk]
      · have hmk : (fun i : Fin (1 + ℓ) => if h : i.1 = 0 then true else wq ⟨i.1 - 1, by omega⟩) ≠
            patWk n (2 * m + 1) := fun h => hqk (haddrk.mp h).2
        rw [if_neg hmk, if_neg hqk, Fintype.sum_bool]
        cases d₂ <;> simp
    rw [hstep1, act_sum, act_sum]
    have h12 : ∀ d₁ : Bool,
        act (embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
              (ps.eqCirc (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m))).unitary
          (act (embedCircuit (embEqWBit1 (ps := ps) (r := r) (n := n) hℓ)
                (ps.eqCirc 2 patW1 pauliZ pauliZ_mem_unitaryGroup)).unitary
            (((if hammingWeight q = 0 then pauliX else 1) d₁ d) •
              ket (packState (ps := ps) c d₁ q wq true false false (fun _ => false)))) =
        ∑ d' : Bool, ∑ d₂ : Bool,
          ((if hammingWeight q = 0 then pauliX else 1) d₁ d *
            (if (hammingWeight q).testBit 1 then pauliZ else 1) d₂ d₁ *
            (if hammingWeight q = 2 * m + 1 then U_k_adj_Z m else 1) d' d₂) •
            ket (packState (ps := ps) c d' q wq true false false (fun _ => false)) := by
      intro d₁
      rw [act_smul, hstep2, act_smul, act_sum, Finset.smul_sum]
      have h23 : ∀ d₂ : Bool,
          ((if hammingWeight q = 0 then pauliX else 1) d₁ d) •
            act (embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
                  (ps.eqCirc (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m))).unitary
              (((if (hammingWeight q).testBit 1 then pauliZ else 1) d₂ d₁) •
                ket (packState (ps := ps) c d₂ q wq true false false (fun _ => false))) =
          ∑ d' : Bool,
            ((if hammingWeight q = 0 then pauliX else 1) d₁ d *
              (if (hammingWeight q).testBit 1 then pauliZ else 1) d₂ d₁ *
              (if hammingWeight q = 2 * m + 1 then U_k_adj_Z m else 1) d' d₂) •
              ket (packState (ps := ps) c d' q wq true false false (fun _ => false)) := by
        intro d₂
        rw [act_smul, hstep3, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun d' _ => ?_
        rw [smul_smul, smul_smul, mul_assoc]
      have h23_sum : (∑ d₂ : Bool,
          ((if hammingWeight q = 0 then pauliX else 1) d₁ d) •
            act (embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
                  (ps.eqCirc (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m))).unitary
              (((if (hammingWeight q).testBit 1 then pauliZ else 1) d₂ d₁) •
                ket (packState (ps := ps) c d₂ q wq true false false (fun _ => false)))) =
          ∑ d₂ : Bool, ∑ d' : Bool,
            ((if hammingWeight q = 0 then pauliX else 1) d₁ d *
              (if (hammingWeight q).testBit 1 then pauliZ else 1) d₂ d₁ *
              (if hammingWeight q = 2 * m + 1 then U_k_adj_Z m else 1) d' d₂) •
              ket (packState (ps := ps) c d' q wq true false false (fun _ => false)) :=
        Finset.sum_congr rfl fun d₂ _ => h23 d₂
      rw [h23_sum]
      exact Finset.sum_comm
    have h12_sum : (∑ d₁ : Bool,
        act (embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
              (ps.eqCirc (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m))).unitary
          (act (embedCircuit (embEqWBit1 (ps := ps) (r := r) (n := n) hℓ)
                (ps.eqCirc 2 patW1 pauliZ pauliZ_mem_unitaryGroup)).unitary
            (((if hammingWeight q = 0 then pauliX else 1) d₁ d) •
              ket (packState (ps := ps) c d₁ q wq true false false (fun _ => false))))) =
        ∑ d₁ : Bool, ∑ d' : Bool, ∑ d₂ : Bool,
          ((if hammingWeight q = 0 then pauliX else 1) d₁ d *
            (if (hammingWeight q).testBit 1 then pauliZ else 1) d₂ d₁ *
            (if hammingWeight q = 2 * m + 1 then U_k_adj_Z m else 1) d' d₂) •
            ket (packState (ps := ps) c d' q wq true false false (fun _ => false)) :=
      Finset.sum_congr rfl fun d₁ _ => h12 d₁
    rw [h12_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d' _ => ?_
    have hsm1 : ∀ d₁ : Bool,
        (∑ d₂ : Bool,
          ((if hammingWeight q = 0 then pauliX else 1) d₁ d *
            (if (hammingWeight q).testBit 1 then pauliZ else 1) d₂ d₁ *
            (if hammingWeight q = 2 * m + 1 then U_k_adj_Z m else 1) d' d₂) •
            ket (packState (ps := ps) c d' q wq true false false (fun _ => false))) =
        (∑ d₂ : Bool,
          ((if hammingWeight q = 0 then pauliX else 1) d₁ d *
            (if (hammingWeight q).testBit 1 then pauliZ else 1) d₂ d₁ *
            (if hammingWeight q = 2 * m + 1 then U_k_adj_Z m else 1) d' d₂)) •
          ket (packState (ps := ps) c d' q wq true false false (fun _ => false)) :=
      fun d₁ => (Finset.sum_smul).symm
    have hsm1_sum : (∑ d₁ : Bool, ∑ d₂ : Bool,
          ((if hammingWeight q = 0 then pauliX else 1) d₁ d *
            (if (hammingWeight q).testBit 1 then pauliZ else 1) d₂ d₁ *
            (if hammingWeight q = 2 * m + 1 then U_k_adj_Z m else 1) d' d₂) •
            ket (packState (ps := ps) c d' q wq true false false (fun _ => false))) =
        ∑ d₁ : Bool, (∑ d₂ : Bool,
          ((if hammingWeight q = 0 then pauliX else 1) d₁ d *
            (if (hammingWeight q).testBit 1 then pauliZ else 1) d₂ d₁ *
            (if hammingWeight q = 2 * m + 1 then U_k_adj_Z m else 1) d' d₂)) •
          ket (packState (ps := ps) c d' q wq true false false (fun _ => false)) :=
      Finset.sum_congr rfl fun d₁ _ => hsm1 d₁
    rw [hsm1_sum, ← Finset.sum_smul]
    congr 1
    rw [U_op_eq_three_gates m (hammingWeight q) hm]
    simp only [U_k_adj_Z, Matrix.mul_apply]
    simp_rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₂ _ => by ring

noncomputable def hHatCirc (hn : 1 ≤ n) : Circuit gates12 M' :=
  embedCircuit (embToffoli (ps := ps) (r := r) (n := n)) ps.toffoliCirc ++
  embedCircuit (embCH (ps := ps) (r := r) (n := n) hn) (ps.chCirc n) ++
  embedCircuit (embToffoli (ps := ps) (r := r) (n := n)) ps.toffoliCirc

lemma hHatCirc_length (hn : 1 ≤ n) :
    (hHatCirc (ps := ps) (r := r) (n := n) hn).length =
      2 * ps.toffoliCirc.length + (ps.chCirc n).length := by
  simp [hHatCirc, List.length_append, embedCircuit]; ring

lemma act_hHatCirc (hn : 1 ≤ n) (c : Qubits r) (d : Bool) (q : Qubits n) (fc : Bool) :
    act (hHatCirc (ps := ps) (r := r) (n := n) hn).unitary
        (ket (packState (ps := ps) c d q (fun _ => false) fc false false (fun _ => false))) =
      if fc then
        ∑ p' : Bool × Qubits n, (H_hat n p' (d, q)) •
          ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) true false false (fun _ => false))
      else
        ket (packState (ps := ps) c d q (fun _ => false) false false false (fun _ => false)) := by
  simp only [hHatCirc, circuit_unitary_append, act_mul]
  rw [act_toffoliFHC]
  cases fc
  · simp only [Bool.false_and, Bool.xor_false, Bool.false_eq_true, ↓reduceIte]
    rw [act_chQCirc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [act_toffoliFHC]
    simp
  · simp only [Bool.true_and, Bool.false_xor, ↓reduceIte]
    rw [act_chQCirc]
    cases hd : d
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [act_toffoliFHC]
      simp only [Bool.true_and, Bool.xor_false]
      symm
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single false]
      · rw [Finset.sum_eq_single q]
        · simp [H_hat, controlled]
        · intro q' _ hq'; simp [H_hat, controlled, hq']
        · simp
      · intro b' _ hb'
        refine Finset.sum_eq_zero fun q' _ => ?_
        simp [H_hat, controlled, hb']
      · simp
    · simp only [↓reduceIte]
      rw [act_sum]
      have hterm : ∀ q' : Qubits n,
          act (embedCircuit (embToffoli (ps := ps) (r := r) (n := n)) ps.toffoliCirc).unitary
            ((hadamardN n q' q) •
              ket (packState (ps := ps) c true q' (fun _ => false) true true false (fun _ => false))) =
          (hadamardN n q' q) •
            ket (packState (ps := ps) c true q' (fun _ => false) true false false (fun _ => false)) := by
        intro q'
        rw [act_smul, act_toffoliFHC]
        simp
      simp_rw [hterm]
      symm
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single true]
      · refine Finset.sum_congr rfl fun q' _ => ?_
        simp [H_hat, controlled]
      · intro b' _ hb'
        refine Finset.sum_eq_zero fun q' _ => ?_
        simp [H_hat, controlled, hb']
      · simp

noncomputable def uBodyCirc {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n) : Circuit gates12 M' :=
  let hn : 1 ≤ n := by omega
  let hℓ : 2 ≤ ℓ := by
    have h4 : 4 ≤ n + 1 := by omega
    by_contra hlt
    have hle1 : ℓ ≤ 1 := by omega
    have hpow := Nat.le_pow_clog (b := 2) (by norm_num) (n + 1)
    have h2 : 2 ^ ℓ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle1
    norm_num at h2
    omega
  embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
    (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
  hHatCirc hn ++
  embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcCirc n) ++
  uTildeCirc m hℓ ++
  embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcAdjCirc n) ++
  hHatCirc hn ++
  embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
    (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)

lemma act_uBodyCirc {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n)
    (c : Qubits r) (d : Bool) (q : Qubits n) :
    act (uBodyCirc (ps := ps) (r := r) (n := n) hm hle).unitary
        (ket (packState (ps := ps) c d q (fun _ => false) false false false (fun _ => false))) =
      if c = (fun _ => false) then
        ∑ p' : Bool × Qubits n, (U_ideal n m p' (d, q)) •
          ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false))
      else
        ket (packState (ps := ps) c d q (fun _ => false) false false false (fun _ => false)) := by
  have hn : 1 ≤ n := by omega
  have hℓ : 2 ≤ ℓ := by
    have h4 : 4 ≤ n + 1 := by omega
    by_contra hlt
    have hle1 : ℓ ≤ 1 := by omega
    have hpow := Nat.le_pow_clog (b := 2) (by norm_num) (n + 1)
    have h2 : 2 ^ ℓ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle1
    norm_num at h2
    omega
  simp only [uBodyCirc, circuit_unitary_append, act_mul]
  rw [act_eqFCCirc]
  by_cases hc0 : c = (fun _ => false)
  · rw [if_pos hc0, if_pos hc0]
    simp only [show (!false : Bool) = true from rfl]
    rw [act_hHatCirc]
    simp only [↓reduceIte]
    rw [act_sum, act_sum, act_sum]
    have hmid : ∀ p₁ : Bool × Qubits n,
        act (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcAdjCirc n)).unitary
          (act (uTildeCirc (ps := ps) (r := r) (n := n) m hℓ).unitary
            (act (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcCirc n)).unitary
              ((H_hat n p₁ (d, q)) •
                ket (packState (ps := ps) c p₁.1 p₁.2 (fun _ => false) true false false (fun _ => false))))) =
        (H_hat n p₁ (d, q)) •
          ∑ p₂ : Bool × Qubits n, (U_tilde n m p₂ p₁) •
            ket (packState (ps := ps) c p₂.1 p₂.2 (fun _ => false) true false false (fun _ => false)) := by
      intro p₁
      rw [act_smul, act_smul, act_smul, act_hcQCirc, act_uTildeCirc hm hle]
      simp only [↓reduceIte, act_sum]
      congr 1
      have hterm : ∀ d' : Bool,
          act (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcAdjCirc n)).unitary
            ((U_op m (hammingWeight p₁.2) d' p₁.1) •
              ket (packState (ps := ps) c d' p₁.2 (natToBitsLSB ℓ (hammingWeight p₁.2)) true false false (fun _ => false))) =
          (U_op m (hammingWeight p₁.2) d' p₁.1) •
            ket (packState (ps := ps) c d' p₁.2 (fun _ => false) true false false (fun _ => false)) := by
        intro d'
        rw [act_smul, act_hcQAdjCirc]
      have hterm_sum : (∑ d' : Bool,
          act (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcAdjCirc n)).unitary
            ((U_op m (hammingWeight p₁.2) d' p₁.1) •
              ket (packState (ps := ps) c d' p₁.2 (natToBitsLSB ℓ (hammingWeight p₁.2)) true false false (fun _ => false)))) =
          ∑ d' : Bool, (U_op m (hammingWeight p₁.2) d' p₁.1) •
            ket (packState (ps := ps) c d' p₁.2 (fun _ => false) true false false (fun _ => false)) :=
        Finset.sum_congr rfl fun d' _ => hterm d'
      rw [hterm_sum]
      symm
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun d' _ => ?_
      rw [Finset.sum_eq_single p₁.2]
      · simp [U_tilde]
      · intro q₂ _ hq₂; simp [U_tilde, hq₂]
      · simp
    have hmid_sum : (∑ p₁ : Bool × Qubits n,
        act (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcAdjCirc n)).unitary
          (act (uTildeCirc (ps := ps) (r := r) (n := n) m hℓ).unitary
            (act (embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcCirc n)).unitary
              ((H_hat n p₁ (d, q)) •
                ket (packState (ps := ps) c p₁.1 p₁.2 (fun _ => false) true false false (fun _ => false)))))) =
        ∑ p₁ : Bool × Qubits n, (H_hat n p₁ (d, q)) •
          ∑ p₂ : Bool × Qubits n, (U_tilde n m p₂ p₁) •
            ket (packState (ps := ps) c p₂.1 p₂.2 (fun _ => false) true false false (fun _ => false)) :=
      Finset.sum_congr rfl fun p₁ _ => hmid p₁
    rw [hmid_sum]
    rw [act_sum]
    have hlast : ∀ p₁ : Bool × Qubits n,
        act (hHatCirc (ps := ps) (r := r) (n := n) hn).unitary
          ((H_hat n p₁ (d, q)) •
            ∑ p₂ : Bool × Qubits n, (U_tilde n m p₂ p₁) •
              ket (packState (ps := ps) c p₂.1 p₂.2 (fun _ => false) true false false (fun _ => false))) =
        ∑ p₂ : Bool × Qubits n, ∑ p' : Bool × Qubits n,
          (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
            ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) true false false (fun _ => false)) := by
      intro p₁
      rw [act_smul, act_sum]
      have hterm2 : ∀ p₂ : Bool × Qubits n,
          (H_hat n p₁ (d, q)) •
            act (hHatCirc (ps := ps) (r := r) (n := n) hn).unitary
              ((U_tilde n m p₂ p₁) •
                ket (packState (ps := ps) c p₂.1 p₂.2 (fun _ => false) true false false (fun _ => false))) =
          ∑ p' : Bool × Qubits n,
            (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
              ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) true false false (fun _ => false)) := by
        intro p₂
        rw [act_smul, act_hHatCirc]
        simp only [↓reduceIte, Finset.smul_sum]
        refine Finset.sum_congr rfl fun p' _ => ?_
        rw [smul_smul, smul_smul]; congr 1; ring
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun p₂ _ => hterm2 p₂
    have hlast_sum : (∑ p₁ : Bool × Qubits n,
        act (hHatCirc (ps := ps) (r := r) (n := n) hn).unitary
          ((H_hat n p₁ (d, q)) •
            ∑ p₂ : Bool × Qubits n, (U_tilde n m p₂ p₁) •
              ket (packState (ps := ps) c p₂.1 p₂.2 (fun _ => false) true false false (fun _ => false)))) =
        ∑ p₁ : Bool × Qubits n, ∑ p₂ : Bool × Qubits n, ∑ p' : Bool × Qubits n,
          (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
            ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) true false false (fun _ => false)) :=
      Finset.sum_congr rfl fun p₁ _ => hlast p₁
    rw [hlast_sum]
    rw [act_sum]
    have hfin : ∀ p₁ : Bool × Qubits n,
        act (embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
              (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).unitary
          (∑ p₂ : Bool × Qubits n, ∑ p' : Bool × Qubits n,
            (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
              ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) true false false (fun _ => false))) =
        ∑ p₂ : Bool × Qubits n, ∑ p' : Bool × Qubits n,
          (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
            ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false)) := by
      intro p₁
      rw [act_sum]
      refine Finset.sum_congr rfl fun p₂ _ => ?_
      rw [act_sum]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [act_smul, act_eqFCCirc, if_pos hc0]
      simp
    have hfin_sum : (∑ p₁ : Bool × Qubits n,
        act (embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
              (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).unitary
          (∑ p₂ : Bool × Qubits n, ∑ p' : Bool × Qubits n,
            (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
              ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) true false false (fun _ => false)))) =
        ∑ p₁ : Bool × Qubits n, ∑ p₂ : Bool × Qubits n, ∑ p' : Bool × Qubits n,
          (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
            ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false)) :=
      Finset.sum_congr rfl fun p₁ _ => hfin p₁
    rw [hfin_sum]
    have hsw1 : (∑ p₁ : Bool × Qubits n, ∑ p₂ : Bool × Qubits n, ∑ p' : Bool × Qubits n,
          (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
            ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false))) =
        ∑ p' : Bool × Qubits n, ∑ p₂ : Bool × Qubits n, ∑ p₁ : Bool × Qubits n,
          (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
            ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false)) := by
      rw [Finset.sum_comm]
      have hs : ∀ p₂ : Bool × Qubits n,
          (∑ p₁ : Bool × Qubits n, ∑ p' : Bool × Qubits n,
            (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
              ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false))) =
          ∑ p' : Bool × Qubits n, ∑ p₁ : Bool × Qubits n,
            (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
              ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false)) :=
        fun _ => Finset.sum_comm
      have hs_sum : (∑ p₂ : Bool × Qubits n, ∑ p₁ : Bool × Qubits n, ∑ p' : Bool × Qubits n,
            (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
              ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false))) =
          ∑ p₂ : Bool × Qubits n, ∑ p' : Bool × Qubits n, ∑ p₁ : Bool × Qubits n,
            (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
              ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false)) :=
        Finset.sum_congr rfl fun p₂ _ => hs p₂
      rw [hs_sum]
      exact Finset.sum_comm
    rw [hsw1]
    refine Finset.sum_congr rfl fun p' _ => ?_
    have hsm : ∀ p₂ : Bool × Qubits n,
        (∑ p₁ : Bool × Qubits n,
          (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
            ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false))) =
        (∑ p₁ : Bool × Qubits n,
          H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
          ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false)) :=
      fun _ => (Finset.sum_smul).symm
    have hsm_sum : (∑ p₂ : Bool × Qubits n, ∑ p₁ : Bool × Qubits n,
          (H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
            ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false))) =
        ∑ p₂ : Bool × Qubits n, (∑ p₁ : Bool × Qubits n,
          H_hat n p' p₂ * U_tilde n m p₂ p₁ * H_hat n p₁ (d, q)) •
          ket (packState (ps := ps) c p'.1 p'.2 (fun _ => false) false false false (fun _ => false)) :=
      Finset.sum_congr rfl fun p₂ _ => hsm p₂
    rw [hsm_sum, ← Finset.sum_smul]
    congr 1
    simp only [U_ideal, Matrix.mul_apply]
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  · rw [if_neg hc0, if_neg hc0]
    rw [act_hHatCirc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [act_hcQCirc, act_uTildeCirc hm hle]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [act_hcQAdjCirc, act_hHatCirc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [act_eqFCCirc, if_neg hc0]

/-! ### Lift from `Fin M'` to `Fin (M' + 1)` with `M = Fin.last M'` and controlled `majOracle` -/

private noncomputable def minusAmp (b : Bool) : ℂ :=
  if b then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)

private lemma minusAmp_neg (b : Bool) : minusAmp (!b) = -minusAmp b := by
  cases b <;> simp [minusAmp]

private lemma sum_norm_sq_minusAmp : ∑ b : Bool, ‖minusAmp b‖ ^ 2 = 1 := by
  simp only [Fintype.sum_bool, minusAmp, ↓reduceIte, Bool.false_eq_true, norm_neg,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  rw [← two_mul, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

noncomputable def withMinus {M : ℕ} (φ : EuclideanSpace ℂ (Qubits M)) :
    EuclideanSpace ℂ (Qubits (M + 1)) :=
  WithLp.toLp 2 fun z => φ (Fin.init z) * minusAmp (z (Fin.last M))

lemma withMinus_norm {M : ℕ} (φ : EuclideanSpace ℂ (Qubits M)) : ‖withMinus φ‖ = ‖φ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_equiv (qubitsSnocEquiv M) _ (fun p => ‖φ p.1‖ ^ 2 * ‖minusAmp p.2‖ ^ 2)
    (fun z => by simp [withMinus, qubitsSnocEquiv, mul_pow])]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, sum_norm_sq_minusAmp, mul_one]

lemma withMinus_sub {M : ℕ} (φ₁ φ₂ : EuclideanSpace ℂ (Qubits M)) :
    withMinus (φ₁ - φ₂) = withMinus φ₁ - withMinus φ₂ := by
  ext z; simp [withMinus, sub_mul]

lemma probEvent_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ z, P z ↔ Q z) : probEvent ψ P = probEvent ψ Q := by
  simp only [probEvent]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hPQ]

lemma probEvent_withMinus {M : ℕ} (φ : EuclideanSpace ℂ (Qubits M))
    (P : Qubits M → Prop) [DecidablePred P] :
    open Classical in
    probEvent (withMinus φ) (fun z => P (Fin.init z)) = probEvent φ P := by
  classical
  simp only [probEvent, prob, ket, EuclideanSpace.inner_single_left, Finset.sum_filter,
    map_one, one_mul]
  rw [Fintype.sum_equiv (qubitsSnocEquiv M) _
    (fun p : Qubits M × Bool => if P p.1 then ‖φ p.1‖ ^ 2 * ‖minusAmp p.2‖ ^ 2 else 0)
    (fun z => by
      by_cases hz : P (Fin.init z)
      · simp [qubitsSnocEquiv, withMinus, hz, mul_pow]
      · simp [qubitsSnocEquiv, hz])]
  rw [Fintype.sum_prod_type]
  have hrow : ∀ x : Qubits M,
      ∑ b : Bool, (if P x then ‖φ x‖ ^ 2 * ‖minusAmp b‖ ^ 2 else 0) =
        if P x then ‖φ x‖ ^ 2 else 0 := by
    intro x
    by_cases hx : P x
    · simp only [hx, ↓reduceIte]
      rw [← Finset.mul_sum, sum_norm_sq_minusAmp, mul_one]
    · simp [hx]
  simp_rw [hrow]

lemma act_embedOp_castSucc_withMinus {M : ℕ} (G : Matrix (Qubits M) (Qubits M) ℂ)
    (φ : EuclideanSpace ℂ (Qubits M)) :
    act (embedOp G (Fin.castAddEmb 1)) (withMinus φ) = withMinus (act G φ) := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, withMinus, embedOp, Matrix.of_apply]
  have hcast : ∀ j : Fin M, Fin.castAddEmb 1 j = j.castSucc := fun _ => rfl
  have hrange : ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) ↔ a = Fin.last M := by
    intro a
    refine Fin.lastCases ?_ ?_ a
    · constructor
      · intro _; rfl
      · rintro _ ⟨i, hi⟩
        have hi' := congrArg Fin.val hi
        simp [Fin.castAddEmb] at hi'
        omega
    · intro i
      constructor
      · intro h; exact absurd ⟨i, rfl⟩ h
      · intro h
        have h' := congrArg Fin.val h
        simp at h'
        omega
  have hprod : (∑ z : Qubits (M + 1),
      (if ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) → y a = z a
        then G (y ∘ Fin.castAddEmb 1) (z ∘ Fin.castAddEmb 1) else 0) *
      (φ (Fin.init z) * minusAmp (z (Fin.last M)))) =
      ∑ p : Qubits M × Bool,
      (if ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) →
          y a = Fin.snoc (α := fun _ => Bool) p.1 p.2 a
        then G (y ∘ Fin.castAddEmb 1) (Fin.snoc (α := fun _ => Bool) p.1 p.2 ∘ Fin.castAddEmb 1)
        else 0) *
      (φ p.1 * minusAmp p.2) := by
    refine Fintype.sum_equiv (qubitsSnocEquiv M) _ _ fun z => ?_
    dsimp only [qubitsSnocEquiv]
    change (if ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) → y a = z a
        then G (y ∘ Fin.castAddEmb 1) (z ∘ Fin.castAddEmb 1) else 0) *
        (φ (Fin.init z) * minusAmp (z (Fin.last M))) =
      (if ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) →
          y a = Fin.snoc (α := fun _ => Bool) (Fin.init z) (z (Fin.last M)) a
        then G (y ∘ Fin.castAddEmb 1)
          (Fin.snoc (α := fun _ => Bool) (Fin.init z) (z (Fin.last M)) ∘ Fin.castAddEmb 1)
        else 0) *
        (φ (Fin.init z) * minusAmp (z (Fin.last M)))
    simp_rw [Fin.snoc_init_self]
  rw [hprod, Fintype.sum_prod_type, Finset.sum_comm]
  have hcomp : ∀ x : Qubits M,
      (Fin.snoc (α := fun _ => Bool) x (y (Fin.last M)) ∘ Fin.castAddEmb 1) = x := by
    intro x; funext j; rw [Function.comp_apply, hcast j, Fin.snoc_castSucc]
  have hy_comp : (y ∘ Fin.castAddEmb 1) = Fin.init y := by
    funext j; rfl
  rw [Finset.sum_eq_single (y (Fin.last M))]
  · have hpos_cond : ∀ x : Qubits M,
        ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) →
          y a = Fin.snoc (α := fun _ => Bool) x (y (Fin.last M)) a := by
      intro x a ha
      rw [(hrange a).mp ha, Fin.snoc_last]
    have hsum_term : ∀ x : Qubits M,
        (if ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) →
            y a = Fin.snoc (α := fun _ => Bool) x (y (Fin.last M)) a
          then G (y ∘ Fin.castAddEmb 1) (Fin.snoc (α := fun _ => Bool) x (y (Fin.last M)) ∘ Fin.castAddEmb 1)
          else 0) * (φ x * minusAmp (y (Fin.last M))) =
        (G (Fin.init y) x * φ x) * minusAmp (y (Fin.last M)) := by
      intro x
      rw [if_pos (hpos_cond x), hy_comp, hcomp x]
      ring
    simp_rw [hsum_term, ← Finset.sum_mul]
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    have hnot : ¬ (∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) →
        y a = Fin.snoc (α := fun _ => Bool) x b a) := by
      intro h
      have hlast := h (Fin.last M) ((hrange (Fin.last M)).mpr rfl)
      simp only [Fin.snoc_last] at hlast
      exact hb hlast.symm
    rw [if_neg hnot, zero_mul]
  · simp

private lemma majJunta_eq_neg_one_iff {n : ℕ} (A : Finset (Fin n)) (x : Qubits n) :
    decide (majJunta A (Finset.univ.filter fun i => x i = true) = -1) = majorityBit A x := by
  have hset : A ∩ (Finset.univ.filter fun i => x i = true) = A.filter fun i => x i := by
    ext i; simp
  rw [majJunta, majorityBit, hset]
  split_ifs with h1 <;> simp_all

noncomputable def phaseCtrlOracle {M n : ℕ} (A : Finset (Fin n)) (ctrl : Fin M)
    (regQ : Fin n ↪ Fin M) : Matrix (Qubits M) (Qubits M) ℂ :=
  Matrix.diagonal fun x => if x ctrl && majorityBit A (x ∘ regQ) then (-1 : ℂ) else 1

private lemma oracleStep_ctrl_query_apply_eq {S : Set Gate} {M n : ℕ} (A : Finset (Fin n)) (ctrl : Fin M)
    (regQ : Fin n ↪ Fin M)
    (wires : Fin (n + 1) ↪ Fin (M + 1))
    (hw_init : ∀ i : Fin n, wires i.castSucc = (regQ i).castSucc)
    (hw_last : wires (Fin.last n) = Fin.last M)
    (hc : ∀ c, some ctrl.castSucc = some c → c ∉ Set.range wires)
    (y z : Qubits (M + 1)) :
    OracleStep.mat (S := S) (r := 1) (a := fun _ => n + 1)
      (fun _ => majOracle A) (.query 0 false (some ctrl.castSucc) wires hc) y z =
    if z = Fin.snoc (α := fun _ => Bool) (Fin.init y)
      (xor (y (Fin.last M)) (Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ)))
    then 1 else 0 := by
  let w' : Fin (n + 2) ↪ Fin (M + 1) :=
    ⟨Fin.cons ctrl.castSucc wires, Fin.cons_injective_iff.2 ⟨hc ctrl.castSucc rfl, wires.injective⟩⟩
  change embedOp (controlledQubits (majOracle A)) w' y z = _
  simp only [embedOp, Matrix.of_apply, controlledQubits, Matrix.submatrix_apply, controlled]
  have hw'0 : ∀ u : Qubits (M + 1), (u ∘ w') 0 = u ctrl.castSucc := fun _ => rfl
  have hw'_tail : ∀ u : Qubits (M + 1), Fin.tail (u ∘ w') = u ∘ wires := fun u => by
    funext i; rfl
  have hw_init_comp : ∀ u : Qubits (M + 1), Fin.init (u ∘ wires) = Fin.init u ∘ regQ := fun u => by
    funext i; simp [Fin.init, hw_init i]
  have hw_last_comp : ∀ u : Qubits (M + 1), (u ∘ wires) (Fin.last n) = u (Fin.last M) := fun u => by
    simp [hw_last]
  by_cases hz_eq : z = Fin.snoc (α := fun _ => Bool) (Fin.init y)
      (xor (y (Fin.last M)) (Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ)))
  · rw [if_pos hz_eq]
    have hoff : ∀ a : Fin (M + 1), a ∉ Set.range w' → y a = z a := by
      intro a ha
      rw [hz_eq]
      refine Fin.lastCases ?_ ?_ a ha
      · intro hl; exfalso; apply hl; refine ⟨(Fin.last n).succ, ?_⟩; simp [w', hw_last]
      · intro i _; simp [Fin.snoc_castSucc, Fin.init]
    rw [if_pos hoff]
    have hctrl_yz : y ctrl.castSucc = z ctrl.castSucc := by
      rw [hz_eq, Fin.snoc_castSucc]; rfl
    simp only [hw'0, hw'_tail, if_pos hctrl_yz]
    cases hcval : y ctrl.castSucc
    · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.one_apply, hw'_tail]
      have hyw : y ∘ wires = z ∘ wires := by
        funext j
        refine Fin.lastCases ?_ ?_ j
        · simp [hw_last, hz_eq, hcval, Fin.init]
        · intro i; simp [hw_init i, hz_eq, Fin.init]
      rw [if_pos hyw]
    · simp only [↓reduceIte, majOracle, Matrix.of_apply, majJunta_eq_neg_one_iff]
      have hmaj : y ∘ wires = Fin.snoc (α := fun _ => Bool) (Fin.init (z ∘ wires))
          (xor ((z ∘ wires) (Fin.last n)) (majorityBit A (Fin.init (z ∘ wires)))) := by
        funext j
        refine Fin.lastCases ?_ ?_ j
        · simp only [hw_last_comp, hw_init_comp, hz_eq, Fin.snoc_last, Fin.init_snoc]
          simp [Fin.init, hcval]
        · intro i
          simp only [Function.comp_apply, hw_init i, Fin.snoc_castSucc, hw_init_comp, hz_eq,
            Fin.init_def]
      rw [if_pos hmaj]
  · rw [if_neg hz_eq]
    by_cases hoff : ∀ a : Fin (M + 1), a ∉ Set.range w' → y a = z a
    · rw [if_pos hoff]
      simp only [hw'0, hw'_tail]
      by_cases hctrl_yz : y ctrl.castSucc = z ctrl.castSucc
      · rw [if_pos hctrl_yz]
        have not_mem_w' : ∀ i : Fin M, i ≠ ctrl → (∀ q, regQ q ≠ i) → i.castSucc ∉ Set.range w' := by
          intro i hi hq ⟨x, hx⟩
          refine Fin.cases ?_ ?_ x hx
          · intro h0; exact hi (Fin.ext (by have h0' := congrArg Fin.val h0; simpa [w'] using h0'.symm))
          · intro j hj
            refine Fin.lastCases ?_ ?_ j hj
            · intro hl; have hl' := congrArg Fin.val hl; simp [w', hw_last] at hl'; omega
            · intro q hq'; apply hq q; exact Fin.ext (by have hq'' := congrArg Fin.val hq'; simpa [w', hw_init q] using hq'')
        cases hcval : y ctrl.castSucc
        · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.one_apply]
          rw [if_neg]
          intro hyw; apply hz_eq; funext a
          refine Fin.lastCases ?_ ?_ a
          · have hl := congrFun hyw (Fin.last n)
            change (y ∘ wires) (Fin.last n) = (z ∘ wires) (Fin.last n) at hl
            rw [hw_last_comp y, hw_last_comp z] at hl
            have hcval' : Fin.init y ctrl = false := by simpa [Fin.init] using hcval
            simp [Fin.snoc_last, hcval', hl]
          · intro i
            by_cases hi : i = ctrl
            · subst hi; simpa [Fin.snoc_castSucc, Fin.init] using hctrl_yz.symm
            · by_cases hq : ∃ q, regQ q = i
              · obtain ⟨q, rfl⟩ := hq
                have hqi := congrFun hyw q.castSucc
                change y (wires q.castSucc) = z (wires q.castSucc) at hqi
                rw [hw_init q] at hqi
                simpa [Fin.snoc_castSucc, Fin.init] using hqi.symm
              · have hq' : ∀ q, regQ q ≠ i := fun q h => hq ⟨q, h⟩
                simpa [Fin.snoc_castSucc, Fin.init] using (hoff i.castSucc (not_mem_w' i hi hq')).symm
        · simp only [↓reduceIte, majOracle, Matrix.of_apply, majJunta_eq_neg_one_iff]
          rw [if_neg]
          intro hmaj; apply hz_eq; funext a
          refine Fin.lastCases ?_ ?_ a
          · have hl := congrFun hmaj (Fin.last n)
            simp only [hw_last_comp, Fin.snoc_last, hw_init_comp] at hl
            have hinit_q : Fin.init z ∘ regQ = Fin.init y ∘ regQ := by
              funext q
              have hq := congrFun hmaj q.castSucc
              simp only [Function.comp_apply, hw_init q, Fin.snoc_castSucc, hw_init_comp] at hq
              exact hq.symm
            rw [hl, hinit_q]
            have hcval' : Fin.init y ctrl = true := by simpa [Fin.init] using hcval
            simp only [Fin.snoc_last, hcval', Bool.true_and,
              Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
          · intro i
            by_cases hi : i = ctrl
            · subst hi; simpa [Fin.snoc_castSucc, Fin.init] using hctrl_yz.symm
            · by_cases hq : ∃ q, regQ q = i
              · obtain ⟨q, rfl⟩ := hq
                have hqi := congrFun hmaj q.castSucc
                simp only [Function.comp_apply, hw_init q, Fin.snoc_castSucc, hw_init_comp] at hqi
                simpa [Fin.snoc_castSucc, Fin.init] using hqi.symm
              · have hq' : ∀ q, regQ q ≠ i := fun q h => hq ⟨q, h⟩
                simpa [Fin.snoc_castSucc, Fin.init] using (hoff i.castSucc (not_mem_w' i hi hq')).symm
      · rw [if_neg hctrl_yz]
    · rw [if_neg hoff]

lemma act_ctrl_majOracle_withMinus {S : Set Gate} {M n : ℕ} (A : Finset (Fin n)) (ctrl : Fin M)
    (regQ : Fin n ↪ Fin M) (wires : Fin (n + 1) ↪ Fin (M + 1))
    (hw_init : ∀ i : Fin n, wires i.castSucc = (regQ i).castSucc)
    (hw_last : wires (Fin.last n) = Fin.last M)
    (hc : ∀ c, some ctrl.castSucc = some c → c ∉ Set.range wires)
    (φ : EuclideanSpace ℂ (Qubits M)) :
    act (OracleStep.mat (S := S) (r := 1) (a := fun _ => n + 1)
      (fun _ => majOracle A) (.query 0 false (some ctrl.castSucc) wires hc)) (withMinus φ) =
    withMinus (act (phaseCtrlOracle A ctrl regQ) φ) := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, withMinus, phaseCtrlOracle,
    Matrix.diagonal_apply]
  simp_rw [oracleStep_ctrl_query_apply_eq A ctrl regQ wires hw_init hw_last hc]
  let bit := Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ)
  rw [Finset.sum_eq_single (Fin.snoc (α := fun _ => Bool) (Fin.init y) (xor (y (Fin.last M)) bit))]
  · rw [if_pos rfl, one_mul, Fin.init_snoc, Fin.snoc_last]
    rw [Finset.sum_eq_single (Fin.init y)]
    · by_cases hbit : bit = true
      · have h1 : Fin.init y ctrl = true := (Bool.and_eq_true _ _).mp hbit |>.1
        have h2 : majorityBit A (Fin.init y ∘ regQ) = true := (Bool.and_eq_true _ _).mp hbit |>.2
        rw [hbit, Bool.xor_true, minusAmp_neg]
        simp only [h1, h2, Bool.true_and, ↓reduceIte]
        ring
      · have hbitf : bit = false := Bool.eq_false_iff.mpr hbit
        rw [hbitf, Bool.xor_false]
        have hbitf' : (Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ)) = false := hbitf
        simp only [hbitf', Bool.false_eq_true, ↓reduceIte]
        ring
    · intro x _ hx; simp [hx.symm]
    · simp
  · intro z _ hz
    have hz' : z ≠ Fin.snoc (α := fun _ => Bool) (Fin.init y)
        (xor (y (Fin.last M)) (Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ))) := hz
    rw [if_neg hz', zero_mul]
  · simp

private def prepareMinusWires (M : ℕ) : Fin 1 ↪ Fin (M + 1) :=
  ⟨fun _ => Fin.last M,
    fun u v _ => Fin.ext (Nat.lt_one_iff.mp u.2 |>.trans (Nat.lt_one_iff.mp v.2).symm)⟩

private noncomputable def prepareMinusStep (M : ℕ) :
    OracleStep gates12 (fun _ : Fin 1 => n + 1) (M + 1) :=
  OracleStep.gate
    ⟨Gate.ofMatrix1 (hadamard * pauliX),
      gate_ofMatrix1_mem_gates12 hadamard_mul_pauliX_mem_unitaryGroup,
      prepareMinusWires M⟩

private lemma act_prepareMinusStep (M : ℕ)
    (orc : (k : Fin 1) → Matrix (Qubits ((fun _ : Fin 1 => n + 1) k)) (Qubits ((fun _ : Fin 1 => n + 1) k)) ℂ) :
    act (OracleStep.mat orc (prepareMinusStep (n := n) M)) (zeroKet (M + 1)) = withMinus (zeroKet M) := by
  change act (embedOp ((hadamard * pauliX).submatrix (fun b => b 0) (fun b => b 0))
    (prepareMinusWires M)) (zeroKet (M + 1)) = withMinus (zeroKet M)
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, embedOp, Matrix.of_apply,
    Matrix.submatrix_apply, zeroKet, ket, withMinus]
  rw [Finset.sum_eq_single (fun _ : Fin (M + 1) => false)]
  · simp only [PiLp.single_apply, ↓reduceIte, mul_one]
    by_cases hinit : Fin.init y = fun _ : Fin M => false
    · have hcond : ∀ b : Fin (M + 1), b ∉ Set.range (prepareMinusWires M) → y b = false := by
        intro b hb
        have hne : b ≠ Fin.last M := fun heq => hb ⟨0, heq.symm⟩
        rcases Fin.exists_castSucc_eq.mpr hne with ⟨i, rfl⟩
        exact congrFun hinit i
      rw [if_pos hcond, if_pos hinit, one_mul]
      change (hadamard * pauliX) (y (Fin.last M)) false = minusAmp (y (Fin.last M))
      cases y (Fin.last M) <;>
        simp [hadamard, pauliX, Matrix.mul_apply, minusAmp]
    · have hcond : ¬ ∀ b : Fin (M + 1), b ∉ Set.range (prepareMinusWires M) → y b = false := by
        intro h; apply hinit; funext i; apply h i.castSucc
        rintro ⟨_, h0⟩; exact Fin.castSucc_ne_last i h0.symm
      rw [if_neg hcond, if_neg hinit, zero_mul]
  · intro z _ hz; simp only [PiLp.single_apply, if_neg hz, mul_zero]
  · simp

noncomputable def liftToFull (c₀ : Circuit gates12 M') :
    OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (M' + 1) :=
  (embedCircuit (Fin.castAddEmb 1) c₀).map OracleStep.gate

lemma liftToFull_unitary (c₀ : Circuit gates12 M')
    (orc : (k : Fin 1) → Matrix (Qubits ((fun _ : Fin 1 => n + 1) k)) (Qubits ((fun _ : Fin 1 => n + 1) k)) ℂ) :
    (liftToFull (ps := ps) (r := r) (n := n) c₀).unitary orc =
      embedOp c₀.unitary (Fin.castAddEmb 1) := by
  unfold liftToFull
  rw [oracleCircuit_unitary_lift, embedCircuit_unitary]

lemma liftToFull_act (c₀ : Circuit gates12 M')
    (orc : (k : Fin 1) → Matrix (Qubits ((fun _ : Fin 1 => n + 1) k)) (Qubits ((fun _ : Fin 1 => n + 1) k)) ℂ)
    (φ : EuclideanSpace ℂ (Qubits M')) :
    act ((liftToFull (ps := ps) (r := r) (n := n) c₀).unitary orc) (withMinus φ) =
      withMinus (act c₀.unitary φ) := by
  rw [liftToFull_unitary, act_embedOp_castSucc_withMinus]

lemma liftToFull_queryCount (c₀ : Circuit gates12 M') :
    (liftToFull (ps := ps) (r := r) (n := n) c₀).queryCount 0 = 0 :=
  oracleCircuit_queryCount_lift _ _

lemma liftToFull_gateCount (c₀ : Circuit gates12 M') :
    (liftToFull (ps := ps) (r := r) (n := n) c₀).gateCount = c₀.length := by
  unfold liftToFull
  rw [oracleCircuit_gateCount_lift, embedCircuit, List.length_map]

lemma liftToFull_depth_le (c₀ : Circuit gates12 M') :
    nonOracleDepth (liftToFull (ps := ps) (r := r) (n := n) c₀) ≤
      nonOracleDepth (c₀.map OracleStep.gate : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) M') :=
  nonOracleDepth_embedCircuit (Fin.castAddEmb 1) c₀

noncomputable def oracleWires : Fin (n + 1) ↪ Fin (M' + 1) :=
  let f : Fin (n + 1) → Fin (M' + 1) := fun i =>
    if h : i.1 < n then (regQ (ps := ps) (r := r) (n := n) ⟨i.1, h⟩).castSucc else Fin.last M'
  ⟨f, fun a b hab => by
    have ha := a.isLt
    have hb := b.isLt
    have hv : (f a).1 = (f b).1 := congrArg Fin.val hab
    have hregq : ∀ (k : ℕ) (hk : k < n),
        ((regQ (ps := ps) (r := r) (n := n) ⟨k, hk⟩).castSucc).1 = r + 1 + k :=
      fun _ _ => rfl
    have hlast : (Fin.last M').1 = r + 1 + n + ℓ + 3 + Amax := rfl
    dsimp only [f] at hv
    by_cases ha_lt : a.1 < n <;> by_cases hb_lt : b.1 < n
    · rw [dif_pos ha_lt, dif_pos hb_lt, hregq, hregq] at hv
      ext; omega
    · rw [dif_pos ha_lt, dif_neg hb_lt, hregq, hlast] at hv
      omega
    · rw [dif_neg ha_lt, dif_pos hb_lt, hlast, hregq] at hv
      omega
    · ext; omega⟩

@[simp] lemma oracleWires_apply (i : Fin (n + 1)) :
    oracleWires (ps := ps) (r := r) (n := n) i =
      if h : i.1 < n then (regQ (ps := ps) (r := r) (n := n) ⟨i.1, h⟩).castSucc else Fin.last M' := rfl

lemma oracleWires_init (i : Fin n) :
    oracleWires (ps := ps) (r := r) (n := n) i.castSucc = (regQ i).castSucc := by
  simp only [oracleWires_apply, Fin.val_castSucc, i.isLt, ↓reduceDIte]

lemma oracleWires_last :
    oracleWires (ps := ps) (r := r) (n := n) (Fin.last n) = Fin.last M' := by
  simp only [oracleWires_apply, Fin.val_last, lt_self_iff_false, ↓reduceDIte]

lemma oracleWires_hc (c : Fin (M' + 1)) (hc : some (wireFQ (ps := ps) (r := r) (n := n)).castSucc = some c) :
    c ∉ Set.range (oracleWires (ps := ps) (r := r) (n := n)) := by
  have hceq : c = (wireFQ (ps := ps) (r := r) (n := n)).castSucc := (Option.some.inj hc).symm
  subst hceq
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hwfq : ((wireFQ (ps := ps) (r := r) (n := n)).castSucc).1 = r + 1 + n + ℓ + 2 := rfl
  have hregq : ∀ k : Fin n, ((regQ (ps := ps) (r := r) (n := n) k).castSucc).1 = r + 1 + k.1 :=
    fun _ => rfl
  have hlast : (Fin.last M').1 = r + 1 + n + ℓ + 3 + Amax := rfl
  rw [oracleWires_apply] at hv
  by_cases hi_lt : i.1 < n
  · rw [dif_pos hi_lt, hregq, hwfq] at hv
    omega
  · rw [dif_neg hi_lt, hlast, hwfq] at hv
    omega

noncomputable def queryStepFull : OracleStep gates12 (fun _ : Fin 1 => n + 1) (M' + 1) :=
  OracleStep.query 0 false (some (wireFQ (ps := ps) (r := r) (n := n)).castSucc)
    (oracleWires (ps := ps) (r := r) (n := n)) (oracleWires_hc (ps := ps) (r := r) (n := n))

def patFQ (r : ℕ) : Qubits (r + 1) :=
  fun i => if i.1 < r then false else true

noncomputable def stepCirc {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n) (c_step : Fin (2 ^ r)) :
    OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (M' + 1) :=
  let pat := natToBitsLSB r c_step.1
  let xc := liftToFull (ps := ps) (r := r) (n := n) (ctrl0XCirc pat)
  let fq := liftToFull (ps := ps) (r := r) (n := n)
    (embedCircuit embEqFQ (ps.eqCirc (r + 1) (patFQ r) pauliX pauliX_mem_unitaryGroup))
  let ubody := liftToFull (ps := ps) (r := r) (n := n) (uBodyCirc hm hle)
  xc ++ fq ++ [queryStepFull] ++ fq ++ ubody ++ xc

lemma act_stepCirc_basis {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n) (c_step : Fin (2 ^ r))
    (A : Finset (Fin n)) (c : Qubits r) (d : Bool) (q : Qubits n) :
    act ((stepCirc (ps := ps) (r := r) (n := n) hm hle c_step).unitary fun _ => majOracle A)
        (withMinus (ket (coreEmbHom (c, d, q)))) =
      withMinus (
        if (if d then c else fun i => xor (c i) (natToBitsLSB r c_step.1 i)) = (fun _ => false) then
          (if d && majorityBit A q then (-1 : ℂ) else 1) •
            ∑ p' : Bool × Qubits n, (U_ideal n m p' (d, q)) •
              ket (coreEmbHom (if p'.1 then fun _ => false else natToBitsLSB r c_step.1, p'.1, p'.2))
        else
          ket (coreEmbHom (c, d, q))) := by
  let pat := natToBitsLSB r c_step.1
  let c'' : Qubits r := if d then c else fun i => xor (c i) (pat i)
  have h1 : act (ctrl0XCirc (ps := ps) (r := r) (n := n) pat).unitary (ket (coreEmbHom (c, d, q))) =
      ket (packState (ps := ps) c'' d q (fun _ => false) false false false (fun _ => false)) := by
    change act (ctrl0XCirc pat).unitary (ket (packState c d q (fun _ => false) false false false (fun _ => false))) = _
    rw [act_ctrl0XCirc]
    congr 2; cases d <;> rfl
  have haddr : ((fun i : Fin (r + 1) => if h : i.1 < r then c'' ⟨i.1, h⟩ else d) = patFQ r) ↔
      (c'' = (fun _ => false) ∧ d = true) := by
    constructor
    · intro h
      have hd := congrFun h ⟨r, by omega⟩
      simp only [lt_self_iff_false, ↓reduceDIte, patFQ] at hd
      refine ⟨?_, hd⟩
      funext i
      have hi := congrFun h ⟨i.1, by omega⟩
      simpa [i.isLt, patFQ] using hi
    · rintro ⟨hc'', hd⟩
      funext i
      by_cases hi : i.1 < r
      · simp [hi, patFQ, hc'']
      · simp [hi, patFQ, hd]
  have h2 : act (embedCircuit (embEqFQ (ps := ps) (r := r) (n := n))
        (ps.eqCirc (r + 1) (patFQ r) pauliX pauliX_mem_unitaryGroup)).unitary
      (ket (packState (ps := ps) c'' d q (fun _ => false) false false false (fun _ => false))) =
      ket (packState (ps := ps) c'' d q (fun _ => false) false false
        (decide (c'' = fun _ => false) && d) (fun _ => false)) := by
    rw [act_eqFQCirc]
    by_cases hcond : c'' = (fun _ => false) ∧ d = true
    · rw [if_pos (haddr.mpr hcond)]; simp [hcond]
    · rw [if_neg (fun h => hcond (haddr.mp h))]
      have hf : (decide (c'' = fun _ => false) && d) = false := by
        by_cases h1 : c'' = fun _ => false <;> by_cases h2 : d = true <;> simp_all
      simp [hf]
  have h3 : act (phaseCtrlOracle A (wireFQ (ps := ps) (r := r) (n := n)) regQ)
      (ket (packState (ps := ps) c'' d q (fun _ => false) false false
        (decide (c'' = fun _ => false) && d) (fun _ => false))) =
      (if decide (c'' = fun _ => false) && d && majorityBit A q then (-1 : ℂ) else 1) •
        ket (packState (ps := ps) c'' d q (fun _ => false) false false
          (decide (c'' = fun _ => false) && d) (fun _ => false)) := by
    ext y
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, phaseCtrlOracle,
      Matrix.diagonal_apply, ket, PiLp.single_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (packState (ps := ps) c'' d q (fun _ => false) false false
        (decide (c'' = fun _ => false) && d) (fun _ => false))]
    · by_cases hy : y = packState (ps := ps) c'' d q (fun _ => false) false false
          (decide (c'' = fun _ => false) && d) (fun _ => false)
      · subst hy
        have hcomp_q : (packState (ps := ps) c'' d q (fun _ => false) false false
            (decide (c'' = fun _ => false) && d) (fun _ => false) ∘ regQ) = q := by
          funext i; exact packState_Q _ _ _ _ _ _ _ _ i
        rw [packState_FQ, hcomp_q]
        simp
      · simp [hy]
    · intro z _ hz; simp [hz]
    · simp
  have h4 : act (embedCircuit (embEqFQ (ps := ps) (r := r) (n := n))
        (ps.eqCirc (r + 1) (patFQ r) pauliX pauliX_mem_unitaryGroup)).unitary
      (ket (packState (ps := ps) c'' d q (fun _ => false) false false
        (decide (c'' = fun _ => false) && d) (fun _ => false))) =
      ket (packState (ps := ps) c'' d q (fun _ => false) false false false (fun _ => false)) := by
    rw [act_eqFQCirc]
    by_cases hcond : c'' = (fun _ => false) ∧ d = true
    · rw [if_pos (haddr.mpr hcond)]; simp [hcond]
    · rw [if_neg (fun h => hcond (haddr.mp h))]
      have hf : (decide (c'' = fun _ => false) && d) = false := by
        by_cases h1 : c'' = fun _ => false <;> by_cases h2 : d = true <;> simp_all
      simp [hf]
  have hq_unit : OracleCircuit.unitary [queryStepFull (ps := ps) (r := r) (n := n)] (fun _ => majOracle A) =
      OracleStep.mat (fun _ => majOracle A) queryStepFull := by
    simp [OracleCircuit.unitary]
  simp only [stepCirc, oracleCircuit_unitary_append, act_mul]
  rw [liftToFull_act, h1, liftToFull_act, h2, hq_unit]
  have hqry : act (OracleStep.mat (fun _ => majOracle A) (queryStepFull (ps := ps) (r := r) (n := n)))
      (withMinus (ket (packState (ps := ps) c'' d q (fun _ => false) false false
        (decide (c'' = fun _ => false) && d) (fun _ => false)))) =
      withMinus (act (phaseCtrlOracle A wireFQ regQ)
        (ket (packState (ps := ps) c'' d q (fun _ => false) false false
          (decide (c'' = fun _ => false) && d) (fun _ => false)))) := by
    change act (OracleStep.mat (S := gates12) (fun _ => majOracle A)
      (.query 0 false (some wireFQ.castSucc) oracleWires oracleWires_hc)) _ = _
    exact act_ctrl_majOracle_withMinus A wireFQ regQ oracleWires oracleWires_init oracleWires_last oracleWires_hc _
  rw [hqry, h3, liftToFull_act, act_smul, h4, liftToFull_act, act_smul, act_uBodyCirc hm hle]
  by_cases hc''0 : c'' = (fun _ => false)
  · have hif_pos : (if d then c else fun i => xor (c i) (natToBitsLSB r c_step.1 i)) = fun _ => false := hc''0
    simp only [hc''0, decide_true, hif_pos, ↓reduceIte, Bool.true_and, liftToFull_act, act_smul, act_sum]
    have hfin : ∀ p' : Bool × Qubits n,
        act (ctrl0XCirc (ps := ps) (r := r) (n := n) (natToBitsLSB r c_step.1)).unitary
          (ket (packState (ps := ps) (fun _ => false) p'.1 p'.2 (fun _ => false) false false false (fun _ => false))) =
        ket (coreEmbHom (ps := ps) (r := r) (n := n) (if p'.1 then fun _ => false else pat, p'.1, p'.2)) := by
      intro p'
      rw [act_ctrl0XCirc]
      congr 1
      have hc_eq : (fun i : Fin r => if p'.1 then false else xor false (natToBitsLSB r c_step.1 i)) =
          if p'.1 then fun _ => false else pat := by
        cases p'.1 <;> funext i <;> simp [pat]
      rw [hc_eq]
      rfl
    have hsum_fin : (∑ p' : Bool × Qubits n, (U_ideal n m p' (d, q)) •
        act (ctrl0XCirc (ps := ps) (r := r) (n := n) (natToBitsLSB r c_step.1)).unitary
          (ket (packState (ps := ps) (fun _ => false) p'.1 p'.2 (fun _ => false) false false false (fun _ => false)))) =
        ∑ p' : Bool × Qubits n, (U_ideal n m p' (d, q)) •
          ket (coreEmbHom (ps := ps) (r := r) (n := n) (if p'.1 then fun _ => false else pat, p'.1, p'.2)) :=
      Finset.sum_congr rfl fun p' _ => by rw [hfin p']
    rw [hsum_fin]
  · have hdec_c : decide (c'' = fun _ => false) = false := decide_eq_false hc''0
    have hif_neg : ¬ ((if d then c else fun i => xor (c i) (natToBitsLSB r c_step.1 i)) = fun _ => false) := hc''0
    rw [if_neg hc''0, if_neg hif_neg, hdec_c]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, one_smul, liftToFull_act,
      act_ctrl0XCirc]
    congr 2
    have hback : (fun i : Fin r => if d then c'' i else xor (c'' i) (natToBitsLSB r c_step.1 i)) = c := by
      cases hd : d
      · funext i; simp [c'', hd, pat]
      · funext i; simp [c'', hd]
    rw [hback]
    rfl

end StepAndWalk

section WalkCorrectnessAndComplexity

variable {ps : PrimitiveSuite} {r n : ℕ}

local notation "ℓ" => Nat.clog 2 (n + 1)
local notation "Amax" => ancMax ps r n
local notation "M'" => regM' ps r n

private def qubitsConsEquiv (M : ℕ) : Qubits (M + 1) ≃ Bool × Qubits M where
  toFun z := (z 0, Fin.tail z)
  invFun p := Fin.cons (α := fun _ => Bool) p.1 p.2
  left_inv z := Fin.cons_self_tail z
  right_inv p := by ext <;> simp

private lemma controlled_mem_unitaryGroup {κ : Type*} [Fintype κ] [DecidableEq κ]
    {U : Matrix κ κ ℂ} (hU : U ∈ Matrix.unitaryGroup κ ℂ) :
    controlled U ∈ Matrix.unitaryGroup (Bool × κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hU_mul : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  ext ⟨b₁, x₁⟩ ⟨b₂, x₂⟩
  simp only [controlled, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  by_cases hb : b₁ = b₂
  · subst hb
    rw [Finset.sum_eq_single b₁]
    · cases b₁
      · simp
      · have h := congrFun (congrFun hU_mul x₁) x₂
        simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
    · intro b' _ hb'; simp [hb'.symm]
    · simp
  · simp only [Prod.mk.injEq, hb, false_and, ↓reduceIte]
    refine Finset.sum_eq_zero fun b' _ => Finset.sum_eq_zero fun x' _ => ?_
    by_cases h1 : b₁ = b'
    · subst h1; simp [Ne.symm hb]
    · simp [h1]

private lemma controlledQubits_mem_unitaryGroup {m : ℕ}
    {U : Matrix (Qubits m) (Qubits m) ℂ} (hU : U ∈ Matrix.unitaryGroup (Qubits m) ℂ) :
    controlledQubits U ∈ Matrix.unitaryGroup (Qubits (m + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hc := Matrix.mem_unitaryGroup_iff.mp (controlled_mem_unitaryGroup hU)
  let e := qubitsConsEquiv m
  have hstar : star (controlledQubits U) = (star (controlled U)).submatrix e e := by
    ext i j; simp [controlledQubits, e, qubitsConsEquiv, Matrix.star_apply]
  have hmul : controlledQubits U * (star (controlled U)).submatrix e e =
      (controlled U * star (controlled U)).submatrix e e := by
    ext i j
    simp only [controlledQubits, Matrix.mul_apply, Matrix.submatrix_apply, e]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hstar, hmul, hc]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [e]
  · have he : e i ≠ e j := fun h => hij (e.injective h)
    simp [Matrix.submatrix_apply, hij, he]

private lemma majOracle_mem_unitaryGroup {n : ℕ} (A : Finset (Fin n)) :
    majOracle A ∈ Matrix.unitaryGroup (Qubits (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  let f : Qubits (n + 1) → Qubits (n + 1) := fun z =>
    Fin.snoc (α := fun _ => Bool) (Fin.init z)
      (xor (z (Fin.last n)) (decide (majJunta A (Finset.univ.filter fun i => Fin.init z i = true) = -1)))
  have hf_invol : ∀ z, f (f z) = z := fun z => by
    have hinit : Fin.init (f z) = Fin.init z := Fin.init_snoc _ _
    dsimp only [f]
    rw [hinit, Fin.snoc_last, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Fin.snoc_init_self]
  ext y z
  simp only [Matrix.mul_apply, Matrix.star_apply, majOracle, Matrix.of_apply, Matrix.one_apply]
  change ∑ x : Qubits (n + 1), (if y = f x then (1 : ℂ) else 0) * star (if z = f x then (1 : ℂ) else 0) = _
  have hx_uniq : ∀ x : Qubits (n + 1), y = f x ↔ x = f y := fun x => by
    constructor
    · intro h; rw [h, hf_invol]
    · intro h; rw [h, hf_invol]
  rw [Finset.sum_eq_single (f y)]
  · simp only [hf_invol, ↓reduceIte, one_mul]
    by_cases hyz : y = z
    · subst hyz; simp
    · simp [hyz, Ne.symm hyz]
  · intro x _ hx
    have hne : y ≠ f x := fun h => hx ((hx_uniq x).mp h)
    simp [hne]
  · simp

private lemma oracleStep_mem_unitaryGroup {S : Set Gate} {a : Fin 1 → ℕ} {M : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary)
    (orc : (k : Fin 1) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (horc : ∀ k, orc k ∈ Matrix.unitaryGroup (Qubits (a k)) ℂ)
    (st : OracleStep S a M) :
    OracleStep.mat orc st ∈ Matrix.unitaryGroup (Qubits M) ℂ := by
  cases st with
  | gate g => exact embedOp_mem_unitaryGroup (hS g.gate g.mem) g.wires
  | query k adj ctl wires hc =>
    have hU : (if adj then star (orc k) else orc k) ∈ Matrix.unitaryGroup (Qubits (a k)) ℂ := by
      cases adj
      · exact horc k
      · exact Matrix.mem_unitaryGroup_iff.mpr (by simpa using Matrix.mem_unitaryGroup_iff'.mp (horc k))
    cases ctl with
    | none => exact embedOp_mem_unitaryGroup hU wires
    | some c => exact embedOp_mem_unitaryGroup (controlledQubits_mem_unitaryGroup hU) _

private lemma oracleCircuit_mem_unitaryGroup {S : Set Gate} {a : Fin 1 → ℕ} {M : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary)
    (orc : (k : Fin 1) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (horc : ∀ k, orc k ∈ Matrix.unitaryGroup (Qubits (a k)) ℂ)
    (c : OracleCircuit S a M) :
    c.unitary orc ∈ Matrix.unitaryGroup (Qubits M) ℂ := by
  unfold OracleCircuit.unitary
  induction c with
  | nil => simp
  | cons st rest ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one] at ih ⊢
    exact Submonoid.mul_mem _ ih (oracleStep_mem_unitaryGroup hS orc horc st)

private lemma probEvent_ge_of_norm_sub_sq {α : Type*} [Fintype α] [DecidableEq α]
    (finalVec idealVec : EuclideanSpace ℂ α) (P : α → Prop) [DecidablePred P]
    (hnorm : ‖finalVec‖ = 1)
    (hsupp : ∀ x, ¬ P x → idealVec x = 0)
    {ε : ℝ}
    (hdist : ‖finalVec - idealVec‖ ^ 2 ≤ ε) :
    probEvent finalVec P ≥ 1 - ε := by
  have h1 : ‖finalVec‖ ^ 2 = probEvent finalVec P +
      ∑ x ∈ Finset.univ.filter (fun x => ¬ P x), ‖finalVec x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ P (fun x => ‖finalVec x‖ ^ 2)).symm
    rw [hsplit]
    congr 1
    simp only [probEvent, prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul]
  have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ P x), ‖finalVec x‖ ^ 2 ≤
      ‖finalVec - idealVec‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hrewrite : ∑ x ∈ Finset.univ.filter (fun x => ¬ P x), ‖finalVec x‖ ^ 2 =
        ∑ x ∈ Finset.univ.filter (fun x => ¬ P x), ‖(finalVec - idealVec) x‖ ^ 2 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp [hsupp x hx]
    rw [hrewrite]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  rw [hnorm, one_pow] at h1
  linarith

noncomputable def ψStart (ps : PrimitiveSuite) (r n : ℕ) : EuclideanSpace ℂ (Qubits (regM' ps r n)) :=
  (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
    ∑ c : Fin (2 ^ r), ket (coreEmbHom (natToBitsLSB r c.1, false, fun _ => false))

noncomputable def ψCat (ps : PrimitiveSuite) (r n m : ℕ) (A : Finset (Fin n))
    (hA : A.card = 2 * m + 1) : EuclideanSpace ℂ (Qubits (regM' ps r n)) :=
  (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
    ∑ S : Qubits n, (wCatVec n m A hA S) • ket (coreEmbHom (fun _ => false, true, S))

noncomputable def ψTarget (ps : PrimitiveSuite) (r n : ℕ) (A : Finset (Fin n)) :
    EuclideanSpace ℂ (Qubits (regM' ps r n)) :=
  (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
    ∑ c : Fin (2 ^ r), ket (coreEmbHom (natToBitsLSB r c.1, false, fun i => decide (i ∈ A)))

noncomputable def ψIdeal (ps : PrimitiveSuite) (r n m : ℕ) (A : Finset (Fin n))
    (hA : A.card = 2 * m + 1) (t : ℕ) : EuclideanSpace ℂ (Qubits (regM' ps r n)) :=
  (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
    ((∑ c : Fin (2 ^ r), ket (coreEmbHom (natToBitsLSB r c.1, false,
        if c.1 < t then (fun i => decide (i ∈ A)) else (fun _ => false)))) +
      ∑ S : Qubits n, (wCatVec n m A hA S) • ket (coreEmbHom (fun _ => false, true, S)))

lemma ψIdeal_zero (m : ℕ) (A : Finset (Fin n)) (hA : A.card = 2 * m + 1) :
    ψIdeal ps r n m A hA 0 = ψStart ps r n + ψCat ps r n m A hA := by
  simp [ψIdeal, ψStart, ψCat, smul_add]

lemma ψIdeal_top (m : ℕ) (A : Finset (Fin n)) (hA : A.card = 2 * m + 1) :
    ψIdeal ps r n m A hA (2 ^ r) = ψTarget ps r n A + ψCat ps r n m A hA := by
  have hsum : ∑ c : Fin (2 ^ r), ket (coreEmbHom (ps := ps) (r := r) (n := n)
        (natToBitsLSB r c.1, false, if c.1 < 2 ^ r then (fun i => decide (i ∈ A)) else (fun _ => false))) =
      ∑ c : Fin (2 ^ r), ket (coreEmbHom (ps := ps) (r := r) (n := n)
        (natToBitsLSB r c.1, false, fun i => decide (i ∈ A))) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [if_pos c.isLt]
  simp only [ψIdeal, hsum, ψTarget, ψCat, smul_add]

lemma norm_sq_ψCat (m : ℕ) (A : Finset (Fin n)) (hA : A.card = 2 * m + 1) :
    ‖ψCat ps r n m A hA‖ ^ 2 = ‖wCatVec n m A hA‖ ^ 2 / (2 ^ r : ℕ) := by
  have hnorm_sum : ‖∑ S : Qubits n, (wCatVec n m A hA S) •
        ket (coreEmbHom (ps := ps) (r := r) (n := n) (fun _ => false, true, S))‖ ^ 2 =
      ‖wCatVec n m A hA‖ ^ 2 := by
    let f : Qubits n → Qubits M' := fun S =>
      coreEmbHom (ps := ps) (r := r) (n := n) (fun _ => false, true, S)
    have hf_inj : Function.Injective f := fun S₁ S₂ h => by
      have h' := coreEmbHom.injective h
      exact (Prod.ext_iff.mp (Prod.ext_iff.mp h').2).2
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have hzero : ∀ y : Qubits M', y ∉ Finset.univ.image f →
        ‖(∑ S : Qubits n, (wCatVec n m A hA S) • ket (f S)) y‖ ^ 2 = 0 := by
      intro y hy
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hy
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hs0 : (∑ S : Qubits n, (wCatVec n m A hA S) * ket (f S) y) = 0 := by
        refine Finset.sum_eq_zero fun S _ => ?_
        have hne : y ≠ f S := Ne.symm (hy S)
        simp [ket, hne]
      rw [hs0, norm_zero, zero_pow (by norm_num)]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) (fun y _ hy => hzero y hy)]
    rw [Finset.sum_image (fun S₁ _ S₂ _ h => hf_inj h)]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single S]
    · simp [ket]
    · intro S' _ hS'
      have hne : f S ≠ f S' := fun h => hS' (hf_inj h.symm)
      simp [ket, hne]
    · simp
  have h2pos : (0 : ℝ) < (2 ^ r : ℕ) := by positivity
  simp only [ψCat, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    mul_pow, inv_pow, Real.sq_sqrt h2pos.le]
  rw [hnorm_sum]
  ring

private lemma withMinus_add {M : ℕ} (φ₁ φ₂ : EuclideanSpace ℂ (Qubits M)) :
    withMinus (φ₁ + φ₂) = withMinus φ₁ + withMinus φ₂ := by
  ext z; simp [withMinus, add_mul]

private lemma withMinus_smul {M : ℕ} (c : ℂ) (φ : EuclideanSpace ℂ (Qubits M)) :
    withMinus (c • φ) = c • withMinus φ := by
  ext z; simp [withMinus]; ring

private lemma withMinus_sum {M : ℕ} {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℂ (Qubits M)) :
    withMinus (∑ x ∈ s, f x) = ∑ x ∈ s, withMinus (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext z; simp [withMinus]
  | insert a s ha ih => rw [Finset.sum_insert ha, withMinus_add, ih, Finset.sum_insert ha]

lemma act_stepCirc_ideal {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n)
    (A : Finset (Fin n)) (hA : A.card = 2 * m + 1) (t : ℕ) (ht : t < 2 ^ r) :
    act ((stepCirc (ps := ps) (r := r) (n := n) hm hle ⟨t, ht⟩).unitary fun _ => majOracle A)
        (withMinus (ψIdeal ps r n m A hA t)) =
      withMinus (ψIdeal ps r n m A hA (t + 1)) := by
  let c_step : Fin (2 ^ r) := ⟨t, ht⟩
  let pat := natToBitsLSB r t
  let indA : Qubits n := fun i => decide (i ∈ A)
  let stepU := (stepCirc (ps := ps) (r := r) (n := n) hm hle c_step).unitary fun _ => majOracle A
  -- Action on each non-matching clock slot c ≠ c_step
  have hother : ∀ c : Fin (2 ^ r), c ≠ c_step →
      act stepU (withMinus (ket (coreEmbHom (ps := ps) (r := r) (n := n)
        (natToBitsLSB r c.1, false, if c.1 < t then indA else fun _ => false)))) =
      withMinus (ket (coreEmbHom (ps := ps) (r := r) (n := n)
        (natToBitsLSB r c.1, false, if c.1 < t then indA else fun _ => false))) := by
    intro c hc
    dsimp only [stepU]
    rw [act_stepCirc_basis hm hle c_step]
    have hne : (fun i : Fin r => xor (natToBitsLSB r c.1 i) (pat i)) ≠ (fun _ => false) := by
      intro heq
      apply hc
      apply Fin.ext
      apply natToBitsLSB_inj_of_lt c.isLt ht
      funext i
      have hi := congrFun heq i
      dsimp only [pat] at hi
      cases h1 : natToBitsLSB r c.1 i <;> cases h2 : natToBitsLSB r t i <;> simp_all
    rw [if_neg (by simpa [c_step, pat] using hne)]
  -- Action on matching slot c_step plus catalyst
  have hslot : act stepU (withMinus (ket (coreEmbHom (ps := ps) (r := r) (n := n)
        (pat, false, fun _ => false)))) =
      withMinus (∑ p' : Bool × Qubits n, (U_ideal n m p' (false, fun _ => false)) •
        ket (coreEmbHom (ps := ps) (r := r) (n := n)
          (if p'.1 then fun _ => false else pat, p'.1, p'.2))) := by
    dsimp only [stepU]
    rw [act_stepCirc_basis hm hle c_step]
    simp [c_step, pat]
  have hcat_term : ∀ S : Qubits n,
      act stepU (withMinus ((wCatVec n m A hA S) •
        ket (coreEmbHom (ps := ps) (r := r) (n := n) (fun _ => false, true, S)))) =
      withMinus ((wCatAfter n m A hA S) •
        ∑ p' : Bool × Qubits n, (U_ideal n m p' (true, S)) •
          ket (coreEmbHom (ps := ps) (r := r) (n := n)
            (if p'.1 then fun _ => false else pat, p'.1, p'.2))) := by
    intro S
    rw [withMinus_smul, act_smul]
    dsimp only [stepU]
    rw [act_stepCirc_basis hm hle c_step]
    simp only [↓reduceIte, Bool.true_and, withMinus_smul]
    have hw_after : (wCatVec n m A hA S) * (if majorityBit A S then (-1 : ℂ) else 1) =
        wCatAfter n m A hA S := by
      have hp := congrFun (congrArg WithLp.ofLp (act_phaseMaj_wCatVec A hA)) S
      simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, phaseMaj,
        Matrix.diagonal_apply] at hp
      rw [Finset.sum_eq_single S] at hp
      · simp only [↓reduceIte] at hp; rw [← hp]; ring
      · intro z _ hz; simp [hz.symm]
      · simp
    rw [← withMinus_smul, ← withMinus_smul, smul_smul, hw_after, withMinus_smul]
  have hcomb :
      act stepU (withMinus (ket (coreEmbHom (ps := ps) (r := r) (n := n) (pat, false, fun _ => false)) +
        ∑ S : Qubits n, (wCatVec n m A hA S) •
          ket (coreEmbHom (ps := ps) (r := r) (n := n) (fun _ => false, true, S)))) =
      withMinus (ket (coreEmbHom (ps := ps) (r := r) (n := n) (pat, false, indA)) +
        ∑ S : Qubits n, (wCatVec n m A hA S) •
          ket (coreEmbHom (ps := ps) (r := r) (n := n) (fun _ => false, true, S))) := by
    rw [withMinus_add, withMinus_sum, act_add, act_sum, hslot]
    simp_rw [hcat_term]
    rw [← withMinus_sum, ← withMinus_add]
    congr 1
    -- Combine into act (U_ideal n m)
    have hcoeff_sum :
        (∑ p' : Bool × Qubits n, (U_ideal n m p' (false, fun _ => false)) •
          ket (coreEmbHom (ps := ps) (r := r) (n := n) (if p'.1 then fun _ => false else pat, p'.1, p'.2))) +
        ∑ S : Qubits n, (wCatAfter n m A hA S) •
          ∑ p' : Bool × Qubits n, (U_ideal n m p' (true, S)) •
            ket (coreEmbHom (ps := ps) (r := r) (n := n) (if p'.1 then fun _ => false else pat, p'.1, p'.2)) =
        ∑ p' : Bool × Qubits n,
          (act (U_ideal n m) (ket (false, fun _ => false) + liftDQ_true (wCatAfter n m A hA))) p' •
            ket (coreEmbHom (ps := ps) (r := r) (n := n) (if p'.1 then fun _ => false else pat, p'.1, p'.2)) := by
      have hswap : (∑ S : Qubits n, (wCatAfter n m A hA S) •
            ∑ p' : Bool × Qubits n, (U_ideal n m p' (true, S)) •
              ket (coreEmbHom (ps := ps) (r := r) (n := n) (if p'.1 then fun _ => false else pat, p'.1, p'.2))) =
          ∑ p' : Bool × Qubits n, (∑ S : Qubits n, wCatAfter n m A hA S * U_ideal n m p' (true, S)) •
            ket (coreEmbHom (ps := ps) (r := r) (n := n) (if p'.1 then fun _ => false else pat, p'.1, p'.2)) := by
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p' _ => ?_
        rw [← Finset.sum_smul]
      rw [hswap, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [← add_smul]
      congr 1
      simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, WithLp.ofLp_add,
        Pi.add_apply, ket, PiLp.single_apply, liftDQ_true, Fintype.sum_prod_type]
      rw [Fintype.sum_bool, add_comm]
      have hfalse : ∑ x : Qubits n, U_ideal n m p' (false, x) *
          ((if (false, x) = (false, fun _ => false) then (1 : ℂ) else 0) + 0) =
          U_ideal n m p' (false, fun _ => false) := by
        rw [Finset.sum_eq_single (fun _ => false)]
        · simp
        · intro x _ hx; simp [hx]
        · simp
      have htrue : ∑ x : Qubits n, U_ideal n m p' (true, x) *
          ((if (true, x) = (false, fun _ => false) then (1 : ℂ) else 0) + wCatAfter n m A hA x) =
          ∑ S : Qubits n, wCatAfter n m A hA S * U_ideal n m p' (true, S) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [mul_comm]
      simp only [Bool.false_eq_true, ↓reduceIte] at *
      rw [hfalse, htrue]
    rw [hcoeff_sum, U_ideal_transduces hm hle A hA]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    have hf_part : ∑ q' : Qubits n,
        (ket (false, indA) + liftDQ_true (wCatVec n m A hA)) (false, q') •
          ket (coreEmbHom (ps := ps) (r := r) (n := n) (pat, false, q')) =
        ket (coreEmbHom (ps := ps) (r := r) (n := n) (pat, false, indA)) := by
      rw [Finset.sum_eq_single indA]
      · simp [ket, liftDQ_true]
      · intro q' _ hq'; simp [ket, liftDQ_true, hq']
      · simp
    have ht_part : ∑ q' : Qubits n,
        (ket (false, indA) + liftDQ_true (wCatVec n m A hA)) (true, q') •
          ket (coreEmbHom (ps := ps) (r := r) (n := n) (fun _ => false, true, q')) =
        ∑ S : Qubits n, (wCatVec n m A hA S) •
          ket (coreEmbHom (ps := ps) (r := r) (n := n) (fun _ => false, true, S)) := by
      refine Finset.sum_congr rfl fun q' _ => ?_
      simp [ket, liftDQ_true]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hf_part, ht_part]
  -- Reassemble ψIdeal (t) and ψIdeal (t + 1)
  have hsplit_t : ψIdeal ps r n m A hA t =
      (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
        ((∑ c ∈ Finset.univ.erase c_step, ket (coreEmbHom (ps := ps) (r := r) (n := n)
            (natToBitsLSB r c.1, false, if c.1 < t then indA else fun _ => false))) +
         (ket (coreEmbHom (ps := ps) (r := r) (n := n) (pat, false, fun _ => false)) +
          ∑ S : Qubits n, (wCatVec n m A hA S) •
            ket (coreEmbHom (ps := ps) (r := r) (n := n) (fun _ => false, true, S)))) := by
    unfold ψIdeal
    congr 1
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c_step)]
    have hltf : ¬ (c_step.1 < t) := by dsimp [c_step]; omega
    simp only [hltf, ↓reduceIte]
    abel
  have hsplit_succ : ψIdeal ps r n m A hA (t + 1) =
      (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
        ((∑ c ∈ Finset.univ.erase c_step, ket (coreEmbHom (ps := ps) (r := r) (n := n)
            (natToBitsLSB r c.1, false, if c.1 < t then indA else fun _ => false))) +
         (ket (coreEmbHom (ps := ps) (r := r) (n := n) (pat, false, indA)) +
          ∑ S : Qubits n, (wCatVec n m A hA S) •
            ket (coreEmbHom (ps := ps) (r := r) (n := n) (fun _ => false, true, S)))) := by
    unfold ψIdeal
    congr 1
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c_step)]
    have hlt_succ : c_step.1 < t + 1 := by dsimp [c_step]; omega
    have hrest : ∑ c ∈ Finset.univ.erase c_step,
          ket (coreEmbHom (ps := ps) (r := r) (n := n)
            (natToBitsLSB r c.1, false, if c.1 < t + 1 then indA else fun _ => false)) =
        ∑ c ∈ Finset.univ.erase c_step,
          ket (coreEmbHom (ps := ps) (r := r) (n := n)
            (natToBitsLSB r c.1, false, if c.1 < t then indA else fun _ => false)) := by
      refine Finset.sum_congr rfl fun c hc => ?_
      have hne : c.1 ≠ t := fun h => (Finset.mem_erase.mp hc).1 (Fin.ext h)
      have hiff : c.1 < t + 1 ↔ c.1 < t := by omega
      simp [hiff]
    rw [if_pos hlt_succ, hrest]
    abel
  rw [hsplit_t, withMinus_smul, act_smul, withMinus_add, act_add, withMinus_sum, act_sum]
  have hother_sum : ∑ c ∈ Finset.univ.erase c_step,
        act stepU (withMinus (ket (coreEmbHom (ps := ps) (r := r) (n := n)
          (natToBitsLSB r c.1, false, if c.1 < t then indA else fun _ => false)))) =
      ∑ c ∈ Finset.univ.erase c_step,
        withMinus (ket (coreEmbHom (ps := ps) (r := r) (n := n)
          (natToBitsLSB r c.1, false, if c.1 < t then indA else fun _ => false))) :=
    Finset.sum_congr rfl fun c hc => hother c (Finset.mem_erase.mp hc).1
  rw [hother_sum, hcomb, ← withMinus_sum, ← withMinus_add, ← withMinus_smul, ← hsplit_succ]

noncomputable def loopPrefix (ps : PrimitiveSuite) (r n m : ℕ) (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n) :
    (t : ℕ) → t ≤ 2 ^ r → OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (regM' ps r n + 1)
  | 0, _ => []
  | t + 1, ht => loopPrefix ps r n m hm hle t (Nat.le_of_lt ht) ++ stepCirc hm hle ⟨t, ht⟩

lemma loopPrefix_queryCount {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n) :
    ∀ (t : ℕ) (ht : t ≤ 2 ^ r),
      (loopPrefix ps r n m hm hle t ht).queryCount 0 = t := by
  intro t
  induction t with
  | zero => intro _; simp [loopPrefix, OracleCircuit.queryCount]
  | succ t ih =>
    intro ht
    simp only [loopPrefix, oracleCircuit_queryCount_append, ih (Nat.le_of_lt ht)]
    have hq_single : OracleCircuit.queryCount ([queryStepFull (ps := ps) (r := r) (n := n)] :
        OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (M' + 1)) 0 = 1 := by
      simp [OracleCircuit.queryCount, OracleStep.IsQueryTo, queryStepFull]
    have hq_step : (stepCirc (ps := ps) (r := r) (n := n) hm hle ⟨t, ht⟩).queryCount 0 = 1 := by
      rw [stepCirc]
      simp only [oracleCircuit_queryCount_append, liftToFull_queryCount, hq_single]
    omega

noncomputable def fullCirc (ps : PrimitiveSuite) (r n m : ℕ) (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n) :
    OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (regM' ps r n + 1) :=
  [prepareMinusStep (n := n) (regM' ps r n)] ++
  liftToFull (ps := ps) (r := r) (n := n) (hadamardLayerC (ps := ps) (r := r) (n := n)) ++
  loopPrefix ps r n m hm hle (2 ^ r) le_rfl

lemma fullCirc_correct (_hr : 1 ≤ r) (m : ℕ) (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n)
    (A : Finset (Fin n)) (hA : A.card = 2 * m + 1)
    {ε : ℝ} (hK : 4 * ‖wCatVec n m A hA‖ ^ 2 / (2 ^ r : ℕ) ≤ ε) :
    open Classical in
    probEvent (act ((fullCirc ps r n m hm hle).unitary fun _ => majOracle A) (zeroKet (regM' ps r n + 1)))
      (fun z => ∀ i : Fin n, z (regQ.trans (Fin.castAddEmb 1) i) = decide (i ∈ A)) ≥ 1 - ε := by
  let Uloop := (loopPrefix ps r n m hm hle (2 ^ r) le_rfl).unitary fun _ => majOracle A
  have hloop_ideal : ∀ (t : ℕ) (ht : t ≤ 2 ^ r),
      act ((loopPrefix ps r n m hm hle t ht).unitary fun _ => majOracle A)
        (withMinus (ψIdeal ps r n m A hA 0)) =
      withMinus (ψIdeal ps r n m A hA t) := by
    intro t
    induction t with
    | zero => intro _; simp [loopPrefix, OracleCircuit.unitary, act_one_vec]
    | succ t ih =>
      intro ht
      simp only [loopPrefix, oracleCircuit_unitary_append, act_mul]
      rw [ih (Nat.le_of_lt ht), act_stepCirc_ideal hm hle A hA t ht]
  have hloop_full := hloop_ideal (2 ^ r) le_rfl
  rw [ψIdeal_zero, ψIdeal_top] at hloop_full
  have hU_mem : Uloop ∈ Matrix.unitaryGroup (Qubits (M' + 1)) ℂ :=
    oracleCircuit_mem_unitaryGroup (fun _ hg => hg.1) _ (fun _ => majOracle_mem_unitaryGroup A) _
  have hstart_prep :
      act (OracleCircuit.unitary ([prepareMinusStep (n := n) M'] ++
          liftToFull (ps := ps) (r := r) (n := n) hadamardLayerC) fun _ => majOracle A)
        (zeroKet (M' + 1)) =
      withMinus (ψStart ps r n) := by
    rw [oracleCircuit_unitary_append, act_mul]
    have hp : act (OracleCircuit.unitary [prepareMinusStep (n := n) M'] fun _ => majOracle A)
        (zeroKet (M' + 1)) = withMinus (zeroKet M') := by
      simp [OracleCircuit.unitary, act_prepareMinusStep]
    rw [hp, liftToFull_act, act_hadamardLayerC]
    rfl
  have hfinal_eq :
      act ((fullCirc ps r n m hm hle).unitary fun _ => majOracle A) (zeroKet (M' + 1)) =
      act Uloop (withMinus (ψStart ps r n)) := by
    rw [oracleCircuit_unitary_append, act_mul] at hstart_prep
    simp only [fullCirc, oracleCircuit_unitary_append, act_mul, hstart_prep]
    rfl
  have hnorm_final : ‖act ((fullCirc ps r n m hm hle).unitary fun _ => majOracle A) (zeroKet (M' + 1))‖ = 1 := by
    have hfull_mem : (fullCirc ps r n m hm hle).unitary (fun _ => majOracle A) ∈
        Matrix.unitaryGroup (Qubits (M' + 1)) ℂ :=
      oracleCircuit_mem_unitaryGroup (fun _ hg => hg.1) _ (fun _ => majOracle_mem_unitaryGroup A) _
    rw [act_norm_of_mem_unitaryGroup hfull_mem]
    simp [zeroKet, ket]
  have hsub : act Uloop (withMinus (ψStart ps r n)) - withMinus (ψTarget ps r n A) =
      withMinus (ψCat ps r n m A hA) - act Uloop (withMinus (ψCat ps r n m A hA)) := by
    have h1 : act Uloop (withMinus (ψStart ps r n)) =
        act Uloop (withMinus (ψStart ps r n) + withMinus (ψCat ps r n m A hA)) -
          act Uloop (withMinus (ψCat ps r n m A hA)) := by
      rw [act_add]; abel
    rw [h1, ← withMinus_add, hloop_full, withMinus_add]
    abel
  have hdist_sq :
      ‖act ((fullCirc ps r n m hm hle).unitary fun _ => majOracle A) (zeroKet (M' + 1)) -
        withMinus (ψTarget ps r n A)‖ ^ 2 ≤ ε := by
    rw [hfinal_eq, hsub]
    have htri : ‖withMinus (ψCat ps r n m A hA) - act Uloop (withMinus (ψCat ps r n m A hA))‖ ≤
        2 * ‖ψCat ps r n m A hA‖ := by
      calc ‖withMinus (ψCat ps r n m A hA) - act Uloop (withMinus (ψCat ps r n m A hA))‖
          ≤ ‖withMinus (ψCat ps r n m A hA)‖ + ‖act Uloop (withMinus (ψCat ps r n m A hA))‖ :=
            norm_sub_le _ _
        _ = ‖ψCat ps r n m A hA‖ + ‖ψCat ps r n m A hA‖ := by
            rw [act_norm_of_mem_unitaryGroup hU_mem, withMinus_norm]
        _ = 2 * ‖ψCat ps r n m A hA‖ := (two_mul _).symm
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, norm_sq_ψCat, mul_div_assoc'] at hsq
    linarith
  have hsupp : ∀ z : Qubits (M' + 1),
      ¬ (∀ i : Fin n, z (regQ.trans (Fin.castAddEmb 1) i) = decide (i ∈ A)) →
      withMinus (ψTarget ps r n A) z = 0 := by
    intro z hz
    simp only [withMinus, ψTarget, WithLp.ofLp_toLp, WithLp.ofLp_smul, WithLp.ofLp_sum,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    have hsum0 : (∑ c : Fin (2 ^ r),
        ket (coreEmbHom (ps := ps) (r := r) (n := n)
          (natToBitsLSB r c.1, false, fun i => decide (i ∈ A))) (Fin.init z)) = 0 := by
      refine Finset.sum_eq_zero fun c _ => ?_
      simp only [ket, PiLp.single_apply]
      split_ifs with heq
      · exfalso; apply hz; intro i
        have hi' := congrFun heq (regQ i)
        rw [coreEmbHom_apply, coreEmb, packState_Q] at hi'
        have heq_wire : ((regQ (ps := ps) (r := r) (n := n)).trans (Fin.castAddEmb 1)) i =
            (regQ (ps := ps) (r := r) (n := n) i).castSucc :=
          Fin.ext (by simp [Fin.castAddEmb])
        rw [heq_wire]
        exact hi'
      · rfl
    rw [hsum0, mul_zero, zero_mul]
  exact probEvent_ge_of_norm_sub_sq _ _ _ hnorm_final hsupp hdist_sq

lemma fullCirc_queryCount {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n) :
    (fullCirc ps r n m hm hle).queryCount 0 = 2 ^ r := by
  have hprep : OracleCircuit.queryCount ([prepareMinusStep (n := n) M'] :
      OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (M' + 1)) 0 = 0 := by
    simp [OracleCircuit.queryCount, OracleStep.IsQueryTo, prepareMinusStep]
  simp only [fullCirc, oracleCircuit_queryCount_append,
    hprep, liftToFull_queryCount, loopPrefix_queryCount hm hle (2 ^ r) le_rfl]
  omega

private lemma nat_clog2_le (x : ℕ) : Nat.clog 2 x ≤ x := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases hx : x ≤ 1
    · interval_cases x <;> simp
    · have hdiv : (x + 1) / 2 < x := by omega
      have hc : Nat.clog 2 x = Nat.clog 2 ((x + 1) / 2) + 1 := by
        have hsub : (x + 2 - 1) / 2 = (x + 1) / 2 := by omega
        rw [Nat.clog_of_one_lt (by norm_num) (by omega : 1 < x), hsub]
      rw [hc]
      have := ih ((x + 1) / 2) hdiv
      omega

private lemma stepCirc_gateCount_le {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n)
    (hn2 : 2 ≤ n) (c_step : Fin (2 ^ r)) :
    ((stepCirc (ps := ps) (r := r) (n := n) hm hle c_step).gateCount : ℝ) ≤
      2 * r + 4 * ps.C_eq * (r + 2) + 4 * ps.toffoliCirc.length + 2 * ps.C_ch * n +
        2 * ps.C_hc * n * Real.log n + ps.C_eq * (2 * ℓ + 7) := by
  have hn : 1 ≤ n := by omega
  have hℓ : 2 ≤ ℓ := by
    have h4 : 4 ≤ n + 1 := by omega
    by_contra hlt
    have hle1 : ℓ ≤ 1 := by omega
    have hpow := Nat.le_pow_clog (b := 2) (by norm_num) (n + 1)
    have h2 : 2 ^ ℓ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle1
    norm_num at h2
    omega
  have hq : OracleCircuit.gateCount ([queryStepFull (ps := ps) (r := r) (n := n)] :
      OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (M' + 1)) = 0 := by
    simp [OracleCircuit.gateCount, queryStepFull]
  have hgc : (stepCirc (ps := ps) (r := r) (n := n) hm hle c_step).gateCount =
      2 * r +
      2 * (ps.eqCirc (r + 1) (patFQ r) pauliX pauliX_mem_unitaryGroup).length +
      2 * (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup).length +
      4 * ps.toffoliCirc.length +
      2 * (ps.chCirc n).length +
      2 * (ps.hcCirc n).length +
      (ps.eqCirc (1 + ℓ) (patW0 n) pauliX pauliX_mem_unitaryGroup).length +
      (ps.eqCirc 2 patW1 pauliZ pauliZ_mem_unitaryGroup).length +
      (ps.eqCirc (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m)).length := by
    dsimp only [stepCirc, uBodyCirc]
    simp only [oracleCircuit_gateCount_append, liftToFull_gateCount, hq, ctrl0XCirc_length,
      List.length_append, embedCircuit, List.length_map, hHatCirc_length, uTildeCirc_length,
      ps.hcAdj_length]
    ring
  have heq1 := (ps.eq_bound (r + 1) (patFQ r) pauliX pauliX_mem_unitaryGroup).1
  have heq2 := (ps.eq_bound r (fun _ => false) pauliX pauliX_mem_unitaryGroup).1
  have hch := (ps.ch_bound n hn2).1
  have hhc := (ps.hc_bound n hn2).1
  have heqW0 := (ps.eq_bound (1 + ℓ) (patW0 n) pauliX pauliX_mem_unitaryGroup).1
  have heqW1 := (ps.eq_bound 2 patW1 pauliZ pauliZ_mem_unitaryGroup).1
  have heqWk := (ps.eq_bound (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m)).1
  have hCeq : 0 < ps.C_eq := ps.hC_eq_pos
  have heq2_le : ps.C_eq * ((r : ℝ) + 1) ≤ ps.C_eq * ((r : ℝ) + 2) := by
    gcongr; linarith
  have hgcr : ((stepCirc (ps := ps) (r := r) (n := n) hm hle c_step).gateCount : ℝ) =
      2 * (r : ℝ) +
      2 * ((ps.eqCirc (r + 1) (patFQ r) pauliX pauliX_mem_unitaryGroup).length : ℝ) +
      2 * ((ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup).length : ℝ) +
      4 * (ps.toffoliCirc.length : ℝ) +
      2 * ((ps.chCirc n).length : ℝ) +
      2 * ((ps.hcCirc n).length : ℝ) +
      ((ps.eqCirc (1 + ℓ) (patW0 n) pauliX pauliX_mem_unitaryGroup).length : ℝ) +
      ((ps.eqCirc 2 patW1 pauliZ pauliZ_mem_unitaryGroup).length : ℝ) +
      ((ps.eqCirc (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m)).length : ℝ) := by
    exact_mod_cast hgc
  rw [hgcr]
  push_cast at heq1 heq2 heqW0 heqW1 heqWk
  linarith

private lemma loopPrefix_gateCount_le {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n)
    {G : ℝ} (hG : ∀ c_step : Fin (2 ^ r),
      ((stepCirc (ps := ps) (r := r) (n := n) hm hle c_step).gateCount : ℝ) ≤ G) :
    ∀ (t : ℕ) (ht : t ≤ 2 ^ r),
      ((loopPrefix ps r n m hm hle t ht).gateCount : ℝ) ≤ (t : ℝ) * G := by
  intro t
  induction t with
  | zero => intro _; simp [loopPrefix, OracleCircuit.gateCount]
  | succ t ih =>
    intro ht
    simp only [loopPrefix, oracleCircuit_gateCount_append, Nat.cast_add]
    have h1 := ih (Nat.le_of_lt ht)
    have h2 := hG ⟨t, ht⟩
    push_cast
    linarith

private lemma stepCirc_nonOracleDepth_le {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n)
    (hn2 : 2 ≤ n) (c_step : Fin (2 ^ r)) :
    (nonOracleDepth (stepCirc (ps := ps) (r := r) (n := n) hm hle c_step) : ℝ) ≤
      2 * r + 4 * ps.C_eq * (r + 3) + 4 * ps.toffoliDepth +
        2 * (ps.C_ch + ps.C_hc) * Real.log n + ps.C_eq * (2 * ℓ + 9) := by
  have hn : 1 ≤ n := by omega
  have hℓ : 2 ≤ ℓ := by
    have h4 : 4 ≤ n + 1 := by omega
    by_contra hlt
    have hle1 : ℓ ≤ 1 := by omega
    have hpow := Nat.le_pow_clog (b := 2) (by norm_num) (n + 1)
    have h2 : 2 ^ ℓ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle1
    norm_num at h2
    omega
  let a1 : Fin 1 → ℕ := fun _ => n + 1
  have hxc_d : nonOracleDepth (liftToFull (ps := ps) (r := r) (n := n) (ctrl0XCirc (natToBitsLSB r c_step.1))) ≤ r := by
    calc nonOracleDepth (liftToFull (ps := ps) (r := r) (n := n) (ctrl0XCirc (natToBitsLSB r c_step.1)))
        ≤ nonOracleDepth ((ctrl0XCirc (ps := ps) (r := r) (n := n) (natToBitsLSB r c_step.1)).map OracleStep.gate :
            OracleCircuit gates12 a1 M') := liftToFull_depth_le _
      _ ≤ ((ctrl0XCirc (ps := ps) (r := r) (n := n) (natToBitsLSB r c_step.1)).map OracleStep.gate :
            OracleCircuit gates12 a1 M').length := nonOracleDepth_le_length _
      _ = r := by simp [ctrl0XCirc_length]
  have hfq_d : nonOracleDepth (liftToFull (ps := ps) (r := r) (n := n)
      (embedCircuit embEqFQ (ps.eqCirc (r + 1) (patFQ r) pauliX pauliX_mem_unitaryGroup))) ≤ ps.eqDepth (r + 1) := by
    calc nonOracleDepth _ ≤ nonOracleDepth ((embedCircuit embEqFQ _).map OracleStep.gate : OracleCircuit gates12 a1 M') :=
          liftToFull_depth_le _
      _ ≤ nonOracleDepth ((ps.eqCirc (r + 1) (patFQ r) pauliX pauliX_mem_unitaryGroup).map OracleStep.gate :
            OracleCircuit gates12 a1 ((r + 1) + 1 + ps.ancEq (r + 1))) := nonOracleDepth_embedCircuit _ _
      _ ≤ ps.eqDepth (r + 1) := ps.eq_hdepth _ _ _ _ 1 a1
  have hq_d : nonOracleDepth ([queryStepFull (ps := ps) (r := r) (n := n)] :
      OracleCircuit gates12 a1 (M' + 1)) = 0 := by
    exact nonOracleDepth_query_single _ _ _ _ _
  have heqfc_d : nonOracleDepth ((embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
      (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map OracleStep.gate :
      OracleCircuit gates12 a1 M') ≤ ps.eqDepth r :=
    le_trans (nonOracleDepth_embedCircuit _ _) (ps.eq_hdepth _ _ _ _ 1 a1)
  have hhat_d : nonOracleDepth ((hHatCirc (ps := ps) (r := r) (n := n) hn).map OracleStep.gate :
      OracleCircuit gates12 a1 M') ≤ 2 * ps.toffoliDepth + ps.chDepth n := by
    simp only [hHatCirc, List.map_append]
    have h1 := nonOracleDepth_append
      (((embedCircuit (embToffoli (ps := ps) (r := r) (n := n)) ps.toffoliCirc ++
         embedCircuit (embCH (ps := ps) (r := r) (n := n) hn) (ps.chCirc n)).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
      (((embedCircuit (embToffoli (ps := ps) (r := r) (n := n)) ps.toffoliCirc).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
    have h2 := nonOracleDepth_append
      (((embedCircuit (embToffoli (ps := ps) (r := r) (n := n)) ps.toffoliCirc).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
      (((embedCircuit (embCH (ps := ps) (r := r) (n := n) hn) (ps.chCirc n)).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
    have ht_d : nonOracleDepth ((embedCircuit (embToffoli (ps := ps) (r := r) (n := n)) ps.toffoliCirc).map
        OracleStep.gate : OracleCircuit gates12 a1 M') ≤ ps.toffoliDepth :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.toffoli_hdepth 1 a1)
    have hc_d : nonOracleDepth ((embedCircuit (embCH (ps := ps) (r := r) (n := n) hn) (ps.chCirc n)).map
        OracleStep.gate : OracleCircuit gates12 a1 M') ≤ ps.chDepth n :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.ch_hdepth n 1 a1)
    simp only [List.map_append] at h1
    omega
  have hhc_d : nonOracleDepth ((embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcCirc n)).map
      OracleStep.gate : OracleCircuit gates12 a1 M') ≤ ps.hcDepth n :=
    le_trans (nonOracleDepth_embedCircuit _ _) (ps.hc_hdepth n 1 a1).1
  have hhcadj_d : nonOracleDepth ((embedCircuit (embHC (ps := ps) (r := r) (n := n)) (ps.hcAdjCirc n)).map
      OracleStep.gate : OracleCircuit gates12 a1 M') ≤ ps.hcDepth n :=
    le_trans (nonOracleDepth_embedCircuit _ _) (ps.hc_hdepth n 1 a1).2
  have hutilde_d : nonOracleDepth ((uTildeCirc (ps := ps) (r := r) (n := n) m hℓ).map
      OracleStep.gate : OracleCircuit gates12 a1 M') ≤
      2 * ps.eqDepth (1 + ℓ) + ps.eqDepth 2 := by
    simp only [uTildeCirc, List.map_append]
    have h1 := nonOracleDepth_append
      (((embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
          (ps.eqCirc (1 + ℓ) (patW0 n) pauliX pauliX_mem_unitaryGroup) ++
        embedCircuit (embEqWBit1 (ps := ps) (r := r) (n := n) hℓ)
          (ps.eqCirc 2 patW1 pauliZ pauliZ_mem_unitaryGroup)).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
      (((embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
          (ps.eqCirc (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m))).map
        OracleStep.gate) : OracleCircuit gates12 a1 M')
    have h2 := nonOracleDepth_append
      (((embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
          (ps.eqCirc (1 + ℓ) (patW0 n) pauliX pauliX_mem_unitaryGroup)).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
      (((embedCircuit (embEqWBit1 (ps := ps) (r := r) (n := n) hℓ)
          (ps.eqCirc 2 patW1 pauliZ pauliZ_mem_unitaryGroup)).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
    have dw0 : nonOracleDepth ((embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
        (ps.eqCirc (1 + ℓ) (patW0 n) pauliX pauliX_mem_unitaryGroup)).map OracleStep.gate :
        OracleCircuit gates12 a1 M') ≤ ps.eqDepth (1 + ℓ) :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.eq_hdepth _ _ _ _ 1 a1)
    have dw1 : nonOracleDepth ((embedCircuit (embEqWBit1 (ps := ps) (r := r) (n := n) hℓ)
        (ps.eqCirc 2 patW1 pauliZ pauliZ_mem_unitaryGroup)).map OracleStep.gate :
        OracleCircuit gates12 a1 M') ≤ ps.eqDepth 2 :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.eq_hdepth _ _ _ _ 1 a1)
    have dwk : nonOracleDepth ((embedCircuit (embEqWFull (ps := ps) (r := r) (n := n))
        (ps.eqCirc (1 + ℓ) (patWk n (2 * m + 1)) (U_k_adj_Z m) (U_k_adj_Z_mem_unitaryGroup m))).map
        OracleStep.gate : OracleCircuit gates12 a1 M') ≤ ps.eqDepth (1 + ℓ) :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.eq_hdepth _ _ _ _ 1 a1)
    simp only [List.map_append] at h1
    omega
  have hubody_d : nonOracleDepth (liftToFull (ps := ps) (r := r) (n := n) (uBodyCirc hm hle)) ≤
      2 * ps.eqDepth r + 4 * ps.toffoliDepth + 2 * ps.chDepth n + 2 * ps.hcDepth n +
        2 * ps.eqDepth (1 + ℓ) + ps.eqDepth 2 := by
    refine le_trans (liftToFull_depth_le _) ?_
    simp only [uBodyCirc, List.map_append]
    have ha1 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
        hHatCirc hn ++
        embedCircuit embHC (ps.hcCirc n) ++
        uTildeCirc m hℓ ++
        embedCircuit embHC (ps.hcAdjCirc n) ++
        hHatCirc hn).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((embedCircuit embEqFC (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map
        OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha2 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
        hHatCirc hn ++
        embedCircuit embHC (ps.hcCirc n) ++
        uTildeCirc m hℓ ++
        embedCircuit embHC (ps.hcAdjCirc n)).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((hHatCirc hn).map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha3 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
        hHatCirc hn ++
        embedCircuit embHC (ps.hcCirc n) ++
        uTildeCirc m hℓ).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((embedCircuit embHC (ps.hcAdjCirc n)).map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha4 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
        hHatCirc hn ++
        embedCircuit embHC (ps.hcCirc n)).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((uTildeCirc m hℓ).map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha5 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
        hHatCirc hn).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((embedCircuit embHC (ps.hcCirc n)).map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha6 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
      (((hHatCirc hn).map OracleStep.gate) : OracleCircuit gates12 a1 M')
    simp only [List.map_append] at ha1 ha2 ha3 ha4 ha5
    omega
  have hstep_d : nonOracleDepth (stepCirc (ps := ps) (r := r) (n := n) hm hle c_step) ≤
      2 * r + 2 * ps.eqDepth (r + 1) + 2 * ps.eqDepth r + 4 * ps.toffoliDepth +
        2 * ps.chDepth n + 2 * ps.hcDepth n + 2 * ps.eqDepth (1 + ℓ) + ps.eqDepth 2 := by
    let pat := natToBitsLSB r c_step.1
    let xc := liftToFull (ps := ps) (r := r) (n := n) (ctrl0XCirc pat)
    let fq := liftToFull (ps := ps) (r := r) (n := n)
      (embedCircuit embEqFQ (ps.eqCirc (r + 1) (patFQ r) pauliX pauliX_mem_unitaryGroup))
    let ubody := liftToFull (ps := ps) (r := r) (n := n) (uBodyCirc hm hle)
    change nonOracleDepth (xc ++ fq ++ [queryStepFull] ++ fq ++ ubody ++ xc) ≤ _
    have hs1 := nonOracleDepth_append (xc ++ fq ++ [queryStepFull] ++ fq ++ ubody) xc
    have hs2 := nonOracleDepth_append (xc ++ fq ++ [queryStepFull] ++ fq) ubody
    have hs3 := nonOracleDepth_append (xc ++ fq ++ [queryStepFull]) fq
    have hs4 := nonOracleDepth_append (xc ++ fq) [queryStepFull]
    have hs5 := nonOracleDepth_append xc fq
    have hxc' : nonOracleDepth xc ≤ r := hxc_d
    have hfq' : nonOracleDepth fq ≤ ps.eqDepth (r + 1) := hfq_d
    have hub' : nonOracleDepth ubody ≤ 2 * ps.eqDepth r + 4 * ps.toffoliDepth +
        2 * ps.chDepth n + 2 * ps.hcDepth n + 2 * ps.eqDepth (1 + ℓ) + ps.eqDepth 2 := hubody_d
    have hqd' : nonOracleDepth ([queryStepFull (ps := ps) (r := r) (n := n)] :
        OracleCircuit gates12 a1 (M' + 1)) = 0 := hq_d
    omega
  have hstep_r : (nonOracleDepth (stepCirc (ps := ps) (r := r) (n := n) hm hle c_step) : ℝ) ≤
      2 * (r : ℝ) + 2 * (ps.eqDepth (r + 1) : ℝ) + 2 * (ps.eqDepth r : ℝ) +
        4 * (ps.toffoliDepth : ℝ) + 2 * (ps.chDepth n : ℝ) + 2 * (ps.hcDepth n : ℝ) +
        2 * (ps.eqDepth (1 + ℓ) : ℝ) + (ps.eqDepth 2 : ℝ) := by
    exact_mod_cast hstep_d
  have heq1 := (ps.eq_bound (r + 1) (patFQ r) pauliX pauliX_mem_unitaryGroup).2
  have heq2 := (ps.eq_bound r (fun _ => false) pauliX pauliX_mem_unitaryGroup).2
  have hch := (ps.ch_bound n hn2).2
  have hhc := (ps.hc_bound n hn2).2
  have heqW0 := (ps.eq_bound (1 + ℓ) (patW0 n) pauliX pauliX_mem_unitaryGroup).2
  have heqW1 := (ps.eq_bound 2 patW1 pauliZ pauliZ_mem_unitaryGroup).2
  have hclog1 : (Nat.clog 2 ((r + 1) + 1) + 1 : ℕ) ≤ r + 3 := by
    have := nat_clog2_le ((r + 1) + 1); omega
  have hclog2 : (Nat.clog 2 (r + 1) + 1 : ℕ) ≤ r + 3 := by
    have := nat_clog2_le (r + 1); omega
  have hclogW : (Nat.clog 2 ((1 + ℓ) + 1) + 1 : ℕ) ≤ ℓ + 3 := by
    have := nat_clog2_le ((1 + ℓ) + 1); omega
  have hclogW1 : (Nat.clog 2 (2 + 1) + 1 : ℕ) = 3 := by decide
  have hCeq : 0 < ps.C_eq := ps.hC_eq_pos
  have b1 : (ps.eqDepth (r + 1) : ℝ) ≤ ps.C_eq * ((r : ℝ) + 3) := by
    refine le_trans heq1 ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hclog1) hCeq.le
  have b2 : (ps.eqDepth r : ℝ) ≤ ps.C_eq * ((r : ℝ) + 3) := by
    refine le_trans heq2 ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hclog2) hCeq.le
  have bW0 : (ps.eqDepth (1 + ℓ) : ℝ) ≤ ps.C_eq * ((ℓ : ℝ) + 3) := by
    refine le_trans heqW0 ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hclogW) hCeq.le
  have bW1 : (ps.eqDepth 2 : ℝ) ≤ ps.C_eq * 3 := by
    refine le_trans heqW1 ?_
    rw [hclogW1]; norm_num
  linarith

private lemma loopPrefix_nonOracleDepth_le {m : ℕ} (hm : 1 ≤ m) (hle : 2 * m + 1 ≤ n)
    {D : ℝ} (hD : ∀ c_step : Fin (2 ^ r),
      (nonOracleDepth (stepCirc (ps := ps) (r := r) (n := n) hm hle c_step) : ℝ) ≤ D) :
    ∀ (t : ℕ) (ht : t ≤ 2 ^ r),
      (nonOracleDepth (loopPrefix ps r n m hm hle t ht) : ℝ) ≤ (t : ℝ) * D := by
  intro t
  induction t with
  | zero => intro _; simp [loopPrefix, nonOracleDepth]
  | succ t ih =>
    intro ht
    simp only [loopPrefix]
    have hnat : nonOracleDepth (loopPrefix ps r n m hm hle t (Nat.le_of_lt ht) ++
        stepCirc (ps := ps) (r := r) (n := n) hm hle ⟨t, ht⟩) ≤
        nonOracleDepth (loopPrefix ps r n m hm hle t (Nat.le_of_lt ht)) +
        nonOracleDepth (stepCirc (ps := ps) (r := r) (n := n) hm hle ⟨t, ht⟩) :=
      nonOracleDepth_append _ _
    have hcast : (nonOracleDepth (loopPrefix ps r n m hm hle t (Nat.le_of_lt ht) ++
        stepCirc (ps := ps) (r := r) (n := n) hm hle ⟨t, ht⟩) : ℝ) ≤
        (nonOracleDepth (loopPrefix ps r n m hm hle t (Nat.le_of_lt ht)) : ℝ) +
        (nonOracleDepth (stepCirc (ps := ps) (r := r) (n := n) hm hle ⟨t, ht⟩) : ℝ) := by
      exact_mod_cast hnat
    have h1 := ih (Nat.le_of_lt ht)
    have h2 := hD ⟨t, ht⟩
    push_cast
    linarith

theorem theorem_4_9_from_primitives (ps : PrimitiveSuite) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ k n : ℕ, 2 ≤ k → k ≤ n → Odd k →
        ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m) (out : Fin n ↪ Fin m),
          (c.queryCount 0 : ℝ) ≤ C * Real.log k ∧
          (c.gateCount : ℝ) ≤ C * n * Real.log n * Real.log k ∧
          (nonOracleDepth c : ℝ) ≤ C * Real.log n * Real.log k ∧
          ∀ A : Finset (Fin n), A.card = k →
            open Classical in
            probEvent (act (c.unitary fun _ => majOracle A) (zeroKet m))
              (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 1 - ε := by
  intro ε hε0 _
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ := wCatVec_energy_bound
  let C_K : ℝ := 8 * C₀ / ε + 4
  let C_ℓ : ℝ := 1 / Real.log 2 + 1
  let C_step_g : ℝ :=
    2 * C_K + 4 * ps.C_eq * (C_K + 2) + 4 * (ps.toffoliCirc.length : ℝ) +
      2 * ps.C_ch + 2 * ps.C_hc + ps.C_eq * (2 * C_ℓ + 7)
  let C_step_d : ℝ :=
    2 * C_K + 4 * ps.C_eq * (C_K + 3) + 4 * (ps.toffoliDepth : ℝ) +
      2 * (ps.C_ch + ps.C_hc) + ps.C_eq * (2 * C_ℓ + 9)
  let C : ℝ := max C_K (max (C_K * (C_step_g + 1 + C_K)) (C_K * (C_step_d + 2)))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCK_pos : 0 < C_K := by positivity
  have hC_pos : 0 < C := lt_of_lt_of_le hCK_pos (le_max_left _ _)
  refine ⟨C, hC_pos, ?_⟩
  intro k n hk2 hkn hkodd
  have hk3 : 3 ≤ k := by
    rcases hkodd with ⟨j, rfl⟩
    omega
  have hn3 : 3 ≤ n := le_trans hk3 hkn
  have hn2 : 2 ≤ n := by omega
  let m_half : ℕ := (k - 1) / 2
  have hm_ge : 1 ≤ m_half := by dsimp [m_half]; omega
  have hmk : 2 * m_half + 1 = k := by
    rcases hkodd with ⟨j, rfl⟩
    dsimp [m_half]
    omega
  have hle : 2 * m_half + 1 ≤ n := by rw [hmk]; exact hkn
  have hlog3_gt_one : (1 : ℝ) < Real.log 3 := by
    have h3 : Real.exp 1 < (3 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) h3
  have hlogk_ge : (1 : ℝ) ≤ Real.log k :=
    le_trans hlog3_gt_one.le (Real.log_le_log (by norm_num) (by exact_mod_cast hk3))
  have hlogk_le_n : Real.log k ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hkn)
  have hlogn_ge : (1 : ℝ) ≤ Real.log n := le_trans hlogk_ge hlogk_le_n
  have hlogk_nn : 0 ≤ Real.log k := by linarith
  have hlogn_nn : 0 ≤ Real.log n := by linarith
  have hCeq_nn : 0 ≤ ps.C_eq := ps.hC_eq_pos.le
  have hCch_nn : 0 ≤ ps.C_ch := ps.hC_ch_pos.le
  have hChc_nn : 0 ≤ ps.C_hc := ps.hC_hc_pos.le
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  let M_req : ℕ := Nat.ceil (4 * C₀ * Real.log k / ε) + 1
  let r : ℕ := max 1 (Nat.clog 2 M_req)
  have hr1 : 1 ≤ r := le_max_left _ _
  have hM_req_pos : 1 ≤ M_req := by omega
  have hpow_ge_M : M_req ≤ 2 ^ r := by
    have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) M_req
    exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have hpow_ge_real : 4 * C₀ * Real.log k / ε ≤ (2 ^ r : ℕ) := by
    have hceil : 4 * C₀ * Real.log k / ε ≤ (M_req : ℝ) := by
      have h1 : 4 * C₀ * Real.log k / ε ≤ (Nat.ceil (4 * C₀ * Real.log k / ε) : ℝ) :=
        Nat.le_ceil _
      have h2 : (Nat.ceil (4 * C₀ * Real.log k / ε) : ℝ) ≤ (M_req : ℝ) := by
        exact_mod_cast Nat.le_succ _
      exact le_trans h1 h2
    exact le_trans hceil (by exact_mod_cast hpow_ge_M)
  have hpow_le_2M : 2 ^ r ≤ 2 * M_req := by
    by_cases hclog : Nat.clog 2 M_req ≤ 1
    · have hr_eq : r = 1 := by dsimp [r]; omega
      rw [hr_eq]; omega
    · have hclog2 : 2 ≤ Nat.clog 2 M_req := by omega
      have hr_eq : r = Nat.clog 2 M_req := by dsimp [r]; omega
      have hpred_lt : r - 1 < Nat.clog 2 M_req := by omega
      have hpow_lt : 2 ^ (r - 1) < M_req :=
        (Nat.lt_clog_iff_pow_lt (by norm_num)).mp hpred_lt
      calc 2 ^ r = 2 ^ ((r - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (r - 1) := by rw [pow_succ']
        _ ≤ 2 * M_req := by omega
  have hM_req_real : (M_req : ℝ) ≤ (4 * C₀ / ε + 2) * Real.log k := by
    have hnonneg : 0 ≤ 4 * C₀ * Real.log k / ε := by positivity
    have hceil_lt := Nat.ceil_lt_add_one hnonneg
    have hM_lt : (M_req : ℝ) ≤ 4 * C₀ * Real.log k / ε + 2 := by
      have : (M_req : ℝ) = (Nat.ceil (4 * C₀ * Real.log k / ε) : ℝ) + 1 := by
        dsimp [M_req]; push_cast; rfl
      linarith
    have h2 : (2 : ℝ) ≤ 2 * Real.log k := by linarith [hlogk_ge]
    calc (M_req : ℝ) ≤ 4 * C₀ * Real.log k / ε + 2 := hM_lt
      _ ≤ (4 * C₀ / ε) * Real.log k + 2 * Real.log k := by
          have : 4 * C₀ * Real.log k / ε = (4 * C₀ / ε) * Real.log k := by ring
          linarith
      _ = (4 * C₀ / ε + 2) * Real.log k := by ring
  have hK_le : ((2 ^ r : ℕ) : ℝ) ≤ C_K * Real.log k := by
    have h2r : ((2 ^ r : ℕ) : ℝ) ≤ 2 * (M_req : ℝ) := by exact_mod_cast hpow_le_2M
    calc ((2 ^ r : ℕ) : ℝ) ≤ 2 * (M_req : ℝ) := h2r
      _ ≤ 2 * ((4 * C₀ / ε + 2) * Real.log k) := by linarith
      _ = C_K * Real.log k := by dsimp [C_K]; ring
  have hr_le : (r : ℝ) ≤ C_K * Real.log n := by
    have hr_lt : r < 2 ^ r := Nat.lt_two_pow_self
    have hr_real : (r : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast hr_lt.le
    calc (r : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := hr_real
      _ ≤ C_K * Real.log k := hK_le
      _ ≤ C_K * Real.log n := mul_le_mul_of_nonneg_left hlogk_le_n hCK_pos.le
  let ℓval : ℕ := Nat.clog 2 (n + 1)
  have hℓ_le : (ℓval : ℝ) ≤ C_ℓ * Real.log n := by
    by_cases hℓ0 : ℓval = 0
    · rw [hℓ0, Nat.cast_zero]; positivity
    · have hpred_lt : ℓval - 1 < Nat.clog 2 (n + 1) := by omega
      have hpow_lt : 2 ^ (ℓval - 1) < n + 1 :=
        (Nat.lt_clog_iff_pow_lt (by norm_num)).mp hpred_lt
      have hpow_le_n : ((2 ^ (ℓval - 1) : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (by omega : 2 ^ (ℓval - 1) ≤ n)
      have hpos2 : (0 : ℝ) < ((2 ^ (ℓval - 1) : ℕ) : ℝ) := by positivity
      have hlog_pow : ((ℓval - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
        calc ((ℓval - 1 : ℕ) : ℝ) * Real.log 2
            = Real.log ((2 : ℝ) ^ (ℓval - 1)) := (Real.log_pow 2 (ℓval - 1)).symm
          _ = Real.log (((2 ^ (ℓval - 1) : ℕ) : ℝ)) := by norm_cast
          _ ≤ Real.log n := Real.log_le_log hpos2 hpow_le_n
      have hdiv : ((ℓval - 1 : ℕ) : ℝ) ≤ Real.log n / Real.log 2 :=
        (le_div_iff₀ hlog2_pos).mpr hlog_pow
      have hcast : (ℓval : ℝ) = ((ℓval - 1 : ℕ) : ℝ) + 1 := by
        have h1 : 1 ≤ ℓval := Nat.one_le_iff_ne_zero.mpr hℓ0
        have : (ℓval : ℝ) = ((ℓval - 1 + 1 : ℕ) : ℝ) := by congr 1; omega
        rw [this]; push_cast; rfl
      rw [hcast]
      calc ((ℓval - 1 : ℕ) : ℝ) + 1 ≤ Real.log n / Real.log 2 + 1 := by linarith
        _ ≤ Real.log n / Real.log 2 + Real.log n := by linarith
        _ = C_ℓ * Real.log n := by dsimp [C_ℓ]; ring
  let M_tot : ℕ := regM' ps r n + 1
  let c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) M_tot := fullCirc ps r n m_half hm_ge hle
  let out : Fin n ↪ Fin M_tot := (regQ (ps := ps) (r := r) (n := n)).trans (Fin.castAddEmb 1)
  refine ⟨M_tot, c, out, ?_, ?_, ?_, ?_⟩
  · -- queryCount
    rw [show (c.queryCount 0 : ℝ) = ((2 ^ r : ℕ) : ℝ) by
      exact_mod_cast fullCirc_queryCount (ps := ps) (r := r) (n := n) hm_ge hle]
    calc ((2 ^ r : ℕ) : ℝ) ≤ C_K * Real.log k := hK_le
      _ ≤ C * Real.log k := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- gateCount
    have hstep_g : ∀ c_step : Fin (2 ^ r),
        ((stepCirc (ps := ps) (r := r) (n := n) hm_ge hle c_step).gateCount : ℝ) ≤
          C_step_g * n * Real.log n := by
      intro c_step
      have hs := stepCirc_gateCount_le (ps := ps) (r := r) (n := n) hm_ge hle hn2 c_step
      have hCeq_pos : 0 ≤ ps.C_eq := ps.hC_eq_pos.le
      have hCch_pos : 0 ≤ ps.C_ch := ps.hC_ch_pos.le
      have h1 : 2 * (r : ℝ) ≤ 2 * C_K * Real.log n := by linarith
      have h2 : 4 * ps.C_eq * ((r : ℝ) + 2) ≤ 4 * ps.C_eq * (C_K + 2) * Real.log n := by
        have h2a : (r : ℝ) + 2 ≤ (C_K + 2) * Real.log n := by linarith [hr_le, hlogn_ge]
        calc 4 * ps.C_eq * ((r : ℝ) + 2) ≤ 4 * ps.C_eq * ((C_K + 2) * Real.log n) :=
              mul_le_mul_of_nonneg_left h2a (by linarith)
          _ = 4 * ps.C_eq * (C_K + 2) * Real.log n := by ring
      have h3 : 4 * (ps.toffoliCirc.length : ℝ) ≤ 4 * (ps.toffoliCirc.length : ℝ) * n * Real.log n := by
        have hnl : 1 ≤ (n : ℝ) * Real.log n := by
          calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
            _ ≤ (n : ℝ) * Real.log n := mul_le_mul hn_ge1 hlogn_ge (by norm_num) (by linarith)
        calc 4 * (ps.toffoliCirc.length : ℝ) = (4 * (ps.toffoliCirc.length : ℝ)) * 1 := (mul_one _).symm
          _ ≤ (4 * (ps.toffoliCirc.length : ℝ)) * ((n : ℝ) * Real.log n) :=
              mul_le_mul_of_nonneg_left hnl (by positivity)
          _ = 4 * (ps.toffoliCirc.length : ℝ) * n * Real.log n := by ring
      have h4 : 2 * ps.C_ch * (n : ℝ) ≤ 2 * ps.C_ch * (n : ℝ) * Real.log n := by
        calc 2 * ps.C_ch * (n : ℝ) = (2 * ps.C_ch * (n : ℝ)) * 1 := (mul_one _).symm
          _ ≤ (2 * ps.C_ch * (n : ℝ)) * Real.log n :=
              mul_le_mul_of_nonneg_left hlogn_ge (by positivity)
          _ = 2 * ps.C_ch * (n : ℝ) * Real.log n := by ring
      have h5 : ps.C_eq * (2 * (ℓval : ℝ) + 7) ≤ ps.C_eq * (2 * C_ℓ + 7) * Real.log n := by
        have h5a : 2 * (ℓval : ℝ) + 7 ≤ (2 * C_ℓ + 7) * Real.log n := by linarith [hℓ_le, hlogn_ge]
        calc ps.C_eq * (2 * (ℓval : ℝ) + 7) ≤ ps.C_eq * ((2 * C_ℓ + 7) * Real.log n) :=
              mul_le_mul_of_nonneg_left h5a hCeq_pos
          _ = ps.C_eq * (2 * C_ℓ + 7) * Real.log n := by ring
      have hrl_to_nrl : ∀ a : ℝ, 0 ≤ a → a * Real.log n ≤ a * (n : ℝ) * Real.log n := fun a ha => by
        have : 0 ≤ a * Real.log n := by positivity
        calc a * Real.log n = (a * Real.log n) * 1 := (mul_one _).symm
          _ ≤ (a * Real.log n) * (n : ℝ) := mul_le_mul_of_nonneg_left hn_ge1 this
          _ = a * (n : ℝ) * Real.log n := by ring
      have ha1 := hrl_to_nrl (2 * C_K) (by positivity)
      have ha2 := hrl_to_nrl (4 * ps.C_eq * (C_K + 2)) (by positivity)
      have ha5 := hrl_to_nrl (ps.C_eq * (2 * C_ℓ + 7)) (by positivity)
      calc ((stepCirc (ps := ps) (r := r) (n := n) hm_ge hle c_step).gateCount : ℝ)
          ≤ 2 * (r : ℝ) + 4 * ps.C_eq * ((r : ℝ) + 2) + 4 * (ps.toffoliCirc.length : ℝ) +
              2 * ps.C_ch * (n : ℝ) + 2 * ps.C_hc * (n : ℝ) * Real.log n +
              ps.C_eq * (2 * (ℓval : ℝ) + 7) := hs
        _ ≤ ((((2 * C_K * (n : ℝ) * Real.log n + 4 * ps.C_eq * (C_K + 2) * (n : ℝ) * Real.log n) +
              4 * (ps.toffoliCirc.length : ℝ) * (n : ℝ) * Real.log n) +
              2 * ps.C_ch * (n : ℝ) * Real.log n) +
              2 * ps.C_hc * (n : ℝ) * Real.log n) +
              ps.C_eq * (2 * C_ℓ + 7) * (n : ℝ) * Real.log n :=
            add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_trans h1 ha1) (le_trans h2 ha2))
              h3) h4) le_rfl) (le_trans h5 ha5)
        _ = C_step_g * (n : ℝ) * Real.log n := by
            dsimp [C_step_g]; ring
    have hloop_g := loopPrefix_gateCount_le (ps := ps) (r := r) (n := n) hm_ge hle hstep_g (2 ^ r) le_rfl
    have hprep_g : OracleCircuit.gateCount ([prepareMinusStep (n := n) (regM' ps r n)] :
        OracleCircuit gates12 (fun _ : Fin 1 => n + 1) M_tot) = 1 := by
      simp [OracleCircuit.gateCount, prepareMinusStep]
    have hfull_g : (c.gateCount : ℝ) =
        1 + (r : ℝ) + ((loopPrefix ps r n m_half hm_ge hle (2 ^ r) le_rfl).gateCount : ℝ) := by
      have hnat : c.gateCount =
          1 + r + (loopPrefix ps r n m_half hm_ge hle (2 ^ r) le_rfl).gateCount := by
        change (fullCirc ps r n m_half hm_ge hle).gateCount = _
        simp only [fullCirc, oracleCircuit_gateCount_append,
          hprep_g, liftToFull_gateCount, hadamardLayerC_length]
      exact_mod_cast hnat
    have h1r : 1 + (r : ℝ) ≤ (1 + C_K) * (n : ℝ) * Real.log n := by
      have h1r_log : 1 + (r : ℝ) ≤ (1 + C_K) * Real.log n := by linarith [hr_le, hlogn_ge]
      have hnonneg : 0 ≤ (1 + C_K) * Real.log n := by positivity
      calc 1 + (r : ℝ) ≤ (1 + C_K) * Real.log n := h1r_log
        _ ≤ ((1 + C_K) * Real.log n) * (n : ℝ) := le_mul_of_one_le_right hnonneg hn_ge1
        _ = (1 + C_K) * (n : ℝ) * Real.log n := by ring
    have hK_ge1 : (1 : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_two_pow
    have h1r_K : 1 + (r : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) * ((1 + C_K) * (n : ℝ) * Real.log n) := by
      have hnonneg : 0 ≤ (1 + C_K) * (n : ℝ) * Real.log n := by positivity
      exact le_trans h1r (le_mul_of_one_le_left hnonneg hK_ge1)
    have htot_g : (c.gateCount : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) * ((C_step_g + 1 + C_K) * (n : ℝ) * Real.log n) := by
      calc (c.gateCount : ℝ)
          = (1 + (r : ℝ)) + ((loopPrefix ps r n m_half hm_ge hle (2 ^ r) le_rfl).gateCount : ℝ) := hfull_g
        _ ≤ ((2 ^ r : ℕ) : ℝ) * ((1 + C_K) * (n : ℝ) * Real.log n) +
              ((2 ^ r : ℕ) : ℝ) * (C_step_g * (n : ℝ) * Real.log n) := add_le_add h1r_K hloop_g
        _ = ((2 ^ r : ℕ) : ℝ) * ((C_step_g + 1 + C_K) * (n : ℝ) * Real.log n) := by ring
    have hC_ge : C_K * (C_step_g + 1 + C_K) ≤ C :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hnonneg_mid : 0 ≤ (C_step_g + 1 + C_K) * (n : ℝ) * Real.log n := by positivity
    calc (c.gateCount : ℝ)
        ≤ ((2 ^ r : ℕ) : ℝ) * ((C_step_g + 1 + C_K) * (n : ℝ) * Real.log n) := htot_g
      _ ≤ (C_K * Real.log k) * ((C_step_g + 1 + C_K) * (n : ℝ) * Real.log n) :=
          mul_le_mul_of_nonneg_right hK_le hnonneg_mid
      _ = (C_K * (C_step_g + 1 + C_K)) * (n : ℝ) * Real.log n * Real.log k := by ring
      _ ≤ C * (n : ℝ) * Real.log n * Real.log k := by
          have hnn : 0 ≤ (n : ℝ) * Real.log n * Real.log k := by positivity
          calc (C_K * (C_step_g + 1 + C_K)) * (n : ℝ) * Real.log n * Real.log k
              = (C_K * (C_step_g + 1 + C_K)) * ((n : ℝ) * Real.log n * Real.log k) := by ring
            _ ≤ C * ((n : ℝ) * Real.log n * Real.log k) := mul_le_mul_of_nonneg_right hC_ge hnn
            _ = C * (n : ℝ) * Real.log n * Real.log k := by ring
  · -- nonOracleDepth
    have hstep_d : ∀ c_step : Fin (2 ^ r),
        (nonOracleDepth (stepCirc (ps := ps) (r := r) (n := n) hm_ge hle c_step) : ℝ) ≤
          C_step_d * Real.log n := by
      intro c_step
      have hs := stepCirc_nonOracleDepth_le (ps := ps) (r := r) (n := n) hm_ge hle hn2 c_step
      have hCeq_pos : 0 ≤ ps.C_eq := ps.hC_eq_pos.le
      have h1 : 2 * (r : ℝ) ≤ 2 * C_K * Real.log n := by linarith
      have h2 : 4 * ps.C_eq * ((r : ℝ) + 3) ≤ 4 * ps.C_eq * (C_K + 3) * Real.log n := by
        have h2a : (r : ℝ) + 3 ≤ (C_K + 3) * Real.log n := by linarith [hr_le, hlogn_ge]
        calc 4 * ps.C_eq * ((r : ℝ) + 3) ≤ 4 * ps.C_eq * ((C_K + 3) * Real.log n) :=
              mul_le_mul_of_nonneg_left h2a (by linarith)
          _ = 4 * ps.C_eq * (C_K + 3) * Real.log n := by ring
      have h3 : 4 * (ps.toffoliDepth : ℝ) ≤ 4 * (ps.toffoliDepth : ℝ) * Real.log n := by
        calc 4 * (ps.toffoliDepth : ℝ) = (4 * (ps.toffoliDepth : ℝ)) * 1 := (mul_one _).symm
          _ ≤ (4 * (ps.toffoliDepth : ℝ)) * Real.log n :=
              mul_le_mul_of_nonneg_left hlogn_ge (by positivity)
          _ = 4 * (ps.toffoliDepth : ℝ) * Real.log n := by ring
      have h4 : ps.C_eq * (2 * (ℓval : ℝ) + 9) ≤ ps.C_eq * (2 * C_ℓ + 9) * Real.log n := by
        have h4a : 2 * (ℓval : ℝ) + 9 ≤ (2 * C_ℓ + 9) * Real.log n := by linarith [hℓ_le, hlogn_ge]
        calc ps.C_eq * (2 * (ℓval : ℝ) + 9) ≤ ps.C_eq * ((2 * C_ℓ + 9) * Real.log n) :=
              mul_le_mul_of_nonneg_left h4a hCeq_pos
          _ = ps.C_eq * (2 * C_ℓ + 9) * Real.log n := by ring
      calc (nonOracleDepth (stepCirc (ps := ps) (r := r) (n := n) hm_ge hle c_step) : ℝ)
          ≤ 2 * (r : ℝ) + 4 * ps.C_eq * ((r : ℝ) + 3) + 4 * (ps.toffoliDepth : ℝ) +
              2 * (ps.C_ch + ps.C_hc) * Real.log n + ps.C_eq * (2 * (ℓval : ℝ) + 9) := hs
        _ ≤ (2 * C_K * Real.log n) + (4 * ps.C_eq * (C_K + 3) * Real.log n) +
              (4 * (ps.toffoliDepth : ℝ) * Real.log n) + (2 * (ps.C_ch + ps.C_hc) * Real.log n) +
              (ps.C_eq * (2 * C_ℓ + 9) * Real.log n) := by
            linarith [h1, h2, h3, h4]
        _ = C_step_d * Real.log n := by
            dsimp [C_step_d]; ring
    have hloop_d := loopPrefix_nonOracleDepth_le (ps := ps) (r := r) (n := n) hm_ge hle hstep_d (2 ^ r) le_rfl
    have hprep_d : nonOracleDepth ([prepareMinusStep (n := n) (regM' ps r n)] :
        OracleCircuit gates12 (fun _ : Fin 1 => n + 1) M_tot) ≤ 1 := by
      simpa using nonOracleDepth_le_length
        ([prepareMinusStep (n := n) (regM' ps r n)] : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) M_tot)
    have hhad_d : nonOracleDepth (liftToFull (ps := ps) (r := r) (n := n) hadamardLayerC) ≤ 1 :=
      le_trans (liftToFull_depth_le _) (hadamardLayerC_depth_le_one (ps := ps) (r := r) (n := n))
    have hfull_d : nonOracleDepth c ≤ 2 + nonOracleDepth (loopPrefix ps r n m_half hm_ge hle (2 ^ r) le_rfl) := by
      change nonOracleDepth (([prepareMinusStep (n := n) (regM' ps r n)] ++
          liftToFull (ps := ps) (r := r) (n := n) hadamardLayerC) ++
          loopPrefix ps r n m_half hm_ge hle (2 ^ r) le_rfl) ≤ _
      have ha1 := nonOracleDepth_append
        ([prepareMinusStep (n := n) (regM' ps r n)] ++
          liftToFull (ps := ps) (r := r) (n := n) hadamardLayerC)
        (loopPrefix ps r n m_half hm_ge hle (2 ^ r) le_rfl)
      have ha2 := nonOracleDepth_cons
        (prepareMinusStep (n := n) (regM' ps r n))
        (liftToFull (ps := ps) (r := r) (n := n) hadamardLayerC)
      exact le_trans ha1 (Nat.add_le_add_right (le_trans ha2 (Nat.add_le_add hprep_d hhad_d)) _)
    have hfull_dr : (nonOracleDepth c : ℝ) ≤
        2 + (nonOracleDepth (loopPrefix ps r n m_half hm_ge hle (2 ^ r) le_rfl) : ℝ) := by
      exact_mod_cast hfull_d
    have hK_ge1 : (1 : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    have h2_K : (2 : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) * (2 * Real.log n) := by
      have : (2 : ℝ) ≤ 2 * Real.log n := by linarith
      exact le_trans this (le_mul_of_one_le_left (by positivity) hK_ge1)
    have htot_d : (nonOracleDepth c : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) * ((C_step_d + 2) * Real.log n) := by
      calc (nonOracleDepth c : ℝ)
          ≤ 2 + (nonOracleDepth (loopPrefix ps r n m_half hm_ge hle (2 ^ r) le_rfl) : ℝ) := hfull_dr
        _ ≤ ((2 ^ r : ℕ) : ℝ) * (2 * Real.log n) +
              ((2 ^ r : ℕ) : ℝ) * (C_step_d * Real.log n) := add_le_add h2_K hloop_d
        _ = ((2 ^ r : ℕ) : ℝ) * ((C_step_d + 2) * Real.log n) := by ring
    have hC_ge : C_K * (C_step_d + 2) ≤ C :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hnonneg_mid : 0 ≤ (C_step_d + 2) * Real.log n := by positivity
    calc (nonOracleDepth c : ℝ)
        ≤ ((2 ^ r : ℕ) : ℝ) * ((C_step_d + 2) * Real.log n) := htot_d
      _ ≤ (C_K * Real.log k) * ((C_step_d + 2) * Real.log n) :=
          mul_le_mul_of_nonneg_right hK_le hnonneg_mid
      _ = (C_K * (C_step_d + 2)) * (Real.log n * Real.log k) := by ring
      _ ≤ C * (Real.log n * Real.log k) := by
          have hnn : 0 ≤ Real.log n * Real.log k := by positivity
          exact mul_le_mul_of_nonneg_right hC_ge hnn
      _ = C * Real.log n * Real.log k := by ring
  · -- Correctness for every A with A.card = k
    intro A hA
    have hA' : A.card = 2 * m_half + 1 := by rw [hA, hmk]
    have hK_err : 4 * ‖wCatVec n m_half A hA'‖ ^ 2 / (2 ^ r : ℕ) ≤ ε := by
      have hw := hC₀_bound n m_half hm_ge hle A hA'
      rw [hmk] at hw
      have h2r_pos : (0 : ℝ) < (2 ^ r : ℕ) := by positivity
      rw [div_le_iff₀ h2r_pos]
      calc 4 * ‖wCatVec n m_half A hA'‖ ^ 2
          ≤ 4 * (C₀ * Real.log k) := by linarith
        _ = ε * (4 * C₀ * Real.log k / ε) := by field_simp
        _ ≤ ε * (2 ^ r : ℕ) := mul_le_mul_of_nonneg_left hpow_ge_real hε0.le
    exact fullCirc_correct (ps := ps) (r := r) (n := n) hr1 m_half hm_ge hle A hA' hK_err

end WalkCorrectnessAndComplexity

end Thm49Walk



/-
  Bridge instantiating `Thm49Walk.PrimitiveSuite` from `Thm49Primitives`,
  followed by the top-level `theorem solution`.
-/

namespace Thm49Bridge

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open Thm49Primitives Thm49Algebra Thm49Walk

private lemma packCH_zero (n : ℕ) (c : Bool) (x a : Qubits n) :
    packCH n n c x a 0 = c := by
  simp [packCH]

private lemma packCH_tgt (n : ℕ) (c : Bool) (x a : Qubits n) (i : Fin n) :
    packCH n n c x a ⟨1 + i.1, by have := i.isLt; omega⟩ = x i := by
  dsimp only [packCH]
  have hi := i.isLt
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1
  ext
  simp

private lemma packCH_anc (n : ℕ) (c : Bool) (x a : Qubits n) (j : Fin n) :
    packCH n n c x a (Fin.natAdd (1 + n) j) = a j := by
  dsimp only [packCH]
  rw [dif_neg (by simp), dif_neg (by simp)]
  congr 1
  ext
  simp

private lemma packCH_inj (n : ℕ) (c : Bool) :
    Function.Injective (fun y : Qubits n => packCH n n c y (fun _ => false)) := by
  intro y1 y2 h
  funext i
  have hi := congrFun h ⟨1 + i.1, by have := i.isLt; omega⟩
  simpa [packCH_tgt] using hi

private lemma eq_packCH_of (n : ℕ) (c : Bool) (w : Qubits (1 + n + n))
    (h0 : w 0 = c) (hanc : ∀ j : Fin n, w (Fin.natAdd (1 + n) j) = false) :
    w = packCH n n c (fun i : Fin n => w ⟨1 + i.1, by have := i.isLt; omega⟩) (fun _ => false) := by
  funext k
  dsimp only [packCH]
  by_cases hk0 : k.1 = 0
  · rw [dif_pos hk0]
    have hk : k = 0 := Fin.ext hk0
    rw [hk, h0]
  · rw [dif_neg hk0]
    by_cases hk1 : k.1 < 1 + n
    · rw [dif_pos hk1]
      congr 1
      ext
      simp
      omega
    · rw [dif_neg hk1]
      have hkt := k.isLt
      have hk_eq : k = Fin.natAdd (1 + n) ⟨k.1 - (1 + n), by omega⟩ := Fin.ext (by simp; omega)
      rw [hk_eq]
      exact hanc _

private lemma bridge_ch_act (n : ℕ) (c : Bool) (x : Qubits n) :
    act (ctrlHadamardN n).toCircuit.unitary (ket (packCH n n c x (fun _ => false))) =
      if c then
        ∑ y : Qubits n, (hadamardN n y x) • ket (packCH n n true y (fun _ => false))
      else
        ket (packCH n n false x (fun _ => false)) := by
  classical
  let z : Qubits (1 + n + n) := packCH n n c x (fun _ => false)
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
      (ctrlHadamardN n).unitary (packCH n n c' y (fun _ => false)) z =
        if c' = c then (if c then hadamardN n y x else if y = x then 1 else 0) else 0 := by
    intro y c'
    rw [ctrlHadamardN_implements n _ z hz_clean]
    have hy_clean : ∀ j : Fin n,
        packCH n n c' y (fun _ => false) (Fin.natAdd (1 + n) j) = false := fun j =>
      packCH_anc n c' y (fun _ => false) j
    rw [if_pos hy_clean]
    simp only [ctrlHadamardMat, Matrix.of_apply, controlledQubits, controlled, Matrix.submatrix_apply,
      Matrix.one_apply]
    have hy_zero : packCH n n c' y (fun _ => false)
        (Fin.castAdd n ((0 : Fin (n + 1)).cast (Nat.add_comm n 1))) = c' :=
      packCH_zero n c' y (fun _ => false)
    have hy_tail : Fin.tail (fun i : Fin (n + 1) =>
        packCH n n c' y (fun _ => false) (Fin.castAdd n (i.cast (Nat.add_comm n 1)))) = y := by
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
      Finset.univ.image (fun y : Qubits n => packCH n n true y (fun _ => false))
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
    packEq L L addr tgt a ⟨i.1, by have := i.isLt; omega⟩ = addr i := by
  dsimp only [packEq]
  have hi := i.isLt
  rw [dif_pos hi]

private lemma packEq_tgt (L : ℕ) (addr : Qubits L) (tgt : Bool) (a : Qubits L) :
    packEq L L addr tgt a ⟨L, by omega⟩ = tgt := by
  dsimp only [packEq]
  rw [dif_neg (by simp), dif_pos rfl]

private lemma packEq_anc (L : ℕ) (addr : Qubits L) (tgt : Bool) (a : Qubits L) (j : Fin L) :
    packEq L L addr tgt a (Fin.natAdd (L + 1) j) = a j := by
  dsimp only [packEq]
  have hj := j.isLt
  rw [dif_neg (by simp; omega), dif_neg (by simp; omega)]
  congr 1
  ext
  simp

private lemma packEq_inj (L : ℕ) (addr : Qubits L) :
    Function.Injective (fun b' : Bool => packEq L L addr b' (fun _ => false)) := by
  intro b1 b2 h
  have hb := congrFun h ⟨L, by omega⟩
  simpa [packEq_tgt] using hb

private lemma eq_packEq_of (L : ℕ) (addr : Qubits L) (y : Qubits (L + 1 + L))
    (haddr : ∀ i : Fin L, y ⟨i.1, by have := i.isLt; omega⟩ = addr i)
    (hanc : ∀ j : Fin L, y (Fin.natAdd (L + 1) j) = false) :
    y = packEq L L addr (y ⟨L, by omega⟩) (fun _ => false) := by
  funext k
  dsimp only [packEq]
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
    act (multiEqCtrl1 L pat U hU).toCircuit.unitary (ket (packEq L L addr tgt (fun _ => false))) =
      if addr = pat then
        ∑ b' : Bool, (U b' tgt) • ket (packEq L L addr b' (fun _ => false))
      else
        ket (packEq L L addr tgt (fun _ => false)) := by
  classical
  let z : Qubits (L + 1 + L) := packEq L L addr tgt (fun _ => false)
  have hz_clean : ∀ j : Fin L, z (Fin.natAdd (L + 1) j) = false := fun j =>
    packEq_anc L addr tgt (fun _ => false) j
  change act (multiEqCtrl1 L pat U hU).unitary (ket z) = _
  rw [act_ket_eq]
  have hz_addr : ∀ i : Fin L, z ⟨i.1, by omega⟩ = addr i := fun i =>
    packEq_addr L addr tgt (fun _ => false) i
  have hz_tgt : z ⟨L, by omega⟩ = tgt := packEq_tgt L addr tgt (fun _ => false)
  have hentry_val : ∀ b' : Bool,
      (multiEqCtrl1 L pat U hU).unitary (packEq L L addr b' (fun _ => false)) z =
        if addr = pat then U b' tgt else if b' = tgt then 1 else 0 := by
    intro b'
    rw [multiEqCtrl1_implements L pat U hU _ z hz_clean]
    have hy_clean : ∀ j : Fin L,
        packEq L L addr b' (fun _ => false) (Fin.natAdd (L + 1) j) = false := fun j =>
      packEq_anc L addr b' (fun _ => false) j
    rw [if_pos hy_clean]
    simp only [eqCtrlMat, Matrix.of_apply]
    have hy_addr : ∀ i : Fin L,
        packEq L L addr b' (fun _ => false) (Fin.castAdd L ⟨i.1, by omega⟩) =
        z (Fin.castAdd L ⟨i.1, by omega⟩) := fun i => by
      change packEq L L addr b' (fun _ => false) ⟨i.1, by have := i.isLt; omega⟩ =
        z ⟨i.1, by have := i.isLt; omega⟩
      rw [packEq_addr, hz_addr]
    have hy_tgt : packEq L L addr b' (fun _ => false) (Fin.castAdd L ⟨L, by omega⟩) = b' :=
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
      Finset.univ.image (fun b' : Bool => packEq L L addr b' (fun _ => false))
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
      change (multiEqCtrl1 L pat U hU).unitary (packEq L L addr tgt (fun _ => false)) z • ket z = ket z
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
    packHC n (Nat.clog 2 (n + 1)) (hammingAnc n) x w a = Fin.addCases (Fin.addCases x w) a := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · refine Fin.addCases (fun q => ?_) (fun b => ?_) i
    · simp [packHC, Fin.addCases_left, q.isLt]
    · dsimp only [packHC]
      have hnot : ¬ (Fin.castAdd (hammingAnc n) (Fin.natAdd n b)).1 < n := by simp
      have hlt : (Fin.castAdd (hammingAnc n) (Fin.natAdd n b)).1 < n + Nat.clog 2 (n + 1) := by
        simp
      rw [dif_neg hnot, dif_pos hlt, Fin.addCases_left, Fin.addCases_right]
      congr 1; ext; simp
  · dsimp only [packHC]
    rw [dif_neg (by simp; omega), dif_neg (by simp), Fin.addCases_right]
    congr 1; ext; simp

private lemma bridge_hc_act (n : ℕ) (x : Qubits n) :
    act (hammingCounter n).toCircuit.unitary
        (ket (packHC n (Nat.clog 2 (n + 1)) (hammingAnc n) x (fun _ => false) (fun _ => false))) =
      ket (packHC n (Nat.clog 2 (n + 1)) (hammingAnc n) x
        (Thm49Walk.natToBitsLSB (Nat.clog 2 (n + 1)) (hammingWeight x)) (fun _ => false)) := by
  rw [packHC_eq_addCases, packHC_eq_addCases]
  have hbits : Thm49Walk.natToBitsLSB (Nat.clog 2 (n + 1)) (hammingWeight x) =
      Thm49Primitives.natToBitsLSB (hcEll n) (Finset.univ.filter fun i : Fin n => x i = true).card :=
    rfl
  rw [hbits]
  exact act_hammingCounter_zero_ket n x

noncomputable def thm49PrimitiveSuite : Thm49Walk.PrimitiveSuite where
  toffoliCirc := toffoli3.toCircuit
  toffoliDepth := toffoli3.depth
  toffoli_hdepth _ _ := toffoli3.nonOracleDepth_le
  toffoli_act b₀ b₁ b₂ := by
    let x : Qubits 3 := fun i : Fin 3 =>
      if i.1 = 0 then b₀ else if i.1 = 1 then b₁ else b₂
    change act toffoli3.unitary (ket x) = _
    rw [act_toffoli3_ket x]
    congr 1
    funext i
    fin_cases i <;> rfl
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
      rw [le_div_iff₀ hlog2_pos]
      linarith
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

end Thm49Bridge

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement in
theorem solution :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ k n : ℕ, 2 ≤ k → k ≤ n → Odd k →
        ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m) (out : Fin n ↪ Fin m),
          (c.queryCount 0 : ℝ) ≤ C * Real.log k ∧
          (c.gateCount : ℝ) ≤ C * n * Real.log n * Real.log k ∧
          (nonOracleDepth c : ℝ) ≤ C * Real.log n * Real.log k ∧
          ∀ A : Finset (Fin n), A.card = k →
            open Classical in
            probEvent (act (c.unitary fun _ => majOracle A) (zeroKet m))
              (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 1 - ε :=
  Thm49Walk.theorem_4_9_from_primitives Thm49Bridge.thm49PrimitiveSuite
