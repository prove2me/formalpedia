-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_4_10
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T06:19:28.516401+00:00
-- url     : https://prove2.me/submissions/b726c0bd-060e-4645-afac-f0e0e5d3578e

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Supplement_majOracle
import Definitions.Def_QuantumLTF_Membership_Supplement_nonOracleDepth
import Definitions.Def_QuantumLTF_Membership_Supplement_coupledOp410
import Definitions.Def_QuantumLTF_Membership_Supplement_primitiveSuite410
import Theorems.Thm_QuantumLTF_Membership_Supplement_coupled_transducer_410
import Theorems.Thm_QuantumLTF_Membership_Supplement_primitive_suite_410

set_option autoImplicit false

namespace Thm410Walk

open QAlgorithms QuantumLTF.Majority QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.CoupledOp410

/-! ### Local Matrix Action, Gate Unitarity, and Transducer Interface Aliases -/

private lemma act_one_vec {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  ext y; simp [act]

private lemma act_add {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act U (ψ + φ) = act U ψ + act U φ := by
  ext y; simp [act, Matrix.mulVec_add]

private lemma act_smul {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act U (c • ψ) = c • act U ψ := by
  ext y; simp [act, Matrix.mulVec_smul]

private lemma act_sum {ι κ : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ ι) :
    act U (∑ x ∈ s, f x) = ∑ x ∈ s, act U (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext y; simp [act]
  | insert a s ha ih => rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

private lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext y; simp [act, Matrix.mulVec_mulVec]

private lemma act_ket_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (z : ι) :
    act U (ket z) = ∑ y : ι, (U y z) • ket y := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single z]
  · simp only [↓reduceIte, mul_one]
    rw [Finset.sum_eq_single y] <;> simp (config := { contextual := true }) [eq_comm]
  · intro u _ hu; simp [hu]
  · simp

private lemma pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, pauliX,
    Matrix.of_apply]
  cases a <;> cases b <;> norm_num

private lemma pauliZ_mem_unitaryGroup : pauliZ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, pauliZ,
    Matrix.diagonal_apply]
  cases a <;> cases b <;> norm_num

private lemma hadamard_mem_unitaryGroup : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hHs : star hadamard = hadamard := by
    ext a b; cases a <;> cases b <;> simp [hadamard, Matrix.star_apply, Complex.conj_ofReal]
  rw [hHs, hadamard_mul_self]

private lemma liftOdd_mem_castSucc {n k : ℕ} (A : BoundedSupports n k) (i : Fin n) :
    i.castSucc ∈ liftOdd A ↔ i ∈ A.1 :=
  (coupled_transducer_410.2.2.2.1 A).1 i

private lemma liftOdd_card_eq {n k : ℕ} (A : BoundedSupports n k) :
    (liftOdd A).card = 2 * layerOf A + 1 ∧ layerOf A ≤ k / 2 :=
  (coupled_transducer_410.2.2.2.1 A).2.1

private lemma liftOdd_majorityBit_snoc_true {n k : ℕ} (A : BoundedSupports n k) (x : Qubits n) :
    majorityBit (liftOdd A) (Fin.snoc (α := fun _ => Bool) x true) = majorityBit A.1 x :=
  (coupled_transducer_410.2.2.2.1 A).2.2.1 x

private lemma liftOdd_majorityBit_snoc_false {n k : ℕ} (A : BoundedSupports n k) (x : Qubits n) :
    majorityBit (liftOdd A) (Fin.snoc (α := fun _ => Bool) (fun i => !(x i)) false) =
      !(majorityBit A.1 x) :=
  (coupled_transducer_410.2.2.2.1 A).2.2.2 x

private lemma wCatVec410_mode_zero_eq_zero {n' M m : ℕ} (B : Finset (Fin n'))
    (hB : B.card = 2 * m + 1) (S : Qubits n') :
    wCatVec410 n' M m B hB (modeKet M 0, S) = 0 :=
  coupled_transducer_410.2.2.2.2.1 B hB S

private lemma wCatVec410_energy_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k n : ℕ), 2 ≤ k → k ≤ n → ∀ A : BoundedSupports n k,
      ‖wCatVec410 (n + 1) (k / 2) (layerOf A) (liftOdd A) (liftOdd_card_eq A).1‖ ^ 2 ≤
        C₀ * Real.log k := by
  obtain ⟨C₀, hpos, h⟩ := coupled_transducer_410.2.2.2.2.2.1
  exact ⟨C₀, hpos, fun k n hk2 hkn A => h k n hk2 hkn A (liftOdd_card_eq A).1⟩

private lemma act_phaseCtrl410_wCatVec410 {n' M m : ℕ} (B : Finset (Fin n'))
    (hB : B.card = 2 * m + 1) :
    act (phaseCtrl410 M n' B) (wCatVec410 n' M m B hB) = wCatAfter410 n' M m B hB :=
  coupled_transducer_410.2.2.2.2.2.2.1 B hB

private lemma U_ideal410_transduces {n' M m : ℕ} (hM : 1 ≤ M) (hmM : m ≤ M) (hle : 2 * m + 1 ≤ n')
    (B : Finset (Fin n')) (hB : B.card = 2 * m + 1) :
    act (U_ideal410 M n') (tensorVec (ket (modeKet M 0)) (zeroKet n') + wCatAfter410 n' M m B hB) =
      tensorVec (ket (modeKet M 0)) (ket (fun i : Fin n' => decide (i ∈ B))) +
        wCatVec410 n' M m B hB :=
  coupled_transducer_410.2.2.2.2.2.2.2 hM hmM hle B hB

/-! ### Bit-order LSB & basic gate / `OracleCircuit` helpers -/

lemma natToBitsLSB_inj_of_lt {ℓ a b : ℕ} (ha : a < 2 ^ ℓ) (hb : b < 2 ^ ℓ)
    (h : natToBitsLSB ℓ a = natToBitsLSB ℓ b) : a = b := by
  have := congrArg bitsToNatLSB h
  rwa [bitsToNatLSB_natToBitsLSB ha, bitsToNatLSB_natToBitsLSB hb] at this

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

lemma hadamard_mul_pauliX_mem_unitaryGroup :
    hadamard * pauliX ∈ Matrix.unitaryGroup Bool ℂ :=
  Submonoid.mul_mem _ hadamard_mem_unitaryGroup pauliX_mem_unitaryGroup

def cnotMat : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 ∧ p.2 = (if q.1 then !(q.2) else q.2) then 1 else 0

lemma cnotMat_mem_unitaryGroup : cnotMat ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext p q
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [Matrix.mul_apply, Matrix.star_apply, cnotMat, Matrix.of_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Fintype.sum_bool]
  cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> simp

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
          exact congrFun (hup_comp (u ∘ w)) j
        · rw [hup_out (u ∘ w) i hi, huz i hi]
      rw [if_neg hne, mul_zero]
    rw [hsum, Finset.sum_image (fun x₁ _ x₂ _ h => hup_inj h)]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hy : ∀ a : Fin m, a ∉ Set.range w → y a = updateW x a := fun a ha =>
      (hout a ha).trans (hup_out x a ha).symm
    have hz : ∀ a : Fin m, a ∉ Set.range w → updateW x a = z a := fun a ha =>
      hup_out x a ha
    rw [if_pos hy, if_pos hz, hup_comp]
  · rw [if_neg hout]
    symm
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases h1 : ∀ a, a ∉ Set.range w → y a = u a
    · have h2 : ¬ ∀ a, a ∉ Set.range w → u a = z a := fun h2' =>
        hout fun a ha => (h1 a ha).trans (h2' a ha)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma embedOp_one {k m : ℕ} (w : Fin k ↪ Fin m) :
    embedOp (1 : Matrix (Qubits k) (Qubits k) ℂ) w = 1 := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg hyz]
    split_ifs with hout hcomp
    · exfalso; apply hyz; funext i
      by_cases hi : i ∈ Set.range w
      · obtain ⟨j, rfl⟩ := hi; exact congrFun hcomp j
      · exact hout i hi
    · rfl
    · rfl

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
  unfold Circuit.unitary embedCircuit
  induction c with
  | nil => simp [embedOp_one]
  | cons g gs ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one] at ih ⊢
    rw [ih, embedOp_mul, embedOp_comp]

lemma circuit_unitary_append {S : Set Gate} {m : ℕ} (c₁ c₂ : Circuit S m) :
    (c₁ ++ c₂).unitary = c₂.unitary * c₁.unitary := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

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
    (c₁ c₂ : OracleCircuit S a m) (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
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
            exact (congrFun hUeq j).trans (congrFun hz'_in j).symm
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

/-! ### `nonOracleDepth` basic bounds -/

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
        have hs : (stepWireSet st).sup τ ≤ (stepWireSet st).sup (fun i => τ i + B) - B := by
          refine Finset.sup_le fun y hy => ?_
          have := Finset.le_sup (f := fun i => τ i + B) hy
          omega
        have hle : B ≤ (stepWireSet st).sup (fun i => τ i + B) := by
          have := Finset.le_sup (f := fun i => τ i + B) hx
          omega
        omega
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
        exact le_of_eq (hτ g List.mem_cons_self (g.wires x) ⟨x, rfl⟩)
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

/-! ### Register Layout and State Packing in `Fin M'` -/

section FullCircuit410

variable (ps : PrimitiveSuite410)

noncomputable def ancMax410 (r n M : ℕ) : ℕ :=
  max (ps.ancCH (n + 1)) (max (ps.ancHC (n + 1)) (max (ps.ancCN n)
    (max (ps.ancUTilde M (n + 1)) (max (ps.ancEq (qW M))
      (max (ps.ancEq r) (max (ps.ancEq (r + qW M)) (ps.ancEq (1 + qW M))))))))

noncomputable def regM'410 (r n M : ℕ) : ℕ :=
  r + qW M + (n + 1) + Nat.clog 2 (n + 2) + 5 + ancMax410 ps r n M

section FixedParams410

variable {ps} {r n M : ℕ}

local notation "qw" => qW M
local notation "n'" => n + 1
local notation "ℓ" => Nat.clog 2 (n + 2)
local notation "Amax" => ancMax410 ps r n M
local notation "M'" => regM'410 ps r n M

def regC : Fin r ↪ Fin M' :=
  ⟨fun i => ⟨i.1, by dsimp only [regM'410]; omega⟩, fun _ _ h => Fin.ext (by
    have := congrArg Fin.val h; dsimp at this; omega)⟩

def regMode : Fin qw ↪ Fin M' :=
  ⟨fun i => ⟨r + i.1, by dsimp only [regM'410]; omega⟩, fun _ _ h => Fin.ext (by
    have := congrArg Fin.val h; dsimp at this; omega)⟩

def regQ : Fin n' ↪ Fin M' :=
  ⟨fun i => ⟨r + qw + i.1, by dsimp only [regM'410]; omega⟩, fun _ _ h => Fin.ext (by
    have := congrArg Fin.val h; dsimp at this; omega)⟩

def regW : Fin ℓ ↪ Fin M' :=
  ⟨fun i => ⟨r + qw + n' + i.1, by dsimp only [regM'410]; omega⟩, fun _ _ h => Fin.ext (by
    have := congrArg Fin.val h; dsimp at this; omega)⟩

def wireFC : Fin M' := ⟨r + qw + n' + ℓ, by dsimp only [regM'410]; omega⟩
def wireFH : Fin M' := ⟨r + qw + n' + ℓ + 1, by dsimp only [regM'410]; omega⟩
def wireFQ : Fin M' := ⟨r + qw + n' + ℓ + 2, by dsimp only [regM'410]; omega⟩
def wirePub : Fin M' := ⟨r + qw + n' + ℓ + 3, by dsimp only [regM'410]; omega⟩
def wireNeg : Fin M' := ⟨r + qw + n' + ℓ + 4, by dsimp only [regM'410]; omega⟩

def regAnc : Fin Amax ↪ Fin M' :=
  ⟨fun i => ⟨r + qw + n' + ℓ + 5 + i.1, by dsimp only [regM'410]; omega⟩, fun _ _ h => Fin.ext (by
    have := congrArg Fin.val h; dsimp at this; omega)⟩

@[simp] lemma regC_val (i : Fin r) : (regC (ps := ps) (r := r) (n := n) (M := M) i).1 = i.1 := rfl
@[simp] lemma regMode_val (i : Fin qw) : (regMode (ps := ps) (r := r) (n := n) (M := M) i).1 = r + i.1 := rfl
@[simp] lemma regQ_val (i : Fin n') : (regQ (ps := ps) (r := r) (n := n) (M := M) i).1 = r + qw + i.1 := rfl
@[simp] lemma regW_val (i : Fin ℓ) : (regW (ps := ps) (r := r) (n := n) (M := M) i).1 = r + qw + n' + i.1 := rfl
@[simp] lemma wireFC_val : (wireFC (ps := ps) (r := r) (n := n) (M := M)).1 = r + qw + n' + ℓ := rfl
@[simp] lemma wireFH_val : (wireFH (ps := ps) (r := r) (n := n) (M := M)).1 = r + qw + n' + ℓ + 1 := rfl
@[simp] lemma wireFQ_val : (wireFQ (ps := ps) (r := r) (n := n) (M := M)).1 = r + qw + n' + ℓ + 2 := rfl
@[simp] lemma wirePub_val : (wirePub (ps := ps) (r := r) (n := n) (M := M)).1 = r + qw + n' + ℓ + 3 := rfl
@[simp] lemma wireNeg_val : (wireNeg (ps := ps) (r := r) (n := n) (M := M)).1 = r + qw + n' + ℓ + 4 := rfl
@[simp] lemma regAnc_val (i : Fin Amax) :
    (regAnc (ps := ps) (r := r) (n := n) (M := M) i).1 = r + qw + n' + ℓ + 5 + i.1 := rfl

def packState410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) : Qubits M' :=
  fun i =>
    if h0 : i.1 < r then c ⟨i.1, h0⟩
    else if h1 : i.1 < r + qw then mode ⟨i.1 - r, by omega⟩
    else if h2 : i.1 < r + qw + n' then q ⟨i.1 - (r + qw), by omega⟩
    else if h3 : i.1 < r + qw + n' + ℓ then w ⟨i.1 - (r + qw + n'), by omega⟩
    else if h4 : i.1 = r + qw + n' + ℓ then fc
    else if h5 : i.1 = r + qw + n' + ℓ + 1 then fh
    else if h6 : i.1 = r + qw + n' + ℓ + 2 then fq
    else if h7 : i.1 = r + qw + n' + ℓ + 3 then pub
    else if h8 : i.1 = r + qw + n' + ℓ + 4 then neg
    else a ⟨i.1 - (r + qw + n' + ℓ + 5), by dsimp only [regM'410] at *; omega⟩

lemma packState410_C (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) (i : Fin r) :
    packState410 c mode q w fc fh fq pub neg a (regC i) = c i := by
  simp only [packState410, regC_val, i.isLt, ↓reduceDIte]

lemma packState410_Mode (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) (i : Fin qw) :
    packState410 c mode q w fc fh fq pub neg a (regMode i) = mode i := by
  have hi := i.isLt
  have h0 : ¬ (r + i.1 < r) := by omega
  have h1 : r + i.1 < r + qw := by omega
  simp only [packState410, regMode_val, h0, h1, ↓reduceDIte]
  congr 1; ext; rw [Fin.val_mk]; omega

lemma packState410_Q (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) (i : Fin n') :
    packState410 c mode q w fc fh fq pub neg a (regQ i) = q i := by
  have hi := i.isLt
  have h0 : ¬ (r + qw + i.1 < r) := by omega
  have h1 : ¬ (r + qw + i.1 < r + qw) := by omega
  have h2 : r + qw + i.1 < r + qw + n' := by omega
  simp only [packState410, regQ_val, h0, h1, h2, ↓reduceDIte]
  congr 1; ext; rw [Fin.val_mk]; omega

lemma packState410_W (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) (i : Fin ℓ) :
    packState410 c mode q w fc fh fq pub neg a (regW i) = w i := by
  have hi := i.isLt
  have h0 : ¬ (r + qw + n' + i.1 < r) := by omega
  have h1 : ¬ (r + qw + n' + i.1 < r + qw) := by omega
  have h2 : ¬ (r + qw + n' + i.1 < r + qw + n') := by omega
  have h3 : r + qw + n' + i.1 < r + qw + n' + ℓ := by omega
  simp only [packState410, regW_val, h0, h1, h2, h3, ↓reduceDIte]
  congr 1; ext; rw [Fin.val_mk]; omega

lemma packState410_FC (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    packState410 c mode q w fc fh fq pub neg a wireFC = fc := by
  have h0 : ¬ (r + qw + n' + ℓ < r) := by omega
  have h1 : ¬ (r + qw + n' + ℓ < r + qw) := by omega
  have h2 : ¬ (r + qw + n' + ℓ < r + qw + n') := by omega
  have h3 : ¬ (r + qw + n' + ℓ < r + qw + n' + ℓ) := by omega
  simp only [packState410, wireFC_val, h0, h1, h2, h3, ↓reduceDIte]

lemma packState410_FH (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    packState410 c mode q w fc fh fq pub neg a wireFH = fh := by
  have h0 : ¬ (r + qw + n' + ℓ + 1 < r) := by omega
  have h1 : ¬ (r + qw + n' + ℓ + 1 < r + qw) := by omega
  have h2 : ¬ (r + qw + n' + ℓ + 1 < r + qw + n') := by omega
  have h3 : ¬ (r + qw + n' + ℓ + 1 < r + qw + n' + ℓ) := by omega
  have h4 : r + qw + n' + ℓ + 1 ≠ r + qw + n' + ℓ := by omega
  simp only [packState410, wireFH_val, h0, h1, h2, h3, h4, ↓reduceDIte]

lemma packState410_FQ (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    packState410 c mode q w fc fh fq pub neg a wireFQ = fq := by
  have h0 : ¬ (r + qw + n' + ℓ + 2 < r) := by omega
  have h1 : ¬ (r + qw + n' + ℓ + 2 < r + qw) := by omega
  have h2 : ¬ (r + qw + n' + ℓ + 2 < r + qw + n') := by omega
  have h3 : ¬ (r + qw + n' + ℓ + 2 < r + qw + n' + ℓ) := by omega
  have h4 : r + qw + n' + ℓ + 2 ≠ r + qw + n' + ℓ := by omega
  have h5 : r + qw + n' + ℓ + 2 ≠ r + qw + n' + ℓ + 1 := by omega
  simp only [packState410, wireFQ_val, h0, h1, h2, h3, h4, h5, ↓reduceDIte]

lemma packState410_Pub (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    packState410 c mode q w fc fh fq pub neg a wirePub = pub := by
  have h0 : ¬ (r + qw + n' + ℓ + 3 < r) := by omega
  have h1 : ¬ (r + qw + n' + ℓ + 3 < r + qw) := by omega
  have h2 : ¬ (r + qw + n' + ℓ + 3 < r + qw + n') := by omega
  have h3 : ¬ (r + qw + n' + ℓ + 3 < r + qw + n' + ℓ) := by omega
  have h4 : r + qw + n' + ℓ + 3 ≠ r + qw + n' + ℓ := by omega
  have h5 : r + qw + n' + ℓ + 3 ≠ r + qw + n' + ℓ + 1 := by omega
  have h6 : r + qw + n' + ℓ + 3 ≠ r + qw + n' + ℓ + 2 := by omega
  simp only [packState410, wirePub_val, h0, h1, h2, h3, h4, h5, h6, ↓reduceDIte]

lemma packState410_Neg (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    packState410 c mode q w fc fh fq pub neg a wireNeg = neg := by
  have h0 : ¬ (r + qw + n' + ℓ + 4 < r) := by omega
  have h1 : ¬ (r + qw + n' + ℓ + 4 < r + qw) := by omega
  have h2 : ¬ (r + qw + n' + ℓ + 4 < r + qw + n') := by omega
  have h3 : ¬ (r + qw + n' + ℓ + 4 < r + qw + n' + ℓ) := by omega
  have h4 : r + qw + n' + ℓ + 4 ≠ r + qw + n' + ℓ := by omega
  have h5 : r + qw + n' + ℓ + 4 ≠ r + qw + n' + ℓ + 1 := by omega
  have h6 : r + qw + n' + ℓ + 4 ≠ r + qw + n' + ℓ + 2 := by omega
  have h7 : r + qw + n' + ℓ + 4 ≠ r + qw + n' + ℓ + 3 := by omega
  simp only [packState410, wireNeg_val, h0, h1, h2, h3, h4, h5, h6, h7, ↓reduceDIte]

lemma packState410_Anc (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) (i : Fin Amax) :
    packState410 c mode q w fc fh fq pub neg a (regAnc i) = a i := by
  have h0 : ¬ (r + qw + n' + ℓ + 5 + i.1 < r) := by omega
  have h1 : ¬ (r + qw + n' + ℓ + 5 + i.1 < r + qw) := by omega
  have h2 : ¬ (r + qw + n' + ℓ + 5 + i.1 < r + qw + n') := by omega
  have h3 : ¬ (r + qw + n' + ℓ + 5 + i.1 < r + qw + n' + ℓ) := by omega
  have h4 : r + qw + n' + ℓ + 5 + i.1 ≠ r + qw + n' + ℓ := by omega
  have h5 : r + qw + n' + ℓ + 5 + i.1 ≠ r + qw + n' + ℓ + 1 := by omega
  have h6 : r + qw + n' + ℓ + 5 + i.1 ≠ r + qw + n' + ℓ + 2 := by omega
  have h7 : r + qw + n' + ℓ + 5 + i.1 ≠ r + qw + n' + ℓ + 3 := by omega
  have h8 : r + qw + n' + ℓ + 5 + i.1 ≠ r + qw + n' + ℓ + 4 := by omega
  simp only [packState410, regAnc_val, h0, h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceDIte]
  congr 1; ext; rw [Fin.val_mk]; omega

lemma packState410_eq_of_C (c₁ c₂ : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) (i : Fin M')
    (hi : ∀ k : Fin r, regC k = i → c₁ k = c₂ k) :
    packState410 c₁ mode q w fc fh fq pub neg a i = packState410 c₂ mode q w fc fh fq pub neg a i := by
  by_cases h0 : i.1 < r
  · simp only [packState410, h0, ↓reduceDIte]
    exact hi ⟨i.1, h0⟩ (Fin.ext rfl)
  · simp only [packState410, h0, ↓reduceDIte]

lemma packState410_eq_of_Mode (c : Qubits r) (m₁ m₂ : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) (i : Fin M') (hi : ∀ j : Fin qw, regMode j ≠ i) :
    packState410 c m₁ q w fc fh fq pub neg a i = packState410 c m₂ q w fc fh fq pub neg a i := by
  by_cases h0 : i.1 < r
  · simp only [packState410, h0, ↓reduceDIte]
  · by_cases h1 : i.1 < r + qw
    · exact absurd (Fin.ext (by simp only [regMode_val]; omega) : regMode ⟨i.1 - r, by omega⟩ = i)
        (hi ⟨i.1 - r, by omega⟩)
    · simp only [packState410, h0, h1, ↓reduceDIte]

lemma packState410_eq_of_Q (c : Qubits r) (mode : Qubits qw) (q₁ q₂ : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) (i : Fin M')
    (hi : ∀ j : Fin n', regQ j = i → q₁ j = q₂ j) :
    packState410 c mode q₁ w fc fh fq pub neg a i = packState410 c mode q₂ w fc fh fq pub neg a i := by
  by_cases h0 : i.1 < r
  · simp only [packState410, h0, ↓reduceDIte]
  · by_cases h1 : i.1 < r + qw
    · simp only [packState410, h0, h1, ↓reduceDIte]
    · by_cases h2 : i.1 < r + qw + n'
      · simp only [packState410, h0, h1, h2, ↓reduceDIte]
        exact hi ⟨i.1 - (r + qw), by omega⟩ (Fin.ext (by simp [regQ_val]; omega))
      · simp only [packState410, h0, h1, h2, ↓reduceDIte]

lemma packState410_eq_of_W (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w₁ w₂ : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) (i : Fin M') (hi : ∀ j : Fin ℓ, regW j ≠ i) :
    packState410 c mode q w₁ fc fh fq pub neg a i = packState410 c mode q w₂ fc fh fq pub neg a i := by
  by_cases h0 : i.1 < r
  · simp only [packState410, h0, ↓reduceDIte]
  · by_cases h1 : i.1 < r + qw
    · simp only [packState410, h0, h1, ↓reduceDIte]
    · by_cases h2 : i.1 < r + qw + n'
      · simp only [packState410, h0, h1, h2, ↓reduceDIte]
      · by_cases h3 : i.1 < r + qw + n' + ℓ
        · exact absurd (Fin.ext (by simp only [regW_val]; omega) : regW ⟨i.1 - (r + qw + n'), by omega⟩ = i)
            (hi ⟨i.1 - (r + qw + n'), by omega⟩)
        · simp only [packState410, h0, h1, h2, h3, ↓reduceDIte]

lemma packState410_eq_of_flag {c : Qubits r} {mode : Qubits qw} {q : Qubits n'} {w : Qubits ℓ}
    {fc₁ fc₂ fh₁ fh₂ fq₁ fq₂ pub₁ pub₂ neg₁ neg₂ : Bool} {a : Qubits Amax} {i : Fin M'}
    (hfc : i = wireFC → fc₁ = fc₂) (hfh : i = wireFH → fh₁ = fh₂)
    (hfq : i = wireFQ → fq₁ = fq₂) (hpub : i = wirePub → pub₁ = pub₂)
    (hneg : i = wireNeg → neg₁ = neg₂) :
    packState410 c mode q w fc₁ fh₁ fq₁ pub₁ neg₁ a i =
      packState410 c mode q w fc₂ fh₂ fq₂ pub₂ neg₂ a i := by
  by_cases h0 : i.1 < r
  · simp only [packState410, h0, ↓reduceDIte]
  · by_cases h1 : i.1 < r + qw
    · simp only [packState410, h0, h1, ↓reduceDIte]
    · by_cases h2 : i.1 < r + qw + n'
      · simp only [packState410, h0, h1, h2, ↓reduceDIte]
      · by_cases h3 : i.1 < r + qw + n' + ℓ
        · simp only [packState410, h0, h1, h2, h3, ↓reduceDIte]
        · by_cases h4 : i.1 = r + qw + n' + ℓ
          · simp only [packState410, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]
            exact hfc (Fin.ext h4)
          · by_cases h5 : i.1 = r + qw + n' + ℓ + 1
            · simp only [packState410, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_pos h5]
              exact hfh (Fin.ext h5)
            · by_cases h6 : i.1 = r + qw + n' + ℓ + 2
              · simp only [packState410, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_pos h6]
                exact hfq (Fin.ext h6)
              · by_cases h7 : i.1 = r + qw + n' + ℓ + 3
                · simp only [packState410, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6, dif_pos h7]
                  exact hpub (Fin.ext h7)
                · by_cases h8 : i.1 = r + qw + n' + ℓ + 4
                  · simp only [packState410, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6, dif_neg h7, dif_pos h8]
                    exact hneg (Fin.ext h8)
                  · simp only [packState410, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6, dif_neg h7, dif_neg h8]

lemma packState410_zero :
    packState410 (ps := ps) (r := r) (n := n) (M := M)
      (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
      false false false false false (fun _ => false) =
    fun _ => false := by
  funext i
  simp only [packState410]
  split_ifs <;> rfl

lemma packState410_inj {c₁ c₂ : Qubits r} {m₁ m₂ : Qubits qw} {q₁ q₂ : Qubits n'} {w₁ w₂ : Qubits ℓ}
    {fc₁ fc₂ fh₁ fh₂ fq₁ fq₂ pub₁ pub₂ neg₁ neg₂ : Bool} {a₁ a₂ : Qubits Amax}
    (h : packState410 (ps := ps) c₁ m₁ q₁ w₁ fc₁ fh₁ fq₁ pub₁ neg₁ a₁ =
         packState410 (ps := ps) c₂ m₂ q₂ w₂ fc₂ fh₂ fq₂ pub₂ neg₂ a₂) :
    c₁ = c₂ ∧ m₁ = m₂ ∧ q₁ = q₂ ∧ w₁ = w₂ ∧ fc₁ = fc₂ ∧ fh₁ = fh₂ ∧ fq₁ = fq₂ ∧
      pub₁ = pub₂ ∧ neg₁ = neg₂ ∧ a₁ = a₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; have := congrFun h (regC i); rwa [packState410_C, packState410_C] at this
  · funext i; have := congrFun h (regMode i); rwa [packState410_Mode, packState410_Mode] at this
  · funext i; have := congrFun h (regQ i); rwa [packState410_Q, packState410_Q] at this
  · funext i; have := congrFun h (regW i); rwa [packState410_W, packState410_W] at this
  · have := congrFun h wireFC; rwa [packState410_FC, packState410_FC] at this
  · have := congrFun h wireFH; rwa [packState410_FH, packState410_FH] at this
  · have := congrFun h wireFQ; rwa [packState410_FQ, packState410_FQ] at this
  · have := congrFun h wirePub; rwa [packState410_Pub, packState410_Pub] at this
  · have := congrFun h wireNeg; rwa [packState410_Neg, packState410_Neg] at this
  · funext i; have := congrFun h (regAnc i); rwa [packState410_Anc, packState410_Anc] at this

def coreEmb410 (p : Qubits r × Qubits qw × Qubits n') : Qubits M' :=
  packState410 (ps := ps) p.1 p.2.1 p.2.2 (fun _ => false) false false false false false (fun _ => false)

lemma coreEmb410_inj : Function.Injective (coreEmb410 (ps := ps) (r := r) (n := n) (M := M)) := by
  intro p₁ p₂ h
  rcases p₁ with ⟨c₁, m₁, q₁⟩; rcases p₂ with ⟨c₂, m₂, q₂⟩
  obtain ⟨hc, hm, hq, _⟩ := packState410_inj h
  exact Prod.ext hc (Prod.ext hm hq)

def coreEmbHom410 : (Qubits r × Qubits qw × Qubits n') ↪ Qubits M' :=
  ⟨coreEmb410, coreEmb410_inj⟩

@[simp] lemma coreEmbHom410_apply (p : Qubits r × Qubits qw × Qubits n') :
    coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) p = coreEmb410 (ps := ps) (r := r) (n := n) (M := M) p := rfl

end FixedParams410

end FullCircuit410

/-! ### Subcircuit Embeddings and Semantics in `Fin M'` -/

section SubCircuitEmbeddings410

variable {ps : PrimitiveSuite410} {r n M : ℕ}

local notation "qw" => qW M
local notation "n'" => n + 1
local notation "ℓ" => Nat.clog 2 (n + 2)
local notation "Amax" => ancMax410 ps r n M
local notation "M'" => regM'410 ps r n M

def singleWireEmb410 (w : Fin M') : Fin 1 ↪ Fin M' :=
  ⟨fun _ => w, fun a b _ => Subsingleton.elim a b⟩

@[simp] lemma singleWireEmb410_apply (w : Fin M') (i : Fin 1) :
    singleWireEmb410 (ps := ps) (r := r) (n := n) (M := M) w i = w := rfl

def embPair410 (u v : Fin M') (huv : u ≠ v) : Fin 2 ↪ Fin M' :=
  ⟨fun i => if i.1 = 0 then u else v, fun a b hab => by
    fin_cases a <;> fin_cases b <;> simp_all [huv.symm]⟩

@[simp] lemma embPair410_apply (u v : Fin M') (huv : u ≠ v) (i : Fin 2) :
    embPair410 (ps := ps) (r := r) (n := n) (M := M) u v huv i = if i.1 = 0 then u else v := rfl

def embToffoliNeg : Fin 3 ↪ Fin M' :=
  let f : Fin 3 → Fin M' := fun i =>
    if i.1 = 0 then wireFQ else if i.1 = 1 then regQ (Fin.last n) else wireNeg
  ⟨f, fun a b hab => by
    have hv := congrArg Fin.val hab
    fin_cases a <;> fin_cases b <;>
      simp [f, wireFQ_val, regQ_val, wireNeg_val] at hv <;> first | rfl | omega⟩

@[simp] lemma embToffoliNeg_apply (i : Fin 3) :
    embToffoliNeg (ps := ps) (r := r) (n := n) (M := M) i =
      if i.1 = 0 then wireFQ else if i.1 = 1 then regQ (Fin.last n) else wireNeg := rfl

def embEqPub : Fin (qw + 1 + ps.ancEq qw) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 < qw then regMode ⟨i.1, h0⟩
    else if h1 : i.1 = qw then wirePub
    else regAnc ⟨i.1 - (qw + 1), by
      have _ := i.isLt
      have hle : ps.ancEq qw ≤ Amax :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_max_right _ _))))
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;> simp only [regMode_val, wirePub_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embEqPub_apply (i : Fin (qw + 1 + ps.ancEq qw)) :
    embEqPub (ps := ps) (r := r) (n := n) (M := M) i =
      if h0 : i.1 < qw then regMode ⟨i.1, h0⟩
      else if h1 : i.1 = qw then wirePub
      else regAnc ⟨i.1 - (qw + 1), by
        have _ := i.isLt
        have hle : ps.ancEq qw ≤ Amax :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _))))
        omega⟩ := rfl

def embEqFQC : Fin (r + 1 + ps.ancEq r) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 < r then regC ⟨i.1, h0⟩
    else if h1 : i.1 = r then wireFQ
    else regAnc ⟨i.1 - (r + 1), by
      have _ := i.isLt
      have hle : ps.ancEq r ≤ Amax :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;> simp only [regC_val, wireFQ_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embEqFQC_apply (i : Fin (r + 1 + ps.ancEq r)) :
    embEqFQC (ps := ps) (r := r) (n := n) (M := M) i =
      if h0 : i.1 < r then regC ⟨i.1, h0⟩
      else if h1 : i.1 = r then wireFQ
      else regAnc ⟨i.1 - (r + 1), by
        have _ := i.isLt
        have hle : ps.ancEq r ≤ Amax :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
        omega⟩ := rfl

def embEqFQCMode : Fin ((r + qw) + 1 + ps.ancEq (r + qw)) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 < r then regC ⟨i.1, h0⟩
    else if h1 : i.1 < r + qw then regMode ⟨i.1 - r, by omega⟩
    else if h2 : i.1 = r + qw then wireFQ
    else regAnc ⟨i.1 - (r + qw + 1), by
      have _ := i.isLt
      have hle : ps.ancEq (r + qw) ≤ Amax :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_max_right _ _))))))
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;>
      simp only [regC_val, regMode_val, wireFQ_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embEqFQCMode_apply (i : Fin ((r + qw) + 1 + ps.ancEq (r + qw))) :
    embEqFQCMode (ps := ps) (r := r) (n := n) (M := M) i =
      if h0 : i.1 < r then regC ⟨i.1, h0⟩
      else if h1 : i.1 < r + qw then regMode ⟨i.1 - r, by omega⟩
      else if h2 : i.1 = r + qw then wireFQ
      else regAnc ⟨i.1 - (r + qw + 1), by
        have _ := i.isLt
        have hle : ps.ancEq (r + qw) ≤ Amax :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
              (le_max_right _ _))))))
        omega⟩ := rfl

def embEqFC : Fin (r + 1 + ps.ancEq r) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 < r then regC ⟨i.1, h0⟩
    else if h1 : i.1 = r then wireFC
    else regAnc ⟨i.1 - (r + 1), by
      have _ := i.isLt
      have hle : ps.ancEq r ≤ Amax :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;> simp only [regC_val, wireFC_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embEqFC_apply (i : Fin (r + 1 + ps.ancEq r)) :
    embEqFC (ps := ps) (r := r) (n := n) (M := M) i =
      if h0 : i.1 < r then regC ⟨i.1, h0⟩
      else if h1 : i.1 = r then wireFC
      else regAnc ⟨i.1 - (r + 1), by
        have _ := i.isLt
        have hle : ps.ancEq r ≤ Amax :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
        omega⟩ := rfl

def embEqFHMode0 : Fin ((1 + qw) + 1 + ps.ancEq (1 + qw)) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 = 0 then wireFC
    else if h1 : i.1 < 1 + qw then regMode ⟨i.1 - 1, by omega⟩
    else if h2 : i.1 = 1 + qw then wireFH
    else regAnc ⟨i.1 - (2 + qw), by
      have _ := i.isLt
      have hle : ps.ancEq (1 + qw) ≤ Amax :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_max_right _ _))))))
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;>
      simp only [wireFC_val, regMode_val, wireFH_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embEqFHMode0_apply (i : Fin ((1 + qw) + 1 + ps.ancEq (1 + qw))) :
    embEqFHMode0 (ps := ps) (r := r) (n := n) (M := M) i =
      if h0 : i.1 = 0 then wireFC
      else if h1 : i.1 < 1 + qw then regMode ⟨i.1 - 1, by omega⟩
      else if h2 : i.1 = 1 + qw then wireFH
      else regAnc ⟨i.1 - (2 + qw), by
        have _ := i.isLt
        have hle : ps.ancEq (1 + qw) ≤ Amax :=
          le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
              (le_max_right _ _))))))
        omega⟩ := rfl

def embCH410 : Fin (1 + n' + ps.ancCH n') ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 = 0 then wireFH
    else if h1 : i.1 < 1 + n' then regQ ⟨i.1 - 1, by omega⟩
    else regAnc ⟨i.1 - (1 + n'), by
      have _ := i.isLt
      have hle : ps.ancCH n' ≤ Amax := le_max_left _ _
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;> simp only [wireFH_val, regQ_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embCH410_apply (i : Fin (1 + n' + ps.ancCH n')) :
    embCH410 (ps := ps) (r := r) (n := n) (M := M) i =
      if h0 : i.1 = 0 then wireFH
      else if h1 : i.1 < 1 + n' then regQ ⟨i.1 - 1, by omega⟩
      else regAnc ⟨i.1 - (1 + n'), by
        have _ := i.isLt
        have hle : ps.ancCH n' ≤ Amax := le_max_left _ _
        omega⟩ := rfl

def embHC410 : Fin (n' + ℓ + ps.ancHC n') ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 < n' then regQ ⟨i.1, h0⟩
    else if h1 : i.1 < n' + ℓ then regW ⟨i.1 - n', by omega⟩
    else regAnc ⟨i.1 - (n' + ℓ), by
      have _ := i.isLt
      have hle : ps.ancHC n' ≤ Amax := le_trans (le_max_left _ _) (le_max_right _ _)
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;> simp only [regQ_val, regW_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embHC410_apply (i : Fin (n' + ℓ + ps.ancHC n')) :
    embHC410 (ps := ps) (r := r) (n := n) (M := M) i =
      if h0 : i.1 < n' then regQ ⟨i.1, h0⟩
      else if h1 : i.1 < n' + ℓ then regW ⟨i.1 - n', by omega⟩
      else regAnc ⟨i.1 - (n' + ℓ), by
        have _ := i.isLt
        have hle : ps.ancHC n' ≤ Amax := le_trans (le_max_left _ _) (le_max_right _ _)
        omega⟩ := rfl

def embCN410 : Fin (1 + n + ps.ancCN n) ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 = 0 then wireNeg
    else if h1 : i.1 < 1 + n then regQ ⟨i.1 - 1, by omega⟩
    else regAnc ⟨i.1 - (1 + n), by
      have _ := i.isLt
      have hle : ps.ancCN n ≤ Amax :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;> simp only [wireNeg_val, regQ_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embCN410_apply (i : Fin (1 + n + ps.ancCN n)) :
    embCN410 (ps := ps) (r := r) (n := n) (M := M) i =
      if h0 : i.1 = 0 then wireNeg
      else if h1 : i.1 < 1 + n then regQ ⟨i.1 - 1, by omega⟩
      else regAnc ⟨i.1 - (1 + n), by
        have _ := i.isLt
        have hle : ps.ancCN n ≤ Amax :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
        omega⟩ := rfl

def embUTilde410 : Fin (1 + ℓ + qw + ps.ancUTilde M n') ↪ Fin M' :=
  ⟨fun i =>
    if h0 : i.1 = 0 then wireFC
    else if h1 : i.1 < 1 + ℓ then regW ⟨i.1 - 1, by omega⟩
    else if h2 : i.1 < 1 + ℓ + qw then regMode ⟨i.1 - (1 + ℓ), by omega⟩
    else regAnc ⟨i.1 - (1 + ℓ + qw), by
      have _ := i.isLt
      have hle : ps.ancUTilde M n' ≤ Amax :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_max_right _ _)))
      omega⟩, by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only at hv
    split_ifs at hv <;>
      simp only [wireFC_val, regW_val, regMode_val, regAnc_val] at hv <;> ext <;> omega⟩

@[simp] lemma embUTilde410_apply (i : Fin (1 + ℓ + qw + ps.ancUTilde M n')) :
    embUTilde410 (ps := ps) (r := r) (n := n) (M := M) i =
      if h0 : i.1 = 0 then wireFC
      else if h1 : i.1 < 1 + ℓ then regW ⟨i.1 - 1, by omega⟩
      else if h2 : i.1 < 1 + ℓ + qw then regMode ⟨i.1 - (1 + ℓ), by omega⟩
      else regAnc ⟨i.1 - (1 + ℓ + qw), by
        have _ := i.isLt
        have hle : ps.ancUTilde M n' ≤ Amax :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_max_right _ _)))
        omega⟩ := rfl

/-! ### `ctrl0XCirc410` (XOR `pat` into `regC` iff `mode = modeKet M 0`) -/

def cnotGateAt410 (u v : Fin M') (huv : u ≠ v) : GateApp gates12 M' :=
  ⟨Gate.ofMatrix2 cnotMat, gate_ofMatrix2_mem_gates12 cnotMat_mem_unitaryGroup, embPair410 u v huv⟩

def idGateAt410 (w : Fin M') : GateApp gates12 M' :=
  ⟨Gate.ofMatrix1 1, gate_ofMatrix1_mem_gates12 (Submonoid.one_mem _), singleWireEmb410 w⟩

noncomputable def ctrl0XStepGate410 (pat : Qubits r) (j : Fin r) : GateApp gates12 M' :=
  ⟨Gate.ofMatrix2 (if pat j then cnotMat else 1),
    gate_ofMatrix2_mem_gates12 (by split_ifs; exact cnotMat_mem_unitaryGroup; exact Submonoid.one_mem _),
    embPair410 wirePub (regC j) (by
      intro h; have hv := congrArg Fin.val h
      simp only [wirePub_val, regC_val] at hv; have := j.isLt; omega)⟩

noncomputable def ctrl0XCirc410 (pat : Qubits r) : Circuit gates12 M' :=
  embedCircuit embEqPub (ps.eqCirc qw (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
  List.ofFn (ctrl0XStepGate410 pat) ++
  embedCircuit embEqPub (ps.eqCirc qw (fun _ => false) pauliX pauliX_mem_unitaryGroup)

lemma ctrl0XCirc410_length (pat : Qubits r) :
    (ctrl0XCirc410 (ps := ps) (r := r) (n := n) (M := M) pat).length =
      2 * (ps.eqCirc qw (fun _ => false) pauliX pauliX_mem_unitaryGroup).length + r := by
  simp [ctrl0XCirc410, embedCircuit]; ring

lemma act_eqPubCirc (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) :
    act (embedCircuit (embEqPub (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc qw (fun _ => false) pauliX pauliX_mem_unitaryGroup)).unitary
        (ket (packState410 c mode q w fc fh fq pub neg (fun _ => false))) =
      ket (packState410 c mode q w fc fh fq (if mode = fun _ => false then !pub else pub) neg (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg (fun _ => false)
  let z' := packState410 (ps := ps) (r := r) (n := n) (M := M)
    c mode q w fc fh fq (if mode = fun _ => false then !pub else pub) neg (fun _ => false)
  let x' := packEq qw (ps.ancEq qw) mode (if mode = fun _ => false then !pub else pub) (fun _ => false)
  refine act_embedOp_basis_map embEqPub _ z x' ?_ z' ?_ ?_
  · have hcomp : z ∘ embEqPub (ps := ps) (r := r) (n := n) (M := M) =
        packEq qw (ps.ancEq qw) mode pub (fun _ => false) := by
      funext i
      by_cases h0 : i.1 < qw
      · rw [Function.comp_apply, embEqPub_apply, dif_pos h0]; dsimp only [z]
        rw [packState410_Mode, packEq, dif_pos h0]
      · by_cases h1 : i.1 = qw
        · rw [Function.comp_apply, embEqPub_apply, dif_neg h0, dif_pos h1]; dsimp only [z]
          rw [packState410_Pub, packEq, dif_neg h0, dif_pos h1]
        · rw [Function.comp_apply, embEqPub_apply, dif_neg h0, dif_neg h1]; dsimp only [z]
          rw [packState410_Anc, packEq, dif_neg h0, dif_neg h1]
    rw [hcomp, ps.eq_act]
    by_cases hm0 : mode = (fun _ => false)
    · rw [if_pos hm0, Fintype.sum_bool]
      cases pub <;> simp [x', hm0, pauliX]
    · rw [if_neg hm0]; simp [x', hm0]
  · funext i
    by_cases h0 : i.1 < qw
    · rw [Function.comp_apply, embEqPub_apply, dif_pos h0]; dsimp only [z', x']
      rw [packState410_Mode, packEq, dif_pos h0]
    · by_cases h1 : i.1 = qw
      · rw [Function.comp_apply, embEqPub_apply, dif_neg h0, dif_pos h1]; dsimp only [z', x']
        rw [packState410_Pub, packEq, dif_neg h0, dif_pos h1]
      · rw [Function.comp_apply, embEqPub_apply, dif_neg h0, dif_neg h1]; dsimp only [z', x']
        rw [packState410_Anc, packEq, dif_neg h0, dif_neg h1]
  · intro i hi
    exact packState410_eq_of_flag (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun h => False.elim (hi ⟨⟨qw, by omega⟩, by simp [embEqPub_apply, h.symm]⟩)) (fun _ => rfl)

private lemma act_ctrl0XStepGate410 (pat : Qubits r) (j : Fin r) (c : Qubits r) (mode : Qubits qw)
    (q : Qubits n') (w : Qubits ℓ) (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    act (embedOp (ctrl0XStepGate410 (ps := ps) (r := r) (n := n) (M := M) pat j).gate.mat
          (ctrl0XStepGate410 pat j).wires)
        (ket (packState410 c mode q w fc fh fq pub neg a)) =
      ket (packState410
        (fun i => if i = j then (if pub then xor (c i) (pat j) else c i) else c i)
        mode q w fc fh fq pub neg a) := by
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg a
  let z' := packState410 (ps := ps) (r := r) (n := n) (M := M)
    (fun i => if i = j then (if pub then xor (c i) (pat j) else c i) else c i)
    mode q w fc fh fq pub neg a
  have hne : (wirePub (ps := ps) (r := r) (n := n) (M := M)) ≠ regC j := by
    intro h; have hv := congrArg Fin.val h
    simp only [wirePub_val, regC_val] at hv; have := j.isLt; omega
  refine act_embedOp_basis_map (embPair410 wirePub (regC j) hne)
    (ctrl0XStepGate410 pat j).gate.mat z (z' ∘ embPair410 wirePub (regC j) hne) ?_ z' rfl ?_
  · ext x
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ctrl0XStepGate410, Gate.ofMatrix2,
      Matrix.submatrix_apply, ket, PiLp.single_apply]
    rw [Finset.sum_eq_single (z ∘ embPair410 wirePub (regC j) hne)]
    · simp only [↓reduceIte, mul_one]
      have h0 : (z ∘ embPair410 wirePub (regC j) hne) 0 = pub := by
        simp [z, embPair410_apply, packState410_Pub]
      have h1 : (z ∘ embPair410 wirePub (regC j) hne) 1 = c j := by
        simp [z, embPair410_apply, packState410_C]
      have hz'0 : (z' ∘ embPair410 wirePub (regC j) hne) 0 = pub := by
        simp [z', embPair410_apply, packState410_Pub]
      have hz'1 : (z' ∘ embPair410 wirePub (regC j) hne) 1 = if pub then xor (c j) (pat j) else c j := by
        simp [z', embPair410_apply, packState410_C]
      have heq_x : (x = z' ∘ embPair410 wirePub (regC j) hne) ↔
          (x 0 = pub ∧ x 1 = (if pub then xor (c j) (pat j) else c j)) := by
        constructor
        · intro h; rw [h, hz'0, hz'1]; exact ⟨rfl, rfl⟩
        · rintro ⟨hx0, hx1⟩; funext i; fin_cases i
          · dsimp; exact hx0.trans hz'0.symm
          · dsimp; exact hx1.trans hz'1.symm
      by_cases hpat : pat j = true
      · have heq_x' : (x = z' ∘ embPair410 wirePub (regC j) hne) ↔
            (x 0 = pub ∧ x 1 = (if pub then !(c j) else c j)) := by
          simpa [hpat] using heq_x
        simp only [hpat, ↓reduceIte, cnotMat, Matrix.of_apply, h0, h1]
        by_cases hx : x = z' ∘ embPair410 wirePub (regC j) hne
        · rw [if_pos hx, if_pos (heq_x'.mp hx)]
        · rw [if_neg hx, if_neg (fun h => hx (heq_x'.mpr h))]
      · have hpf : pat j = false := Bool.eq_false_iff.mpr hpat
        simp only [hpf, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply, Prod.mk.injEq, h0, h1]
        by_cases hx : x = z' ∘ embPair410 wirePub (regC j) hne
        · rw [if_pos hx]; have hx' := heq_x.mp hx; simp [hpf, hx']
        · rw [if_neg hx, if_neg]; rintro ⟨hx0, hx1⟩; apply hx; apply heq_x.mpr; simp [hpf, hx0, hx1]
    · intro u _ hu; simp [hu]
    · simp
  · intro i hi
    refine packState410_eq_of_C _ c mode q w fc fh fq pub neg a i fun k hk => ?_
    by_cases hkj : k = j
    · subst hkj; exact absurd hk (fun h => hi ⟨1, by simp [embPair410_apply, h]⟩)
    · simp [hkj]

lemma act_ctrl0XCirc410 (pat : Qubits r) (c : Qubits r) (mode : Qubits qw)
    (q : Qubits n') (w : Qubits ℓ) (fc fh fq neg : Bool) :
    act (ctrl0XCirc410 (ps := ps) (r := r) (n := n) (M := M) pat).unitary
        (ket (packState410 c mode q w fc fh fq false neg (fun _ => false))) =
      ket (packState410
        (fun i => if mode = fun _ => false then xor (c i) (pat i) else c i)
        mode q w fc fh fq false neg (fun _ => false)) := by
  have hmid : ∀ (pub : Bool),
      act (Circuit.unitary (List.ofFn (ctrl0XStepGate410 (ps := ps) (r := r) (n := n) (M := M) pat)))
          (ket (packState410 c mode q w fc fh fq pub neg (fun _ => false))) =
        ket (packState410 (fun i => if pub then xor (c i) (pat i) else c i)
          mode q w fc fh fq pub neg (fun _ => false)) := by
    intro pub
    have hpref : ∀ (k : ℕ) (hk : k ≤ r),
        act (Circuit.unitary (List.ofFn fun j : Fin k => ctrl0XStepGate410 (ps := ps) (r := r) (n := n) (M := M)
            pat (Fin.castLE hk j)))
          (ket (packState410 c mode q w fc fh fq pub neg (fun _ => false))) =
        ket (packState410
          (fun i => if i.1 < k then (if pub then xor (c i) (pat i) else c i) else c i)
          mode q w fc fh fq pub neg (fun _ => false)) := by
      intro k
      induction k with
      | zero => intro _; simp [Circuit.unitary, act_one_vec]
      | succ k ih =>
        intro hk
        have hk_le : k ≤ r := Nat.le_of_lt hk
        have hfn : (List.ofFn fun j : Fin (k + 1) => ctrl0XStepGate410 (ps := ps) (r := r) (n := n) (M := M)
              pat (Fin.castLE hk j)) =
            (List.ofFn fun j : Fin k => ctrl0XStepGate410 (ps := ps) (r := r) (n := n) (M := M)
              pat (Fin.castLE hk_le j)) ++
            [ctrl0XStepGate410 (ps := ps) (r := r) (n := n) (M := M) pat ⟨k, hk⟩] := by
          rw [List.ofFn_succ', List.concat_eq_append]; rfl
        have hunit : Circuit.unitary (List.ofFn fun j : Fin (k + 1) =>
              ctrl0XStepGate410 (ps := ps) (r := r) (n := n) (M := M) pat (Fin.castLE hk j)) =
            embedOp (ctrl0XStepGate410 pat ⟨k, hk⟩).gate.mat (ctrl0XStepGate410 pat ⟨k, hk⟩).wires *
            Circuit.unitary (List.ofFn fun j : Fin k => ctrl0XStepGate410 (ps := ps) (r := r) (n := n) (M := M)
              pat (Fin.castLE hk_le j)) := by
          rw [hfn]; simp [Circuit.unitary]
        rw [hunit, act_mul, ih hk_le, act_ctrl0XStepGate410]
        congr 1; ext idx
        by_cases h0 : idx.1 < r
        · simp only [packState410, h0, ↓reduceDIte]
          by_cases hik : idx.1 < k
          · have hik1 : idx.1 < k + 1 := by omega
            have hne : (⟨idx.1, h0⟩ : Fin r) ≠ ⟨k, hk⟩ := fun h => by
              have := congrArg Fin.val h; dsimp at this; omega
            simp [hik, hik1, hne]
          · by_cases hiek : idx.1 = k
            · have hlt : idx.1 < k + 1 := by omega
              have heq : (⟨idx.1, h0⟩ : Fin r) = ⟨k, hk⟩ := Fin.ext hiek
              simp [hik, hlt, heq]
            · have hn1 : ¬ idx.1 < k + 1 := by omega
              have hne : (⟨idx.1, h0⟩ : Fin r) ≠ ⟨k, hk⟩ := fun h => hiek (congrArg Fin.val h)
              simp [hik, hn1, hne]
        · simp [packState410, h0]
    simpa [Fin.isLt] using hpref r le_rfl
  simp only [ctrl0XCirc410, circuit_unitary_append, act_mul]
  rw [act_eqPubCirc]
  by_cases hm0 : mode = (fun _ => false)
  · have hmid' := hmid true
    rw [hm0] at hmid'
    simp only [hm0, ↓reduceIte, Bool.not_false]
    rw [hmid', act_eqPubCirc]
    simp
  · simp only [hm0, ↓reduceIte]
    rw [hmid false, act_eqPubCirc]
    simp [hm0]

/-! ### `hadamardLayerC410` (parallel `H` on all `r` clock qubits) -/

noncomputable def hadamardGateAt410 (w : Fin M') : GateApp gates12 M' :=
  ⟨Gate.ofMatrix1 hadamard, gate_ofMatrix1_mem_gates12 hadamard_mem_unitaryGroup, singleWireEmb410 w⟩

noncomputable def hadamardLayerC410 : Circuit gates12 M' :=
  List.ofFn fun j : Fin r => hadamardGateAt410 (regC j)

lemma hadamardLayerC410_length : (hadamardLayerC410 (ps := ps) (r := r) (n := n) (M := M)).length = r := by
  simp [hadamardLayerC410]

lemma hadamardLayerC410_depth_le_one {a : Fin 1 → ℕ} :
    nonOracleDepth ((hadamardLayerC410 (ps := ps) (r := r) (n := n) (M := M)).map OracleStep.gate :
      OracleCircuit gates12 a M') ≤ 1 := by
  refine nonOracleDepth_disjoint_gates_le_one _ ?_
  rw [hadamardLayerC410, List.pairwise_ofFn]
  intro i j hij
  rw [Set.disjoint_left]
  rintro x ⟨_, rfl⟩ ⟨_, hx⟩
  simp only [hadamardGateAt410] at hx
  exact hij.ne (regC.injective hx.symm)

private def qubitsSnocEquiv (m : ℕ) : Qubits (m + 1) ≃ Qubits m × Bool where
  toFun z := (Fin.init z, z (Fin.last m))
  invFun p := Fin.snoc (α := fun _ => Bool) p.1 p.2
  left_inv z := Fin.snoc_init_self z
  right_inv p := by ext <;> simp

noncomputable def natToBitsLSBEquiv (r : ℕ) : Fin (2 ^ r) ≃ Qubits r :=
  Equiv.ofBijective (fun c => natToBitsLSB r c.1)
    ((Fintype.bijective_iff_injective_and_card (fun c : Fin (2 ^ r) => natToBitsLSB r c.1)).2
      ⟨fun c₁ c₂ h => Fin.ext (natToBitsLSB_inj_of_lt c₁.isLt c₂.isLt h), by simp⟩)

lemma act_hadamardGateAt410_false (j : Fin r) (c : Qubits r) (hc : c j = false)
    (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ) (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    act (embedOp (hadamardGateAt410 (ps := ps) (r := r) (n := n) (M := M) (regC j)).gate.mat
          (hadamardGateAt410 (regC j)).wires)
        (ket (packState410 c mode q w fc fh fq pub neg a)) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        (ket (packState410 (Function.update c j false) mode q w fc fh fq pub neg a) +
         ket (packState410 (Function.update c j true) mode q w fc fh fq pub neg a)) := by
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg a
  let z' : Bool → Qubits M' := fun b =>
    packState410 (ps := ps) (r := r) (n := n) (M := M) (Function.update c j b) mode q w fc fh fq pub neg a
  change act (embedOp (Gate.ofMatrix1 hadamard).mat (singleWireEmb410 (regC j))) (ket z) = _
  trans (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ket (z' true) + ket (z' false))
  · rw [smul_add]
    have hsum_eq : (∑ b : Bool, (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (z' b)) =
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (z' true) +
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (z' false) := Fintype.sum_bool _
    rw [← hsum_eq]
    refine act_embedOp_basis_sum (singleWireEmb410 (regC j))
      (Gate.ofMatrix1 hadamard).mat z (fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ))
      (fun b _ => b) z' ?_ ?_ ?_
    · ext u
      have hz0 : (z ∘ singleWireEmb410 (ps := ps) (r := r) (n := n) (M := M) (regC j)) = fun _ : Fin 1 => false := by
        funext i; simp only [Function.comp_apply, singleWireEmb410_apply, z, packState410_C, hc]
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
          subst huf; simp [hadamard, hne.symm]
        · have hut : u = fun _ => true := funext fun i => by fin_cases i; exact h0
          subst hut; simp [hadamard, hne]
      · intro x _ hx; simp [hx]
      · simp
    · intro b; funext i
      simp only [Function.comp_apply, z', singleWireEmb410_apply, packState410_C, Function.update_self]
    · intro b i hi
      refine packState410_eq_of_C _ c mode q w fc fh fq pub neg a i fun k hk => ?_
      by_cases hkj : k = j
      · subst hkj; exact absurd hk (fun h => hi ⟨0, by simp [singleWireEmb410_apply, h]⟩)
      · simp [hkj]
  · rw [add_comm]

lemma act_hadamardLayerC410 :
    act (hadamardLayerC410 (ps := ps) (r := r) (n := n) (M := M)).unitary (zeroKet M') =
      (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
        ∑ c : Fin (2 ^ r), ket (coreEmbHom410 (natToBitsLSB r c.1, fun _ => false, fun _ => false)) := by
  let extZero : (k : ℕ) → k ≤ r → Qubits k → Qubits r := fun k _ s i =>
    if hi : i.1 < k then s ⟨i.1, hi⟩ else false
  have hpref : ∀ (k : ℕ) (hk : k ≤ r),
      act (Circuit.unitary (List.ofFn fun j : Fin k => hadamardGateAt410 (ps := ps) (r := r) (n := n) (M := M)
          (regC (Fin.castLE hk j)))) (zeroKet M') =
        (((Real.sqrt 2)⁻¹ ^ k : ℝ) : ℂ) •
          ∑ s : Qubits k, ket (packState410 (ps := ps) (extZero k hk s) (fun _ => false) (fun _ => false)
            (fun _ => false) false false false false false (fun _ => false)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hext : ∀ s : Qubits 0, extZero 0 hk s = fun _ => false := fun s => by
        funext i; simp [extZero]
      simp only [Circuit.unitary, List.ofFn_zero, List.map_nil, List.reverse_nil, List.prod_nil,
        act_one_vec, pow_zero, Complex.ofReal_one, one_smul]
      rw [Fintype.sum_unique, hext _, packState410_zero]
      rfl
    | succ k ih =>
      intro hk
      have hk_le : k ≤ r := Nat.le_of_lt hk
      have hfn : (List.ofFn fun j : Fin (k + 1) => hadamardGateAt410 (ps := ps) (r := r) (n := n) (M := M)
            (regC (Fin.castLE hk j))) =
          (List.ofFn fun j : Fin k => hadamardGateAt410 (ps := ps) (r := r) (n := n) (M := M)
            (regC (Fin.castLE hk_le j))) ++
          [hadamardGateAt410 (ps := ps) (r := r) (n := n) (M := M) (regC ⟨k, hk⟩)] := by
        rw [List.ofFn_succ', List.concat_eq_append]; rfl
      have hunit : Circuit.unitary (List.ofFn fun j : Fin (k + 1) =>
            hadamardGateAt410 (ps := ps) (r := r) (n := n) (M := M) (regC (Fin.castLE hk j))) =
          embedOp (hadamardGateAt410 (regC ⟨k, hk⟩)).gate.mat (hadamardGateAt410 (regC ⟨k, hk⟩)).wires *
          Circuit.unitary (List.ofFn fun j : Fin k =>
            hadamardGateAt410 (ps := ps) (r := r) (n := n) (M := M) (regC (Fin.castLE hk_le j))) := by
        rw [hfn]; simp [Circuit.unitary]
      rw [hunit, act_mul, ih hk_le, act_smul, act_sum]
      have hterm : ∀ s : Qubits k,
          act (embedOp (hadamardGateAt410 (ps := ps) (r := r) (n := n) (M := M) (regC ⟨k, hk⟩)).gate.mat
                (hadamardGateAt410 (regC ⟨k, hk⟩)).wires)
              (ket (packState410 (ps := ps) (extZero k hk_le s) (fun _ => false) (fun _ => false)
                (fun _ => false) false false false false false (fun _ => false))) =
            (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
              (ket (packState410 (ps := ps) (extZero (k + 1) hk (Fin.snoc s false)) (fun _ => false) (fun _ => false)
                  (fun _ => false) false false false false false (fun _ => false)) +
               ket (packState410 (ps := ps) (extZero (k + 1) hk (Fin.snoc s true)) (fun _ => false) (fun _ => false)
                  (fun _ => false) false false false false false (fun _ => false))) := by
        intro s
        have hfalse : extZero k hk_le s ⟨k, hk⟩ = false := by simp [extZero]
        rw [act_hadamardGateAt410_false ⟨k, hk⟩ (extZero k hk_le s) hfalse]
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
        (fun p : Qubits k × Bool => ket (packState410 (ps := ps) (extZero (k + 1) hk (Fin.snoc p.1 p.2))
          (fun _ => false) (fun _ => false) (fun _ => false) false false false false false (fun _ => false)))
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
  simp only [hadamardLayerC410] at *
  have hcirc : (List.ofFn fun j : Fin r => hadamardGateAt410 (ps := ps) (r := r) (n := n) (M := M) (regC j)) =
      (List.ofFn fun j : Fin r => hadamardGateAt410 (ps := ps) (r := r) (n := n) (M := M)
        (regC (Fin.castLE le_rfl j))) := rfl
  rw [hcirc, hfull, hsqrt]
  congr 1
  simp_rw [hext_full]
  symm
  exact Fintype.sum_equiv (natToBitsLSBEquiv r) _
    (fun s : Qubits r => ket (packState410 (ps := ps) s (fun _ => false) (fun _ => false)
      (fun _ => false) false false false false false (fun _ => false)))
    (fun _ => rfl)

/-! ### `fqComputeCirc410`, `hHatCirc410`, and `uBodyCirc410` -/

noncomputable def fqComputeCirc410 : Circuit gates12 M' :=
  embedCircuit embEqFQC (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
  embedCircuit embEqFQCMode (ps.eqCirc (r + qw) (fun _ => false) pauliX pauliX_mem_unitaryGroup)

lemma fqComputeCirc410_length :
    (fqComputeCirc410 (ps := ps) (r := r) (n := n) (M := M)).length =
      (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup).length +
      (ps.eqCirc (r + qw) (fun _ => false) pauliX pauliX_mem_unitaryGroup).length := by
  simp [fqComputeCirc410, embedCircuit]

lemma act_eqFQCCirc410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) :
    act (embedCircuit (embEqFQC (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).unitary
        (ket (packState410 c mode q w fc fh fq pub neg (fun _ => false))) =
      ket (packState410 c mode q w fc fh (if c = fun _ => false then !fq else fq) pub neg (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg (fun _ => false)
  let z' := packState410 (ps := ps) (r := r) (n := n) (M := M)
    c mode q w fc fh (if c = fun _ => false then !fq else fq) pub neg (fun _ => false)
  let x' := packEq r (ps.ancEq r) c (if c = fun _ => false then !fq else fq) (fun _ => false)
  refine act_embedOp_basis_map embEqFQC _ z x' ?_ z' ?_ ?_
  · have hcomp : z ∘ embEqFQC (ps := ps) (r := r) (n := n) (M := M) =
        packEq r (ps.ancEq r) c fq (fun _ => false) := by
      funext i
      by_cases h0 : i.1 < r
      · rw [Function.comp_apply, embEqFQC_apply, dif_pos h0]; dsimp only [z]
        rw [packState410_C, packEq, dif_pos h0]
      · by_cases h1 : i.1 = r
        · rw [Function.comp_apply, embEqFQC_apply, dif_neg h0, dif_pos h1]; dsimp only [z]
          rw [packState410_FQ, packEq, dif_neg h0, dif_pos h1]
        · rw [Function.comp_apply, embEqFQC_apply, dif_neg h0, dif_neg h1]; dsimp only [z]
          rw [packState410_Anc, packEq, dif_neg h0, dif_neg h1]
    rw [hcomp, ps.eq_act]
    by_cases hc0 : c = (fun _ => false)
    · rw [if_pos hc0, Fintype.sum_bool]
      cases fq <;> simp [x', hc0, pauliX]
    · rw [if_neg hc0]; simp [x', hc0]
  · funext i
    by_cases h0 : i.1 < r
    · rw [Function.comp_apply, embEqFQC_apply, dif_pos h0]; dsimp only [z', x']
      rw [packState410_C, packEq, dif_pos h0]
    · by_cases h1 : i.1 = r
      · rw [Function.comp_apply, embEqFQC_apply, dif_neg h0, dif_pos h1]; dsimp only [z', x']
        rw [packState410_FQ, packEq, dif_neg h0, dif_pos h1]
      · rw [Function.comp_apply, embEqFQC_apply, dif_neg h0, dif_neg h1]; dsimp only [z', x']
        rw [packState410_Anc, packEq, dif_neg h0, dif_neg h1]
  · intro i hi
    exact packState410_eq_of_flag (fun _ => rfl) (fun _ => rfl)
      (fun h => False.elim (hi ⟨⟨r, by omega⟩, by simp [embEqFQC_apply, h.symm]⟩))
      (fun _ => rfl) (fun _ => rfl)

lemma act_eqFQCModeCirc410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) :
    act (embedCircuit (embEqFQCMode (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc (r + qw) (fun _ => false) pauliX pauliX_mem_unitaryGroup)).unitary
        (ket (packState410 c mode q w fc fh fq pub neg (fun _ => false))) =
      ket (packState410 c mode q w fc fh
        (if c = (fun _ => false) ∧ mode = (fun _ => false) then !fq else fq) pub neg (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let addr : Qubits (r + qw) := fun i => if h : i.1 < r then c ⟨i.1, h⟩ else mode ⟨i.1 - r, by omega⟩
  have haddr : (addr = fun _ => false) ↔ (c = (fun _ => false) ∧ mode = (fun _ => false)) := by
    constructor
    · intro h
      refine ⟨funext fun i => ?_, funext fun i => ?_⟩
      · have hi := congrFun h ⟨i.1, by omega⟩; simpa [addr, i.isLt] using hi
      · have hi := congrFun h ⟨r + i.1, by omega⟩
        simp only [addr, show ¬ (r + i.1 < r) by omega, ↓reduceDIte] at hi
        simpa using hi
    · rintro ⟨hc, hm⟩; funext i
      by_cases hi : i.1 < r
      · simp [addr, hi, hc]
      · simp [addr, hi, hm]
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg (fun _ => false)
  let z' := packState410 (ps := ps) (r := r) (n := n) (M := M)
    c mode q w fc fh (if c = (fun _ => false) ∧ mode = (fun _ => false) then !fq else fq)
    pub neg (fun _ => false)
  let x' := packEq (r + qw) (ps.ancEq (r + qw)) addr
    (if c = (fun _ => false) ∧ mode = (fun _ => false) then !fq else fq) (fun _ => false)
  refine act_embedOp_basis_map embEqFQCMode _ z x' ?_ z' ?_ ?_
  · have hcomp : z ∘ embEqFQCMode (ps := ps) (r := r) (n := n) (M := M) =
        packEq (r + qw) (ps.ancEq (r + qw)) addr fq (fun _ => false) := by
      funext i
      by_cases h0 : i.1 < r
      · have h0' : i.1 < r + qw := by omega
        rw [Function.comp_apply, embEqFQCMode_apply, dif_pos h0]; dsimp only [z]
        rw [packState410_C, packEq, dif_pos h0']; simp [addr, h0]
      · by_cases h1 : i.1 < r + qw
        · rw [Function.comp_apply, embEqFQCMode_apply, dif_neg h0, dif_pos h1]; dsimp only [z]
          rw [packState410_Mode, packEq, dif_pos h1]; simp [addr, h0]
        · by_cases h2 : i.1 = r + qw
          · rw [Function.comp_apply, embEqFQCMode_apply, dif_neg h0, dif_neg h1, dif_pos h2]
            dsimp only [z]; rw [packState410_FQ, packEq, dif_neg h1, dif_pos h2]
          · rw [Function.comp_apply, embEqFQCMode_apply, dif_neg h0, dif_neg h1, dif_neg h2]
            dsimp only [z]; rw [packState410_Anc, packEq, dif_neg h1, dif_neg h2]
    rw [hcomp, ps.eq_act]
    by_cases hm : c = (fun _ => false) ∧ mode = (fun _ => false)
    · rw [if_pos (haddr.mpr hm), Fintype.sum_bool]
      cases fq <;> simp [x', hm, pauliX]
    · rw [if_neg (fun h => hm (haddr.mp h))]; simp [x', hm]
  · funext i
    by_cases h0 : i.1 < r
    · have h0' : i.1 < r + qw := by omega
      rw [Function.comp_apply, embEqFQCMode_apply, dif_pos h0]; dsimp only [z', x']
      rw [packState410_C, packEq, dif_pos h0']; simp [addr, h0]
    · by_cases h1 : i.1 < r + qw
      · rw [Function.comp_apply, embEqFQCMode_apply, dif_neg h0, dif_pos h1]; dsimp only [z', x']
        rw [packState410_Mode, packEq, dif_pos h1]; simp [addr, h0]
      · by_cases h2 : i.1 = r + qw
        · rw [Function.comp_apply, embEqFQCMode_apply, dif_neg h0, dif_neg h1, dif_pos h2]
          dsimp only [z', x']; rw [packState410_FQ, packEq, dif_neg h1, dif_pos h2]
        · rw [Function.comp_apply, embEqFQCMode_apply, dif_neg h0, dif_neg h1, dif_neg h2]
          dsimp only [z', x']; rw [packState410_Anc, packEq, dif_neg h1, dif_neg h2]
  · intro i hi
    exact packState410_eq_of_flag (fun _ => rfl) (fun _ => rfl)
      (fun h => False.elim (hi ⟨⟨r + qw, by omega⟩, by simp [embEqFQCMode_apply, h.symm]⟩))
      (fun _ => rfl) (fun _ => rfl)

lemma act_fqComputeCirc410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) :
    act (fqComputeCirc410 (ps := ps) (r := r) (n := n) (M := M)).unitary
        (ket (packState410 c mode q w fc fh fq pub neg (fun _ => false))) =
      ket (packState410 c mode q w fc fh
        (if c = (fun _ => false) ∧ mode ≠ (fun _ => false) then !fq else fq)
        pub neg (fun _ => false)) := by
  simp only [fqComputeCirc410, circuit_unitary_append, act_mul]
  rw [act_eqFQCCirc410, act_eqFQCModeCirc410]
  by_cases hc : c = (fun _ => false) <;> by_cases hm : mode = (fun _ => false) <;>
    simp [hc, hm]

lemma act_eqFCCirc410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) :
    act (embedCircuit (embEqFC (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).unitary
        (ket (packState410 c mode q w fc fh fq pub neg (fun _ => false))) =
      ket (packState410 c mode q w (if c = fun _ => false then !fc else fc) fh fq pub neg (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg (fun _ => false)
  let z' := packState410 (ps := ps) (r := r) (n := n) (M := M)
    c mode q w (if c = fun _ => false then !fc else fc) fh fq pub neg (fun _ => false)
  let x' := packEq r (ps.ancEq r) c (if c = fun _ => false then !fc else fc) (fun _ => false)
  refine act_embedOp_basis_map embEqFC _ z x' ?_ z' ?_ ?_
  · have hcomp : z ∘ embEqFC (ps := ps) (r := r) (n := n) (M := M) =
        packEq r (ps.ancEq r) c fc (fun _ => false) := by
      funext i
      by_cases h0 : i.1 < r
      · rw [Function.comp_apply, embEqFC_apply, dif_pos h0]; dsimp only [z]
        rw [packState410_C, packEq, dif_pos h0]
      · by_cases h1 : i.1 = r
        · rw [Function.comp_apply, embEqFC_apply, dif_neg h0, dif_pos h1]; dsimp only [z]
          rw [packState410_FC, packEq, dif_neg h0, dif_pos h1]
        · rw [Function.comp_apply, embEqFC_apply, dif_neg h0, dif_neg h1]; dsimp only [z]
          rw [packState410_Anc, packEq, dif_neg h0, dif_neg h1]
    rw [hcomp, ps.eq_act]
    by_cases hc0 : c = (fun _ => false)
    · rw [if_pos hc0, Fintype.sum_bool]
      cases fc <;> simp [x', hc0, pauliX]
    · rw [if_neg hc0]; simp [x', hc0]
  · funext i
    by_cases h0 : i.1 < r
    · rw [Function.comp_apply, embEqFC_apply, dif_pos h0]; dsimp only [z', x']
      rw [packState410_C, packEq, dif_pos h0]
    · by_cases h1 : i.1 = r
      · rw [Function.comp_apply, embEqFC_apply, dif_neg h0, dif_pos h1]; dsimp only [z', x']
        rw [packState410_FC, packEq, dif_neg h0, dif_pos h1]
      · rw [Function.comp_apply, embEqFC_apply, dif_neg h0, dif_neg h1]; dsimp only [z', x']
        rw [packState410_Anc, packEq, dif_neg h0, dif_neg h1]
  · intro i hi
    exact packState410_eq_of_flag (fun h => False.elim (hi ⟨⟨r, by omega⟩, by simp [embEqFC_apply, h.symm]⟩))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

def patFCMode0 (M : ℕ) : Qubits (1 + qW M) :=
  fun i => if i.1 = 0 then true else false

noncomputable def hHatCirc410 : Circuit gates12 M' :=
  let cnotFCH : GateApp gates12 M' := cnotGateAt410 wireFC wireFH (by
    intro h; have hv := congrArg Fin.val h; simp only [wireFC_val, wireFH_val] at hv; omega)
  let eqFH := embedCircuit (embEqFHMode0 (ps := ps) (r := r) (n := n) (M := M))
    (ps.eqCirc (1 + qw) (patFCMode0 M) pauliX pauliX_mem_unitaryGroup)
  let ch := embedCircuit (embCH410 (ps := ps) (r := r) (n := n) (M := M)) (ps.chCirc n')
  [cnotFCH] ++ eqFH ++ ch ++ eqFH ++ [cnotFCH]

lemma hHatCirc410_length :
    (hHatCirc410 (ps := ps) (r := r) (n := n) (M := M)).length =
      2 + 2 * (ps.eqCirc (1 + qw) (patFCMode0 M) pauliX pauliX_mem_unitaryGroup).length +
      (ps.chCirc n').length := by
  simp [hHatCirc410, embedCircuit]; ring

lemma act_cnotFCH (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    act (embedOp (cnotGateAt410 (ps := ps) (r := r) (n := n) (M := M) wireFC wireFH (by
            intro h; have hv := congrArg Fin.val h; simp only [wireFC_val, wireFH_val] at hv; omega)).gate.mat
          (cnotGateAt410 wireFC wireFH (by
            intro h; have hv := congrArg Fin.val h; simp only [wireFC_val, wireFH_val] at hv; omega)).wires)
        (ket (packState410 c mode q w fc fh fq pub neg a)) =
      ket (packState410 c mode q w fc (xor fh fc) fq pub neg a) := by
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg a
  let z' := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc (xor fh fc) fq pub neg a
  have hne : (wireFC (ps := ps) (r := r) (n := n) (M := M)) ≠ wireFH := by
    intro h; have hv := congrArg Fin.val h; simp only [wireFC_val, wireFH_val] at hv; omega
  refine act_embedOp_basis_map (embPair410 wireFC wireFH hne)
    (cnotGateAt410 wireFC wireFH hne).gate.mat z (z' ∘ embPair410 wireFC wireFH hne) ?_ z' rfl ?_
  · ext x
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, cnotGateAt410, Gate.ofMatrix2,
      Matrix.submatrix_apply, ket, PiLp.single_apply]
    rw [Finset.sum_eq_single (z ∘ embPair410 wireFC wireFH hne)]
    · simp only [↓reduceIte, mul_one, cnotMat, Matrix.of_apply]
      have h0 : (z ∘ embPair410 wireFC wireFH hne) 0 = fc := by simp [z, embPair410_apply, packState410_FC]
      have h1 : (z ∘ embPair410 wireFC wireFH hne) 1 = fh := by simp [z, embPair410_apply, packState410_FH]
      have hz'0 : (z' ∘ embPair410 wireFC wireFH hne) 0 = fc := by simp [z', embPair410_apply, packState410_FC]
      have hz'1 : (z' ∘ embPair410 wireFC wireFH hne) 1 = xor fh fc := by simp [z', embPair410_apply, packState410_FH]
      have heq : (x = z' ∘ embPair410 wireFC wireFH hne) ↔ (x 0 = fc ∧ x 1 = xor fh fc) := by
        constructor
        · intro h; rw [h, hz'0, hz'1]; exact ⟨rfl, rfl⟩
        · rintro ⟨hx0, hx1⟩; funext i; fin_cases i
          · dsimp; exact hx0.trans hz'0.symm
          · dsimp; exact hx1.trans hz'1.symm
      rw [h0, h1]
      by_cases hx : x = z' ∘ embPair410 wireFC wireFH hne
      · rw [if_pos hx, if_pos]; obtain ⟨hx0, hx1⟩ := heq.mp hx; cases fc <;> simp [hx0, hx1]
      · rw [if_neg hx, if_neg]; rintro ⟨hx0, hx1⟩; apply hx; apply heq.mpr; cases fc <;> simp [hx0, hx1]
    · intro u _ hu; simp [hu]
    · simp
  · intro i hi
    exact packState410_eq_of_flag (fun _ => rfl)
      (fun h => False.elim (hi ⟨1, by simp [embPair410_apply, h.symm]⟩))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

lemma act_eqFHMode0Circ (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) :
    act (embedCircuit (embEqFHMode0 (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc (1 + qw) (patFCMode0 M) pauliX pauliX_mem_unitaryGroup)).unitary
        (ket (packState410 c mode q w fc fh fq pub neg (fun _ => false))) =
      ket (packState410 c mode q w fc
        (if fc = true ∧ mode = fun _ => false then !fh else fh) fq pub neg (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let addr : Qubits (1 + qw) := fun i => if h : i.1 = 0 then fc else mode ⟨i.1 - 1, by omega⟩
  have haddr : (addr = patFCMode0 M) ↔ (fc = true ∧ mode = fun _ => false) := by
    constructor
    · intro h
      have h0 := congrFun h ⟨0, by omega⟩
      simp only [addr, ↓reduceDIte, patFCMode0, ↓reduceIte] at h0
      refine ⟨h0, funext fun j => ?_⟩
      have hj := congrFun h ⟨1 + j.1, by omega⟩
      simpa [addr, patFCMode0] using hj
    · rintro ⟨hfc, hm⟩; funext i
      by_cases hi : i.1 = 0
      · have hi0 : i = 0 := Fin.ext hi
        simp [addr, patFCMode0, hi0, hfc]
      · have hi0 : i ≠ 0 := fun h => hi (congrArg Fin.val h)
        simp [addr, patFCMode0, hi, hi0, hm]
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg (fun _ => false)
  let z' := packState410 (ps := ps) (r := r) (n := n) (M := M)
    c mode q w fc (if fc = true ∧ mode = fun _ => false then !fh else fh) fq pub neg (fun _ => false)
  let x' := packEq (1 + qw) (ps.ancEq (1 + qw)) addr
    (if fc = true ∧ mode = fun _ => false then !fh else fh) (fun _ => false)
  refine act_embedOp_basis_map embEqFHMode0 _ z x' ?_ z' ?_ ?_
  · have hcomp : z ∘ embEqFHMode0 (ps := ps) (r := r) (n := n) (M := M) =
        packEq (1 + qw) (ps.ancEq (1 + qw)) addr fh (fun _ => false) := by
      funext i
      by_cases h0 : i.1 = 0
      · have h0' : i.1 < 1 + qw := by omega
        rw [Function.comp_apply, embEqFHMode0_apply, dif_pos h0]; dsimp only [z]
        rw [packState410_FC, packEq, dif_pos h0']; simp [addr, h0]
      · by_cases h1 : i.1 < 1 + qw
        · rw [Function.comp_apply, embEqFHMode0_apply, dif_neg h0, dif_pos h1]; dsimp only [z]
          rw [packState410_Mode, packEq, dif_pos h1]; simp [addr, h0]
        · by_cases h2 : i.1 = 1 + qw
          · rw [Function.comp_apply, embEqFHMode0_apply, dif_neg h0, dif_neg h1, dif_pos h2]
            dsimp only [z]; rw [packState410_FH, packEq, dif_neg h1, dif_pos h2]
          · rw [Function.comp_apply, embEqFHMode0_apply, dif_neg h0, dif_neg h1, dif_neg h2]
            dsimp only [z]; rw [packState410_Anc, packEq, dif_neg h1, dif_neg h2]
    rw [hcomp, ps.eq_act]
    by_cases hm : fc = true ∧ mode = fun _ => false
    · rw [if_pos (haddr.mpr hm), Fintype.sum_bool]
      cases fh <;> simp [x', hm, pauliX]
    · rw [if_neg (fun h => hm (haddr.mp h))]; simp [x', hm]
  · funext i
    by_cases h0 : i.1 = 0
    · have h0' : i.1 < 1 + qw := by omega
      rw [Function.comp_apply, embEqFHMode0_apply, dif_pos h0]; dsimp only [z', x']
      rw [packState410_FC, packEq, dif_pos h0']; simp [addr, h0]
    · by_cases h1 : i.1 < 1 + qw
      · rw [Function.comp_apply, embEqFHMode0_apply, dif_neg h0, dif_pos h1]; dsimp only [z', x']
        rw [packState410_Mode, packEq, dif_pos h1]; simp [addr, h0]
      · by_cases h2 : i.1 = 1 + qw
        · rw [Function.comp_apply, embEqFHMode0_apply, dif_neg h0, dif_neg h1, dif_pos h2]
          dsimp only [z', x']; rw [packState410_FH, packEq, dif_neg h1, dif_pos h2]
        · rw [Function.comp_apply, embEqFHMode0_apply, dif_neg h0, dif_neg h1, dif_neg h2]
          dsimp only [z', x']; rw [packState410_Anc, packEq, dif_neg h1, dif_neg h2]
  · intro i hi
    exact packState410_eq_of_flag (fun _ => rfl)
      (fun h => False.elim (hi ⟨⟨1 + qw, by omega⟩, by simp [embEqFHMode0_apply, h.symm]⟩))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

lemma act_chQCirc410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) :
    act (embedCircuit (embCH410 (ps := ps) (r := r) (n := n) (M := M)) (ps.chCirc n')).unitary
        (ket (packState410 c mode q w fc fh fq pub neg (fun _ => false))) =
      if fh then
        ∑ q' : Qubits n', (hadamardN n' q' q) •
          ket (packState410 c mode q' w fc true fq pub neg (fun _ => false))
      else
        ket (packState410 c mode q w fc false fq pub neg (fun _ => false)) := by
  rw [embedCircuit_unitary]
  cases hfh : fh
  · simp only [Bool.false_eq_true, ↓reduceIte]
    let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc false fq pub neg (fun _ => false)
    let x' := packCH n' (ps.ancCH n') false q (fun _ => false)
    refine act_embedOp_basis_map embCH410 _ z x' ?_ z ?_ (fun _ _ => rfl)
    · have hcomp : z ∘ embCH410 (ps := ps) (r := r) (n := n) (M := M) =
          packCH n' (ps.ancCH n') false q (fun _ => false) := by
        funext i
        by_cases h0 : i.1 = 0
        · rw [Function.comp_apply, embCH410_apply, dif_pos h0]; dsimp only [z]
          rw [packState410_FH, packCH, dif_pos h0]
        · by_cases h1 : i.1 < 1 + n'
          · rw [Function.comp_apply, embCH410_apply, dif_neg h0, dif_pos h1]; dsimp only [z]
            rw [packState410_Q, packCH, dif_neg h0, dif_pos h1]
          · rw [Function.comp_apply, embCH410_apply, dif_neg h0, dif_neg h1]; dsimp only [z]
            rw [packState410_Anc, packCH, dif_neg h0, dif_neg h1]
      rw [hcomp, ps.ch_act]; simp [x']
    · funext i
      by_cases h0 : i.1 = 0
      · rw [Function.comp_apply, embCH410_apply, dif_pos h0]; dsimp only [z, x']
        rw [packState410_FH, packCH, dif_pos h0]
      · by_cases h1 : i.1 < 1 + n'
        · rw [Function.comp_apply, embCH410_apply, dif_neg h0, dif_pos h1]; dsimp only [z, x']
          rw [packState410_Q, packCH, dif_neg h0, dif_pos h1]
        · rw [Function.comp_apply, embCH410_apply, dif_neg h0, dif_neg h1]; dsimp only [z, x']
          rw [packState410_Anc, packCH, dif_neg h0, dif_neg h1]
  · simp only [↓reduceIte]
    let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc true fq pub neg (fun _ => false)
    let z' : Qubits n' → Qubits M' := fun q' =>
      packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q' w fc true fq pub neg (fun _ => false)
    refine act_embedOp_basis_sum embCH410 _ z (fun q' => hadamardN n' q' q)
      (fun q' => packCH n' (ps.ancCH n') true q' (fun _ => false)) z' ?_ ?_ ?_
    · have hcomp : z ∘ embCH410 (ps := ps) (r := r) (n := n) (M := M) =
          packCH n' (ps.ancCH n') true q (fun _ => false) := by
        funext i
        by_cases h0 : i.1 = 0
        · rw [Function.comp_apply, embCH410_apply, dif_pos h0]; dsimp only [z]
          rw [packState410_FH, packCH, dif_pos h0]
        · by_cases h1 : i.1 < 1 + n'
          · rw [Function.comp_apply, embCH410_apply, dif_neg h0, dif_pos h1]; dsimp only [z]
            rw [packState410_Q, packCH, dif_neg h0, dif_pos h1]
          · rw [Function.comp_apply, embCH410_apply, dif_neg h0, dif_neg h1]; dsimp only [z]
            rw [packState410_Anc, packCH, dif_neg h0, dif_neg h1]
      rw [hcomp, ps.ch_act]; simp
    · intro q'; funext i
      by_cases h0 : i.1 = 0
      · rw [Function.comp_apply, embCH410_apply, dif_pos h0]; dsimp only [z']
        rw [packState410_FH, packCH, dif_pos h0]
      · by_cases h1 : i.1 < 1 + n'
        · rw [Function.comp_apply, embCH410_apply, dif_neg h0, dif_pos h1]; dsimp only [z']
          rw [packState410_Q, packCH, dif_neg h0, dif_pos h1]
        · rw [Function.comp_apply, embCH410_apply, dif_neg h0, dif_neg h1]; dsimp only [z']
          rw [packState410_Anc, packCH, dif_neg h0, dif_neg h1]
    · intro q' i hi
      refine packState410_eq_of_Q _ mode q' q w fc true fq pub neg (fun _ => false) i fun j hj => ?_
      have hjlt := j.isLt
      exact False.elim (hi ⟨⟨1 + j.1, by omega⟩, by
        rw [embCH410_apply, dif_neg (by dsimp only; omega), dif_pos (by dsimp only; omega)]
        simpa using hj⟩)

lemma act_hHatCirc410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc : Bool) :
    act (hHatCirc410 (ps := ps) (r := r) (n := n) (M := M)).unitary
        (ket (packState410 c mode q w fc false false false false (fun _ => false))) =
      if fc then
        ∑ p' : Qubits qw × Qubits n', (H_hat410 M n' p' (mode, q)) •
          ket (packState410 c p'.1 p'.2 w true false false false false (fun _ => false))
      else
        ket (packState410 c mode q w false false false false false (fun _ => false)) := by
  have hcnot : ∀ (fh : Bool),
      act (Circuit.unitary ([cnotGateAt410 (ps := ps) (r := r) (n := n) (M := M) wireFC wireFH (by
            intro h; have hv := congrArg Fin.val h; simp only [wireFC_val, wireFH_val] at hv; omega)] :
          Circuit gates12 M'))
        (ket (packState410 c mode q w fc fh false false false (fun _ => false))) =
      ket (packState410 c mode q w fc (xor fh fc) false false false (fun _ => false)) := by
    intro fh; simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    exact act_cnotFCH _ _ _ _ _ _ _ _ _ _
  have hcnot_gen : ∀ (q' : Qubits n') (fh : Bool),
      act (Circuit.unitary ([cnotGateAt410 (ps := ps) (r := r) (n := n) (M := M) wireFC wireFH (by
            intro h; have hv := congrArg Fin.val h; simp only [wireFC_val, wireFH_val] at hv; omega)] :
          Circuit gates12 M'))
        (ket (packState410 c mode q' w fc fh false false false (fun _ => false))) =
      ket (packState410 c mode q' w fc (xor fh fc) false false false (fun _ => false)) := by
    intro q' fh; simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    exact act_cnotFCH _ _ _ _ _ _ _ _ _ _
  dsimp only [hHatCirc410]
  simp only [circuit_unitary_append, act_mul]
  rw [hcnot]
  cases fc
  · simp only [Bool.xor_false, Bool.false_eq_true, ↓reduceIte]
    rw [act_eqFHMode0Circ]
    simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    rw [act_chQCirc410]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [act_eqFHMode0Circ]
    simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    exact hcnot false
  · simp only [Bool.false_xor, ↓reduceIte]
    rw [act_eqFHMode0Circ]
    by_cases hm0 : mode = modeKet M 0
    · have hm0' : mode = fun _ => false := by rwa [modeKet_zero] at hm0
      rw [if_pos ⟨rfl, hm0'⟩]
      simp only [Bool.not_true]
      rw [act_chQCirc410]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [act_eqFHMode0Circ, if_pos ⟨rfl, hm0'⟩]
      simp only [Bool.not_false]
      rw [hcnot true]
      simp only [Bool.xor_self]
      symm
      rw [Fintype.sum_prod_type, Finset.sum_eq_single mode]
      · rw [Finset.sum_eq_single q]
        · simp [H_hat410, hm0]
        · intro q' _ hq'; simp [H_hat410, hm0, Matrix.one_apply, hq']
        · simp
      · intro m' _ hm'; refine Finset.sum_eq_zero fun q' _ => ?_; simp [H_hat410, hm']
      · simp
    · have hm0' : ¬ mode = fun _ => false := by rwa [← modeKet_zero M]
      rw [if_neg (fun h => hm0' h.2)]
      rw [act_chQCirc410]
      simp only [↓reduceIte, act_sum]
      have hterm : ∀ q' : Qubits n',
          act (Circuit.unitary ([cnotGateAt410 (ps := ps) (r := r) (n := n) (M := M) wireFC wireFH (by
              intro h; have hv := congrArg Fin.val h; simp only [wireFC_val, wireFH_val] at hv; omega)] :
              Circuit gates12 M'))
            (act (embedCircuit embEqFHMode0
              (ps.eqCirc (1 + qw) (patFCMode0 M) pauliX pauliX_mem_unitaryGroup)).unitary
              ((hadamardN n' q' q) •
                ket (packState410 c mode q' w true true false false false (fun _ => false)))) =
          (hadamardN n' q' q) •
            ket (packState410 c mode q' w true false false false false (fun _ => false)) := by
        intro q'
        rw [act_smul, act_smul, act_eqFHMode0Circ, if_neg (fun h => hm0' h.2), hcnot_gen q' true]
        simp
      rw [Finset.sum_congr rfl fun q' _ => hterm q']
      symm
      rw [Fintype.sum_prod_type, Finset.sum_eq_single mode]
      · refine Finset.sum_congr rfl fun q' _ => ?_; simp [H_hat410, hm0]
      · intro m' _ hm'; refine Finset.sum_eq_zero fun q' _ => ?_; simp [H_hat410, hm']
      · simp

lemma act_hcQCirc410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n')
    (fc fh fq pub neg : Bool) :
    act (embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M)) (ps.hcCirc n')).unitary
        (ket (packState410 c mode q (fun _ => false) fc fh fq pub neg (fun _ => false))) =
      ket (packState410 c mode q (natToBitsLSB ℓ (hammingWeight q)) fc fh fq pub neg (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q (fun _ => false) fc fh fq pub neg (fun _ => false)
  let z' := packState410 (ps := ps) (r := r) (n := n) (M := M)
    c mode q (natToBitsLSB ℓ (hammingWeight q)) fc fh fq pub neg (fun _ => false)
  let x' := packHC n' ℓ (ps.ancHC n') q (natToBitsLSB ℓ (hammingWeight q)) (fun _ => false)
  refine act_embedOp_basis_map embHC410 (ps.hcCirc n').unitary z x' ?_ z' ?_ ?_
  · have hcomp : z ∘ embHC410 (ps := ps) (r := r) (n := n) (M := M) =
        packHC n' ℓ (ps.ancHC n') q (fun _ => false) (fun _ => false) := by
      funext i
      simp only [Function.comp_apply, embHC410_apply, packHC, z]
      split_ifs <;> simp [packState410_Q, packState410_W, packState410_Anc]
    rw [hcomp, ps.hc_act]
  · funext i
    simp only [Function.comp_apply, embHC410_apply, packHC, z', x']
    split_ifs <;> simp [packState410_Q, packState410_W, packState410_Anc]
  · intro i hi
    refine packState410_eq_of_W c mode q _ (fun _ => false) fc fh fq pub neg (fun _ => false) i fun j hj => ?_
    have hjlt := j.isLt
    exact hi ⟨⟨n' + j.1, by omega⟩, by
      rw [embHC410_apply, dif_neg (by dsimp only; omega), dif_pos (by dsimp only; omega)]
      simpa using hj⟩

lemma act_hcQAdjCirc410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n')
    (fc fh fq pub neg : Bool) :
    act (embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M)) (ps.hcAdjCirc n')).unitary
        (ket (packState410 c mode q (natToBitsLSB ℓ (hammingWeight q)) fc fh fq pub neg (fun _ => false))) =
      ket (packState410 c mode q (fun _ => false) fc fh fq pub neg (fun _ => false)) := by
  have hunit : (embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M)) (ps.hcAdjCirc n')).unitary =
      star (embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M)) (ps.hcCirc n')).unitary := by
    rw [embedCircuit_unitary, embedCircuit_unitary, ps.hcAdj_unitary]
    ext y z
    simp only [embedOp, Matrix.of_apply, Matrix.star_apply]
    by_cases h : ∀ a, a ∉ Set.range (embHC410 (ps := ps) (r := r) (n := n) (M := M)) → y a = z a
    · have h' : ∀ a, a ∉ Set.range (embHC410 (ps := ps) (r := r) (n := n) (M := M)) → z a = y a :=
        fun a ha => (h a ha).symm
      rw [if_pos h, if_pos h']
    · have h' : ¬ ∀ a, a ∉ Set.range (embHC410 (ps := ps) (r := r) (n := n) (M := M)) → z a = y a :=
        fun h' => h fun a ha => (h' a ha).symm
      rw [if_neg h, if_neg h']; simp
  have hmem : (embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M)) (ps.hcCirc n')).unitary ∈
      Matrix.unitaryGroup (Qubits M') ℂ :=
    circuit_unitary_mem_unitaryGroup _
  have hmul : star (embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M)) (ps.hcCirc n')).unitary *
      (embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M)) (ps.hcCirc n')).unitary = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hmem
  rw [← act_hcQCirc410 (ps := ps) c mode q fc fh fq pub neg, ← act_mul, hunit, hmul, act_one_vec]

private lemma hammingWeight_le410 {m : ℕ} (q : Qubits m) : hammingWeight q ≤ m := by
  simpa [hammingWeight] using Finset.card_le_univ (Finset.univ.filter fun i => q i = true)

private lemma nat_lt_two_pow_clog410 (m : ℕ) : m < 2 ^ Nat.clog 2 (m + 1) := by
  have h : m + 1 ≤ 2 ^ Nat.clog 2 (m + 1) := Nat.le_pow_clog (b := 2) (by norm_num) (m + 1)
  omega

lemma act_uTilde410Circ (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n')
    (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (fc : Bool) :
    act (embedCircuit (embUTilde410 (ps := ps) (r := r) (n := n) (M := M))
          (ps.uTilde410Circ M n' hM hle)).unitary
        (ket (packState410 c mode q (natToBitsLSB ℓ (hammingWeight q)) fc false false false false (fun _ => false))) =
      if fc then
        ∑ mode' : Qubits qw, (U_op410 M (hammingWeight q) mode' mode) •
          ket (packState410 c mode' q (natToBitsLSB ℓ (hammingWeight q)) true false false false false (fun _ => false))
      else
        ket (packState410 c mode q (natToBitsLSB ℓ (hammingWeight q)) false false false false false (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let wq := natToBitsLSB ℓ (hammingWeight q)
  have hlt_q : hammingWeight q < 2 ^ ℓ := lt_of_le_of_lt (hammingWeight_le410 q) (nat_lt_two_pow_clog410 n')
  have hbits : bitsToNatLSB wq = hammingWeight q := bitsToNatLSB_natToBitsLSB hlt_q
  have hcomp : ∀ b : Bool,
      (packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q wq b false false false false (fun _ => false)) ∘
        embUTilde410 (ps := ps) (r := r) (n := n) (M := M) =
      packUTilde410 M n' (ps.ancUTilde M n') b wq mode (fun _ => false) := by
    intro b; funext i
    by_cases h0 : i.1 = 0
    · rw [Function.comp_apply, embUTilde410_apply, dif_pos h0]
      rw [packState410_FC, packUTilde410, dif_pos h0]
    · by_cases h1 : i.1 < 1 + ℓ
      · rw [Function.comp_apply, embUTilde410_apply, dif_neg h0, dif_pos h1]
        rw [packState410_W, packUTilde410, dif_neg h0, dif_pos h1]
      · by_cases h2 : i.1 < 1 + ℓ + qw
        · rw [Function.comp_apply, embUTilde410_apply, dif_neg h0, dif_neg h1, dif_pos h2]
          rw [packState410_Mode, packUTilde410, dif_neg h0, dif_neg h1, dif_pos h2]
        · rw [Function.comp_apply, embUTilde410_apply, dif_neg h0, dif_neg h1, dif_neg h2]
          rw [packState410_Anc, packUTilde410, dif_neg h0, dif_neg h1, dif_neg h2]
  cases fc
  · simp only [Bool.false_eq_true, ↓reduceIte]
    let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q wq false false false false false (fun _ => false)
    let x' := packUTilde410 M n' (ps.ancUTilde M n') false wq mode (fun _ => false)
    refine act_embedOp_basis_map embUTilde410 _ z x' ?_ z (hcomp false) (fun _ _ => rfl)
    rw [hcomp false, ps.uTilde410_act]; simp [x']
  · simp only [↓reduceIte]
    let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q wq true false false false false (fun _ => false)
    let z' : Qubits qw → Qubits M' := fun mode' =>
      packState410 (ps := ps) (r := r) (n := n) (M := M) c mode' q wq true false false false false (fun _ => false)
    refine act_embedOp_basis_sum embUTilde410 _ z (fun mode' => U_op410 M (hammingWeight q) mode' mode)
      (fun mode' => packUTilde410 M n' (ps.ancUTilde M n') true wq mode' (fun _ => false)) z' ?_ ?_ ?_
    · rw [hcomp true, ps.uTilde410_act, hbits]; simp
    · intro mode'; funext i
      by_cases h0 : i.1 = 0
      · rw [Function.comp_apply, embUTilde410_apply, dif_pos h0]; dsimp only [z']
        rw [packState410_FC, packUTilde410, dif_pos h0]
      · by_cases h1 : i.1 < 1 + ℓ
        · rw [Function.comp_apply, embUTilde410_apply, dif_neg h0, dif_pos h1]; dsimp only [z']
          rw [packState410_W, packUTilde410, dif_neg h0, dif_pos h1]
        · by_cases h2 : i.1 < 1 + ℓ + qw
          · rw [Function.comp_apply, embUTilde410_apply, dif_neg h0, dif_neg h1, dif_pos h2]; dsimp only [z']
            rw [packState410_Mode, packUTilde410, dif_neg h0, dif_neg h1, dif_pos h2]
          · rw [Function.comp_apply, embUTilde410_apply, dif_neg h0, dif_neg h1, dif_neg h2]; dsimp only [z']
            rw [packState410_Anc, packUTilde410, dif_neg h0, dif_neg h1, dif_neg h2]
    · intro mode' i hi
      refine packState410_eq_of_Mode c mode' mode q wq true false false false false (fun _ => false) i fun j hj => ?_
      have hjlt := j.isLt
      exact hi ⟨⟨1 + ℓ + j.1, by omega⟩, by
        rw [embUTilde410_apply, dif_neg (by dsimp only; omega), dif_neg (by dsimp only; omega),
          dif_pos (by dsimp only; omega)]
        simpa using hj⟩

noncomputable def uBodyCirc410 (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n') : Circuit gates12 M' :=
  embedCircuit embEqFC (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
  hHatCirc410 ++
  embedCircuit embHC410 (ps.hcCirc n') ++
  embedCircuit embUTilde410 (ps.uTilde410Circ M n' hM hle) ++
  embedCircuit embHC410 (ps.hcAdjCirc n') ++
  hHatCirc410 ++
  embedCircuit embEqFC (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)

lemma act_uBodyCirc410 (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n')
    (c : Qubits r) (mode : Qubits qw) (q : Qubits n') :
    act (uBodyCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle).unitary
        (ket (packState410 c mode q (fun _ => false) false false false false false (fun _ => false))) =
      if c = (fun _ => false) then
        ∑ p' : Qubits qw × Qubits n', (U_ideal410 M n' p' (mode, q)) •
          ket (packState410 c p'.1 p'.2 (fun _ => false) false false false false false (fun _ => false))
      else
        ket (packState410 c mode q (fun _ => false) false false false false false (fun _ => false)) := by
  simp only [uBodyCirc410, circuit_unitary_append, act_mul]
  rw [act_eqFCCirc410]
  by_cases hc0 : c = (fun _ => false)
  · rw [if_pos hc0, if_pos hc0]
    simp only [show (!false : Bool) = true from rfl]
    rw [act_hHatCirc410, if_pos rfl]
    have hmid : ∀ p₁ : Qubits qw × Qubits n',
        act (embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M)) (ps.hcAdjCirc n')).unitary
          (act (embedCircuit (embUTilde410 (ps := ps) (r := r) (n := n) (M := M)) (ps.uTilde410Circ M n' hM hle)).unitary
            (act (embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M)) (ps.hcCirc n')).unitary
              ((H_hat410 M n' p₁ (mode, q)) •
                ket (packState410 c p₁.1 p₁.2 (fun _ => false) true false false false false (fun _ => false))))) =
        (H_hat410 M n' p₁ (mode, q)) •
          ∑ p₂ : Qubits qw × Qubits n', (U_tilde410 M n' p₂ p₁) •
            ket (packState410 c p₂.1 p₂.2 (fun _ => false) true false false false false (fun _ => false)) := by
      intro p₁
      rw [act_smul, act_smul, act_smul, act_hcQCirc410, act_uTilde410Circ hM hle]
      simp only [↓reduceIte, act_sum]
      congr 1
      have hterm : ∀ m' : Qubits qw,
          act (embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M)) (ps.hcAdjCirc n')).unitary
            ((U_op410 M (hammingWeight p₁.2) m' p₁.1) •
              ket (packState410 c m' p₁.2 (natToBitsLSB ℓ (hammingWeight p₁.2)) true false false false false (fun _ => false))) =
          (U_op410 M (hammingWeight p₁.2) m' p₁.1) •
            ket (packState410 c m' p₁.2 (fun _ => false) true false false false false (fun _ => false)) := by
        intro m'; rw [act_smul, act_hcQAdjCirc410]
      rw [Finset.sum_congr rfl fun m' _ => hterm m']
      symm; rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun m' _ => ?_
      rw [Finset.sum_eq_single p₁.2]
      · simp [U_tilde410]
      · intro q₂ _ hq₂; simp [U_tilde410, hq₂]
      · simp
    rw [act_sum, act_sum, act_sum, Finset.sum_congr rfl fun p₁ _ => hmid p₁]
    have hlast : ∀ p₁ : Qubits qw × Qubits n',
        act (hHatCirc410 (ps := ps) (r := r) (n := n) (M := M)).unitary
          ((H_hat410 M n' p₁ (mode, q)) •
            ∑ p₂ : Qubits qw × Qubits n', (U_tilde410 M n' p₂ p₁) •
              ket (packState410 c p₂.1 p₂.2 (fun _ => false) true false false false false (fun _ => false))) =
        ∑ p₂ : Qubits qw × Qubits n', ∑ p' : Qubits qw × Qubits n',
          (H_hat410 M n' p' p₂ * U_tilde410 M n' p₂ p₁ * H_hat410 M n' p₁ (mode, q)) •
            ket (packState410 c p'.1 p'.2 (fun _ => false) true false false false false (fun _ => false)) := by
      intro p₁
      rw [act_smul, act_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p₂ _ => ?_
      rw [act_smul, act_hHatCirc410]
      simp only [↓reduceIte, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [act_sum, Finset.sum_congr rfl fun p₁ _ => hlast p₁]
    have hfin : ∀ p₁ : Qubits qw × Qubits n',
        act (embedCircuit (embEqFC (ps := ps) (r := r) (n := n) (M := M))
              (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).unitary
          (∑ p₂ : Qubits qw × Qubits n', ∑ p' : Qubits qw × Qubits n',
            (H_hat410 M n' p' p₂ * U_tilde410 M n' p₂ p₁ * H_hat410 M n' p₁ (mode, q)) •
              ket (packState410 c p'.1 p'.2 (fun _ => false) true false false false false (fun _ => false))) =
        ∑ p₂ : Qubits qw × Qubits n', ∑ p' : Qubits qw × Qubits n',
          (H_hat410 M n' p' p₂ * U_tilde410 M n' p₂ p₁ * H_hat410 M n' p₁ (mode, q)) •
            ket (packState410 c p'.1 p'.2 (fun _ => false) false false false false false (fun _ => false)) := by
      intro p₁
      rw [act_sum]
      refine Finset.sum_congr rfl fun p₂ _ => ?_
      rw [act_sum]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [act_smul, act_eqFCCirc410, if_pos hc0]; simp
    rw [act_sum, Finset.sum_congr rfl fun p₁ _ => hfin p₁]
    have hsw : (∑ p₁ : Qubits qw × Qubits n', ∑ p₂ : Qubits qw × Qubits n', ∑ p' : Qubits qw × Qubits n',
          (H_hat410 M n' p' p₂ * U_tilde410 M n' p₂ p₁ * H_hat410 M n' p₁ (mode, q)) •
            ket (packState410 (ps := ps) c p'.1 p'.2 (fun _ => false) false false false false false (fun _ => false))) =
        ∑ p' : Qubits qw × Qubits n', ∑ p₂ : Qubits qw × Qubits n', ∑ p₁ : Qubits qw × Qubits n',
          (H_hat410 M n' p' p₂ * U_tilde410 M n' p₂ p₁ * H_hat410 M n' p₁ (mode, q)) •
            ket (packState410 (ps := ps) c p'.1 p'.2 (fun _ => false) false false false false false (fun _ => false)) := by
      rw [Finset.sum_comm]
      have hs : ∀ p₂ : Qubits qw × Qubits n',
          (∑ p₁ : Qubits qw × Qubits n', ∑ p' : Qubits qw × Qubits n',
            (H_hat410 M n' p' p₂ * U_tilde410 M n' p₂ p₁ * H_hat410 M n' p₁ (mode, q)) •
              ket (packState410 (ps := ps) c p'.1 p'.2 (fun _ => false) false false false false false (fun _ => false))) =
          ∑ p' : Qubits qw × Qubits n', ∑ p₁ : Qubits qw × Qubits n',
            (H_hat410 M n' p' p₂ * U_tilde410 M n' p₂ p₁ * H_hat410 M n' p₁ (mode, q)) •
              ket (packState410 (ps := ps) c p'.1 p'.2 (fun _ => false) false false false false false (fun _ => false)) :=
        fun _ => Finset.sum_comm
      rw [Finset.sum_congr rfl fun p₂ _ => hs p₂]
      exact Finset.sum_comm
    rw [hsw]
    refine Finset.sum_congr rfl fun p' _ => ?_
    have hsm : ∀ p₂ : Qubits qw × Qubits n',
        (∑ p₁ : Qubits qw × Qubits n',
          (H_hat410 M n' p' p₂ * U_tilde410 M n' p₂ p₁ * H_hat410 M n' p₁ (mode, q)) •
            ket (packState410 (ps := ps) c p'.1 p'.2 (fun _ => false) false false false false false (fun _ => false))) =
        (∑ p₁ : Qubits qw × Qubits n',
          H_hat410 M n' p' p₂ * U_tilde410 M n' p₂ p₁ * H_hat410 M n' p₁ (mode, q)) •
          ket (packState410 (ps := ps) c p'.1 p'.2 (fun _ => false) false false false false false (fun _ => false)) :=
      fun _ => (Finset.sum_smul).symm
    rw [Finset.sum_congr rfl fun p₂ _ => hsm p₂, ← Finset.sum_smul]
    congr 1
    simp only [U_ideal410, Matrix.mul_apply]
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  · rw [if_neg hc0, if_neg hc0]
    rw [act_hHatCirc410]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [act_hcQCirc410, act_uTilde410Circ hM hle]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [act_hcQAdjCirc410, act_hHatCirc410]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [act_eqFCCirc410, if_neg hc0]

end SubCircuitEmbeddings410

/-! ### Eq. (127) Coherent Even-to-Odd Oracle Lift and `withMinus` Walk Step -/

section LiftedOracleAndStep410

variable {ps : PrimitiveSuite410} {r n M : ℕ}

local notation "qw" => qW M
local notation "n'" => n + 1
local notation "ℓ" => Nat.clog 2 (n + 2)
local notation "Amax" => ancMax410 ps r n M
local notation "M'" => regM'410 ps r n M

private noncomputable def minusAmp (b : Bool) : ℂ :=
  if b then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)

private lemma minusAmp_neg (b : Bool) : minusAmp (!b) = -minusAmp b := by
  cases b <;> simp [minusAmp]

private lemma sum_norm_sq_minusAmp : ∑ b : Bool, ‖minusAmp b‖ ^ 2 = 1 := by
  simp only [Fintype.sum_bool, minusAmp, ↓reduceIte, Bool.false_eq_true, norm_neg,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  rw [← two_mul, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

noncomputable def withMinus {m : ℕ} (φ : EuclideanSpace ℂ (Qubits m)) :
    EuclideanSpace ℂ (Qubits (m + 1)) :=
  WithLp.toLp 2 fun z => φ (Fin.init z) * minusAmp (z (Fin.last m))

lemma withMinus_norm {m : ℕ} (φ : EuclideanSpace ℂ (Qubits m)) : ‖withMinus φ‖ = ‖φ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_equiv (qubitsSnocEquiv m) _ (fun p => ‖φ p.1‖ ^ 2 * ‖minusAmp p.2‖ ^ 2)
    (fun z => by simp [withMinus, qubitsSnocEquiv, mul_pow])]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, sum_norm_sq_minusAmp, mul_one]

lemma withMinus_add {m : ℕ} (φ₁ φ₂ : EuclideanSpace ℂ (Qubits m)) :
    withMinus (φ₁ + φ₂) = withMinus φ₁ + withMinus φ₂ := by
  ext z; simp [withMinus, add_mul]

lemma withMinus_smul {m : ℕ} (c : ℂ) (φ : EuclideanSpace ℂ (Qubits m)) :
    withMinus (c • φ) = c • withMinus φ := by
  ext z; simp [withMinus]; ring

lemma withMinus_sum {m : ℕ} {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℂ (Qubits m)) :
    withMinus (∑ x ∈ s, f x) = ∑ x ∈ s, withMinus (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext z; simp [withMinus]
  | insert a s ha ih => rw [Finset.sum_insert ha, withMinus_add, ih, Finset.sum_insert ha]

lemma act_embedOp_castSucc_withMinus {m : ℕ} (G : Matrix (Qubits m) (Qubits m) ℂ)
    (φ : EuclideanSpace ℂ (Qubits m)) :
    act (embedOp G (Fin.castAddEmb 1)) (withMinus φ) = withMinus (act G φ) := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, withMinus, embedOp, Matrix.of_apply]
  have hcast : ∀ j : Fin m, Fin.castAddEmb 1 j = j.castSucc := fun _ => rfl
  have hrange : ∀ a : Fin (m + 1), a ∉ Set.range (Fin.castAddEmb 1) ↔ a = Fin.last m := by
    intro a
    refine Fin.lastCases ?_ ?_ a
    · constructor
      · intro _; rfl
      · rintro _ ⟨i, hi⟩
        have hi' := congrArg Fin.val hi
        simp [Fin.castAddEmb] at hi'; omega
    · intro i
      constructor
      · intro h; exact absurd ⟨i, rfl⟩ h
      · intro h; have h' := congrArg Fin.val h; simp at h'; omega
  have hprod : (∑ z : Qubits (m + 1),
      (if ∀ a : Fin (m + 1), a ∉ Set.range (Fin.castAddEmb 1) → y a = z a
        then G (y ∘ Fin.castAddEmb 1) (z ∘ Fin.castAddEmb 1) else 0) *
      (φ (Fin.init z) * minusAmp (z (Fin.last m)))) =
      ∑ p : Qubits m × Bool,
      (if ∀ a : Fin (m + 1), a ∉ Set.range (Fin.castAddEmb 1) →
          y a = Fin.snoc (α := fun _ => Bool) p.1 p.2 a
        then G (y ∘ Fin.castAddEmb 1) (Fin.snoc (α := fun _ => Bool) p.1 p.2 ∘ Fin.castAddEmb 1)
        else 0) *
      (φ p.1 * minusAmp p.2) := by
    refine Fintype.sum_equiv (qubitsSnocEquiv m) _ _ fun z => ?_
    dsimp only [qubitsSnocEquiv]
    change (if ∀ a : Fin (m + 1), a ∉ Set.range (Fin.castAddEmb 1) → y a = z a
        then G (y ∘ Fin.castAddEmb 1) (z ∘ Fin.castAddEmb 1) else 0) *
        (φ (Fin.init z) * minusAmp (z (Fin.last m))) =
      (if ∀ a : Fin (m + 1), a ∉ Set.range (Fin.castAddEmb 1) →
          y a = Fin.snoc (α := fun _ => Bool) (Fin.init z) (z (Fin.last m)) a
        then G (y ∘ Fin.castAddEmb 1)
          (Fin.snoc (α := fun _ => Bool) (Fin.init z) (z (Fin.last m)) ∘ Fin.castAddEmb 1)
        else 0) *
        (φ (Fin.init z) * minusAmp (z (Fin.last m)))
    simp_rw [Fin.snoc_init_self]
  rw [hprod, Fintype.sum_prod_type, Finset.sum_comm]
  have hcomp : ∀ x : Qubits m,
      (Fin.snoc (α := fun _ => Bool) x (y (Fin.last m)) ∘ Fin.castAddEmb 1) = x := by
    intro x; funext j; rw [Function.comp_apply, hcast j, Fin.snoc_castSucc]
  have hy_comp : (y ∘ Fin.castAddEmb 1) = Fin.init y := by funext j; rfl
  rw [Finset.sum_eq_single (y (Fin.last m))]
  · have hpos_cond : ∀ x : Qubits m,
        ∀ a : Fin (m + 1), a ∉ Set.range (Fin.castAddEmb 1) →
          y a = Fin.snoc (α := fun _ => Bool) x (y (Fin.last m)) a := fun x a ha => by
      rw [(hrange a).mp ha, Fin.snoc_last]
    have hsum_term : ∀ x : Qubits m,
        (if ∀ a : Fin (m + 1), a ∉ Set.range (Fin.castAddEmb 1) →
            y a = Fin.snoc (α := fun _ => Bool) x (y (Fin.last m)) a
          then G (y ∘ Fin.castAddEmb 1) (Fin.snoc (α := fun _ => Bool) x (y (Fin.last m)) ∘ Fin.castAddEmb 1)
          else 0) * (φ x * minusAmp (y (Fin.last m))) =
        (G (Fin.init y) x * φ x) * minusAmp (y (Fin.last m)) := fun x => by
      rw [if_pos (hpos_cond x), hy_comp, hcomp x]; ring
    simp_rw [hsum_term, ← Finset.sum_mul]
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    have hnot : ¬ (∀ a : Fin (m + 1), a ∉ Set.range (Fin.castAddEmb 1) →
        y a = Fin.snoc (α := fun _ => Bool) x b a) := by
      intro h; have hlast := h (Fin.last m) ((hrange (Fin.last m)).mpr rfl)
      simp only [Fin.snoc_last] at hlast; exact hb hlast.symm
    rw [if_neg hnot, zero_mul]
  · simp

private lemma majJunta_eq_neg_one_iff {n₀ : ℕ} (A : Finset (Fin n₀)) (x : Qubits n₀) :
    decide (majJunta A (Finset.univ.filter fun i => x i = true) = -1) = majorityBit A x := by
  have hset : A ∩ (Finset.univ.filter fun i => x i = true) = A.filter fun i => x i := by
    ext i; simp
  rw [majJunta, majorityBit, hset]
  split_ifs with h1 <;> simp_all

noncomputable def phaseCtrlOracle {M₀ n₀ : ℕ} (A : Finset (Fin n₀)) (ctrl : Fin M₀)
    (regQ : Fin n₀ ↪ Fin M₀) : Matrix (Qubits M₀) (Qubits M₀) ℂ :=
  Matrix.diagonal fun x => if x ctrl && majorityBit A (x ∘ regQ) then (-1 : ℂ) else 1

private lemma oracleStep_ctrl_query_apply_eq {S : Set Gate} {M₀ n₀ : ℕ} (A : Finset (Fin n₀))
    (ctrl : Fin M₀) (regQ : Fin n₀ ↪ Fin M₀)
    (wires : Fin (n₀ + 1) ↪ Fin (M₀ + 1))
    (hw_init : ∀ i : Fin n₀, wires i.castSucc = (regQ i).castSucc)
    (hw_last : wires (Fin.last n₀) = Fin.last M₀)
    (hc : ∀ c, some ctrl.castSucc = some c → c ∉ Set.range wires)
    (y z : Qubits (M₀ + 1)) :
    OracleStep.mat (S := S) (r := 1) (a := fun _ => n₀ + 1)
      (fun _ => majOracle A) (.query 0 false (some ctrl.castSucc) wires hc) y z =
    if z = Fin.snoc (α := fun _ => Bool) (Fin.init y)
      (xor (y (Fin.last M₀)) (Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ)))
    then 1 else 0 := by
  let w' : Fin (n₀ + 2) ↪ Fin (M₀ + 1) :=
    ⟨Fin.cons ctrl.castSucc wires, Fin.cons_injective_iff.2 ⟨hc ctrl.castSucc rfl, wires.injective⟩⟩
  change embedOp (controlledQubits (majOracle A)) w' y z = _
  simp only [embedOp, Matrix.of_apply, controlledQubits, Matrix.submatrix_apply, controlled]
  have hw'0 : ∀ u : Qubits (M₀ + 1), (u ∘ w') 0 = u ctrl.castSucc := fun _ => rfl
  have hw'_tail : ∀ u : Qubits (M₀ + 1), Fin.tail (u ∘ w') = u ∘ wires := fun _ => by funext i; rfl
  have hw_init_comp : ∀ u : Qubits (M₀ + 1), Fin.init (u ∘ wires) = Fin.init u ∘ regQ := fun _ => by
    funext i; simp [Fin.init, hw_init i]
  have hw_last_comp : ∀ u : Qubits (M₀ + 1), (u ∘ wires) (Fin.last n₀) = u (Fin.last M₀) := fun u => by
    simp [hw_last]
  by_cases hz_eq : z = Fin.snoc (α := fun _ => Bool) (Fin.init y)
      (xor (y (Fin.last M₀)) (Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ)))
  · rw [if_pos hz_eq]
    have hoff : ∀ a : Fin (M₀ + 1), a ∉ Set.range w' → y a = z a := by
      intro a ha; rw [hz_eq]; refine Fin.lastCases ?_ ?_ a ha
      · intro hl; exfalso; apply hl; refine ⟨(Fin.last n₀).succ, ?_⟩; simp [w', hw_last]
      · intro i _; simp [Fin.snoc_castSucc, Fin.init]
    rw [if_pos hoff]
    have hctrl_yz : y ctrl.castSucc = z ctrl.castSucc := by rw [hz_eq, Fin.snoc_castSucc]; rfl
    simp only [hw'0, hw'_tail, if_pos hctrl_yz]
    cases hcval : y ctrl.castSucc
    · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.one_apply, hw'_tail]
      have hyw : y ∘ wires = z ∘ wires := by
        funext j; refine Fin.lastCases ?_ ?_ j
        · simp [hw_last, hz_eq, hcval, Fin.init]
        · intro i; simp [hw_init i, hz_eq, Fin.init]
      rw [if_pos hyw]
    · simp only [↓reduceIte, majOracle, Matrix.of_apply, majJunta_eq_neg_one_iff]
      have hmaj : y ∘ wires = Fin.snoc (α := fun _ => Bool) (Fin.init (z ∘ wires))
          (xor ((z ∘ wires) (Fin.last n₀)) (majorityBit A (Fin.init (z ∘ wires)))) := by
        funext j; refine Fin.lastCases ?_ ?_ j
        · simp only [hw_last_comp, hw_init_comp, hz_eq, Fin.snoc_last, Fin.init_snoc]; simp [Fin.init, hcval]
        · intro i; simp only [Function.comp_apply, hw_init i, Fin.snoc_castSucc, hw_init_comp, hz_eq, Fin.init_def]
      rw [if_pos hmaj]
  · rw [if_neg hz_eq]
    by_cases hoff : ∀ a : Fin (M₀ + 1), a ∉ Set.range w' → y a = z a
    · rw [if_pos hoff]; simp only [hw'0, hw'_tail]
      by_cases hctrl_yz : y ctrl.castSucc = z ctrl.castSucc
      · rw [if_pos hctrl_yz]
        have not_mem_w' : ∀ i : Fin M₀, i ≠ ctrl → (∀ q, regQ q ≠ i) → i.castSucc ∉ Set.range w' := by
          intro i hi hq ⟨x, hx⟩; refine Fin.cases ?_ ?_ x hx
          · intro h0; exact hi (Fin.ext (by have h0' := congrArg Fin.val h0; simpa [w'] using h0'.symm))
          · intro j hj; refine Fin.lastCases ?_ ?_ j hj
            · intro hl; have hl' := congrArg Fin.val hl; simp [w', hw_last] at hl'; omega
            · intro q hq'; apply hq q; exact Fin.ext (by have hq'' := congrArg Fin.val hq'; simpa [w', hw_init q] using hq'')
        cases hcval : y ctrl.castSucc
        · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.one_apply]; rw [if_neg]
          intro hyw; apply hz_eq; funext a; refine Fin.lastCases ?_ ?_ a
          · have hl := congrFun hyw (Fin.last n₀); change (y ∘ wires) (Fin.last n₀) = (z ∘ wires) (Fin.last n₀) at hl
            rw [hw_last_comp y, hw_last_comp z] at hl
            have hcval' : Fin.init y ctrl = false := by simpa [Fin.init] using hcval
            simp [Fin.snoc_last, hcval', hl]
          · intro i; by_cases hi : i = ctrl
            · subst hi; simpa [Fin.snoc_castSucc, Fin.init] using hctrl_yz.symm
            · by_cases hq : ∃ q, regQ q = i
              · obtain ⟨q, rfl⟩ := hq; have hqi := congrFun hyw q.castSucc
                change y (wires q.castSucc) = z (wires q.castSucc) at hqi; rw [hw_init q] at hqi
                simpa [Fin.snoc_castSucc, Fin.init] using hqi.symm
              · have hq' : ∀ q, regQ q ≠ i := fun q h => hq ⟨q, h⟩
                simpa [Fin.snoc_castSucc, Fin.init] using (hoff i.castSucc (not_mem_w' i hi hq')).symm
        · simp only [↓reduceIte, majOracle, Matrix.of_apply, majJunta_eq_neg_one_iff]; rw [if_neg]
          intro hmaj; apply hz_eq; funext a; refine Fin.lastCases ?_ ?_ a
          · have hl := congrFun hmaj (Fin.last n₀)
            simp only [hw_last_comp, Fin.snoc_last, hw_init_comp] at hl
            have hinit_q : Fin.init z ∘ regQ = Fin.init y ∘ regQ := by
              funext q; have hq := congrFun hmaj q.castSucc
              simp only [Function.comp_apply, hw_init q, Fin.snoc_castSucc, hw_init_comp] at hq; exact hq.symm
            rw [hl, hinit_q]
            have hcval' : Fin.init y ctrl = true := by simpa [Fin.init] using hcval
            simp only [Fin.snoc_last, hcval', Bool.true_and, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
          · intro i; by_cases hi : i = ctrl
            · subst hi; simpa [Fin.snoc_castSucc, Fin.init] using hctrl_yz.symm
            · by_cases hq : ∃ q, regQ q = i
              · obtain ⟨q, rfl⟩ := hq; have hqi := congrFun hmaj q.castSucc
                simp only [Function.comp_apply, hw_init q, Fin.snoc_castSucc, hw_init_comp] at hqi
                simpa [Fin.snoc_castSucc, Fin.init] using hqi.symm
              · have hq' : ∀ q, regQ q ≠ i := fun q h => hq ⟨q, h⟩
                simpa [Fin.snoc_castSucc, Fin.init] using (hoff i.castSucc (not_mem_w' i hi hq')).symm
      · rw [if_neg hctrl_yz]
    · rw [if_neg hoff]

lemma act_ctrl_majOracle_withMinus {S : Set Gate} {M₀ n₀ : ℕ} (A : Finset (Fin n₀)) (ctrl : Fin M₀)
    (regQ : Fin n₀ ↪ Fin M₀) (wires : Fin (n₀ + 1) ↪ Fin (M₀ + 1))
    (hw_init : ∀ i : Fin n₀, wires i.castSucc = (regQ i).castSucc)
    (hw_last : wires (Fin.last n₀) = Fin.last M₀)
    (hc : ∀ c, some ctrl.castSucc = some c → c ∉ Set.range wires)
    (φ : EuclideanSpace ℂ (Qubits M₀)) :
    act (OracleStep.mat (S := S) (r := 1) (a := fun _ => n₀ + 1)
      (fun _ => majOracle A) (.query 0 false (some ctrl.castSucc) wires hc)) (withMinus φ) =
    withMinus (act (phaseCtrlOracle A ctrl regQ) φ) := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, withMinus, phaseCtrlOracle,
    Matrix.diagonal_apply]
  simp_rw [oracleStep_ctrl_query_apply_eq A ctrl regQ wires hw_init hw_last hc]
  let bit := Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ)
  rw [Finset.sum_eq_single (Fin.snoc (α := fun _ => Bool) (Fin.init y) (xor (y (Fin.last M₀)) bit))]
  · rw [if_pos rfl, one_mul, Fin.init_snoc, Fin.snoc_last]
    rw [Finset.sum_eq_single (Fin.init y)]
    · by_cases hbit : bit = true
      · have h1 : Fin.init y ctrl = true := (Bool.and_eq_true _ _).mp hbit |>.1
        have h2 : majorityBit A (Fin.init y ∘ regQ) = true := (Bool.and_eq_true _ _).mp hbit |>.2
        rw [hbit, Bool.xor_true, minusAmp_neg]
        simp only [h1, h2, Bool.true_and, ↓reduceIte]; ring
      · have hbitf : bit = false := Bool.eq_false_iff.mpr hbit
        rw [hbitf, Bool.xor_false]
        simp only [bit] at hbitf
        simp only [hbitf, Bool.false_eq_true, ↓reduceIte]; ring
    · intro x _ hx; simp [hx.symm]
    · simp
  · intro z _ hz; rw [if_neg hz, zero_mul]
  · simp

private def prepareMinusWires (m : ℕ) : Fin 1 ↪ Fin (m + 1) :=
  ⟨fun _ => Fin.last m,
    fun u v _ => Fin.ext (Nat.lt_one_iff.mp u.2 |>.trans (Nat.lt_one_iff.mp v.2).symm)⟩

private noncomputable def prepareMinusStep410 (m : ℕ) :
    OracleStep gates12 (fun _ : Fin 1 => n + 1) (m + 1) :=
  OracleStep.gate
    ⟨Gate.ofMatrix1 (hadamard * pauliX),
      gate_ofMatrix1_mem_gates12 hadamard_mul_pauliX_mem_unitaryGroup,
      prepareMinusWires m⟩

private lemma act_prepareMinusStep410 (m : ℕ)
    (orc : (k : Fin 1) → Matrix (Qubits ((fun _ : Fin 1 => n + 1) k)) (Qubits ((fun _ : Fin 1 => n + 1) k)) ℂ) :
    act (OracleStep.mat orc (prepareMinusStep410 (n := n) m)) (zeroKet (m + 1)) = withMinus (zeroKet m) := by
  change act (embedOp ((hadamard * pauliX).submatrix (fun b => b 0) (fun b => b 0))
    (prepareMinusWires m)) (zeroKet (m + 1)) = withMinus (zeroKet m)
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, embedOp, Matrix.of_apply,
    Matrix.submatrix_apply, zeroKet, ket, withMinus]
  rw [Finset.sum_eq_single (fun _ : Fin (m + 1) => false)]
  · simp only [PiLp.single_apply, ↓reduceIte, mul_one]
    by_cases hinit : Fin.init y = fun _ : Fin m => false
    · have hcond : ∀ b : Fin (m + 1), b ∉ Set.range (prepareMinusWires m) → y b = false := by
        intro b hb; have hne : b ≠ Fin.last m := fun heq => hb ⟨0, heq.symm⟩
        rcases Fin.exists_castSucc_eq.mpr hne with ⟨i, rfl⟩; exact congrFun hinit i
      rw [if_pos hcond, if_pos hinit, one_mul]
      change (hadamard * pauliX) (y (Fin.last m)) false = minusAmp (y (Fin.last m))
      cases y (Fin.last m) <;> simp [hadamard, pauliX, Matrix.mul_apply, minusAmp]
    · have hcond : ¬ ∀ b : Fin (m + 1), b ∉ Set.range (prepareMinusWires m) → y b = false := by
        intro h; apply hinit; funext i; apply h i.castSucc; rintro ⟨_, h0⟩; exact Fin.castSucc_ne_last i h0.symm
      rw [if_neg hcond, if_neg hinit, zero_mul]
  · intro z _ hz; simp only [PiLp.single_apply, if_neg hz, mul_zero]
  · simp

noncomputable def liftToFull410 (c₀ : Circuit gates12 M') :
    OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (M' + 1) :=
  (embedCircuit (Fin.castAddEmb 1) c₀).map OracleStep.gate

lemma liftToFull410_unitary (c₀ : Circuit gates12 M')
    (orc : (k : Fin 1) → Matrix (Qubits ((fun _ : Fin 1 => n + 1) k)) (Qubits ((fun _ : Fin 1 => n + 1) k)) ℂ) :
    (liftToFull410 (ps := ps) (r := r) (n := n) (M := M) c₀).unitary orc =
      embedOp c₀.unitary (Fin.castAddEmb 1) := by
  unfold liftToFull410; rw [oracleCircuit_unitary_lift, embedCircuit_unitary]

lemma liftToFull410_act (c₀ : Circuit gates12 M')
    (orc : (k : Fin 1) → Matrix (Qubits ((fun _ : Fin 1 => n + 1) k)) (Qubits ((fun _ : Fin 1 => n + 1) k)) ℂ)
    (φ : EuclideanSpace ℂ (Qubits M')) :
    act ((liftToFull410 (ps := ps) (r := r) (n := n) (M := M) c₀).unitary orc) (withMinus φ) =
      withMinus (act c₀.unitary φ) := by
  rw [liftToFull410_unitary, act_embedOp_castSucc_withMinus]

lemma liftToFull410_queryCount (c₀ : Circuit gates12 M') :
    (liftToFull410 (ps := ps) (r := r) (n := n) (M := M) c₀).queryCount 0 = 0 := by
  unfold liftToFull410
  exact oracleCircuit_queryCount_lift _ _

lemma liftToFull410_gateCount (c₀ : Circuit gates12 M') :
    (liftToFull410 (ps := ps) (r := r) (n := n) (M := M) c₀).gateCount = c₀.length := by
  unfold liftToFull410; rw [oracleCircuit_gateCount_lift, embedCircuit, List.length_map]

lemma liftToFull410_depth_le (c₀ : Circuit gates12 M') :
    nonOracleDepth (liftToFull410 (ps := ps) (r := r) (n := n) (M := M) c₀) ≤
      nonOracleDepth (c₀.map OracleStep.gate : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) M') :=
  nonOracleDepth_embedCircuit (Fin.castAddEmb 1) c₀

noncomputable def oracleWires410 : Fin (n + 1) ↪ Fin (M' + 1) :=
  let f : Fin (n + 1) → Fin (M' + 1) := fun i =>
    if h : i.1 < n then (regQ (ps := ps) (r := r) (n := n) (M := M) ⟨i.1, by omega⟩).castSucc
    else Fin.last M'
  ⟨f, fun a b hab => by
    have ha := a.isLt; have hb := b.isLt
    have hv := congrArg Fin.val hab
    have hregq : ∀ (k : ℕ) (hk : k < n'),
        ((regQ (ps := ps) (r := r) (n := n) (M := M) ⟨k, hk⟩).castSucc).1 = r + qw + k := fun _ _ => rfl
    have hlast : (Fin.last M').1 = r + qw + n' + ℓ + 5 + Amax := rfl
    dsimp only [f] at hv
    by_cases ha_lt : a.1 < n <;> by_cases hb_lt : b.1 < n
    · rw [dif_pos ha_lt, dif_pos hb_lt, hregq, hregq] at hv; ext; omega
    · rw [dif_pos ha_lt, dif_neg hb_lt, hregq, hlast] at hv; omega
    · rw [dif_neg ha_lt, dif_pos hb_lt, hlast, hregq] at hv; omega
    · ext; omega⟩

@[simp] lemma oracleWires410_apply (i : Fin (n + 1)) :
    oracleWires410 (ps := ps) (r := r) (n := n) (M := M) i =
      if h : i.1 < n then (regQ (ps := ps) (r := r) (n := n) (M := M) ⟨i.1, by omega⟩).castSucc
      else Fin.last M' := rfl

lemma oracleWires410_init (i : Fin n) :
    oracleWires410 (ps := ps) (r := r) (n := n) (M := M) i.castSucc =
      ((Fin.castSuccEmb.trans (regQ (ps := ps) (r := r) (n := n) (M := M))) i).castSucc := by
  simp only [oracleWires410_apply, Fin.val_castSucc, i.isLt, ↓reduceDIte, Function.Embedding.trans_apply,
    Fin.castSuccEmb_apply]; rfl

lemma oracleWires410_last :
    oracleWires410 (ps := ps) (r := r) (n := n) (M := M) (Fin.last n) = Fin.last M' := by
  simp only [oracleWires410_apply, Fin.val_last, lt_self_iff_false, ↓reduceDIte]

lemma oracleWires410_hc (c : Fin (M' + 1))
    (hc : some (wireFQ (ps := ps) (r := r) (n := n) (M := M)).castSucc = some c) :
    c ∉ Set.range (oracleWires410 (ps := ps) (r := r) (n := n) (M := M)) := by
  have hceq : c = (wireFQ (ps := ps) (r := r) (n := n) (M := M)).castSucc := (Option.some.inj hc).symm
  subst hceq
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hwfq : ((wireFQ (ps := ps) (r := r) (n := n) (M := M)).castSucc).1 = r + qw + n' + ℓ + 2 := rfl
  have hregq : ∀ k : Fin n', ((regQ (ps := ps) (r := r) (n := n) (M := M) k).castSucc).1 = r + qw + k.1 :=
    fun _ => rfl
  have hlast : (Fin.last M').1 = r + qw + n' + ℓ + 5 + Amax := rfl
  rw [oracleWires410_apply] at hv
  by_cases hi_lt : i.1 < n
  · rw [dif_pos hi_lt, hregq, hwfq] at hv; dsimp only at hv; omega
  · rw [dif_neg hi_lt, hlast, hwfq] at hv; omega

noncomputable def queryStepFull410 : OracleStep gates12 (fun _ : Fin 1 => n + 1) (M' + 1) :=
  OracleStep.query 0 false (some (wireFQ (ps := ps) (r := r) (n := n) (M := M)).castSucc)
    (oracleWires410 (ps := ps) (r := r) (n := n) (M := M))
    (oracleWires410_hc (ps := ps) (r := r) (n := n) (M := M))

noncomputable def xLastGate410 : GateApp gates12 M' :=
  ⟨Gate.ofMatrix1 pauliX, gate_ofMatrix1_mem_gates12 pauliX_mem_unitaryGroup,
    singleWireEmb410 (regQ (Fin.last n))⟩

noncomputable def zNegGate410 : GateApp gates12 M' :=
  ⟨Gate.ofMatrix1 pauliZ, gate_ofMatrix1_mem_gates12 pauliZ_mem_unitaryGroup,
    singleWireEmb410 wireNeg⟩

noncomputable def negPrepCirc410 : Circuit gates12 M' :=
  [xLastGate410] ++ embedCircuit embToffoliNeg ps.toffoliCirc ++ [xLastGate410]

lemma negPrepCirc410_length :
    (negPrepCirc410 (ps := ps) (r := r) (n := n) (M := M)).length = 2 + ps.toffoliCirc.length := by
  simp [negPrepCirc410, embedCircuit]; ring

lemma act_xLastGate410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    act (embedOp (xLastGate410 (ps := ps) (r := r) (n := n) (M := M)).gate.mat
          (xLastGate410 (ps := ps) (r := r) (n := n) (M := M)).wires)
        (ket (packState410 c mode q w fc fh fq pub neg a)) =
      ket (packState410 c mode (Function.update q (Fin.last n) !(q (Fin.last n))) w fc fh fq pub neg a) := by
  let q' := Function.update q (Fin.last n) !(q (Fin.last n))
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg a
  let z' := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q' w fc fh fq pub neg a
  refine act_embedOp_basis_map (singleWireEmb410 (regQ (Fin.last n)))
    (Gate.ofMatrix1 pauliX).mat z (z' ∘ singleWireEmb410 (regQ (Fin.last n))) ?_ z' rfl ?_
  · ext u
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Gate.ofMatrix1,
      Matrix.submatrix_apply, ket, PiLp.single_apply]
    rw [Finset.sum_eq_single (z ∘ singleWireEmb410 (regQ (Fin.last n)))]
    · simp only [↓reduceIte, mul_one, pauliX, Matrix.of_apply]
      have hz0 : (z ∘ singleWireEmb410 (regQ (Fin.last n))) 0 = q (Fin.last n) := by
        simp [z, singleWireEmb410_apply, packState410_Q]
      have hz'0 : (z' ∘ singleWireEmb410 (regQ (Fin.last n))) 0 = !(q (Fin.last n)) := by
        simp [z', q', singleWireEmb410_apply, packState410_Q]
      have heq : (u = z' ∘ singleWireEmb410 (regQ (Fin.last n))) ↔ (u 0 = !(q (Fin.last n))) := by
        constructor
        · intro h; rw [h, hz'0]
        · intro h; funext i; fin_cases i; dsimp; exact h.trans hz'0.symm
      rw [hz0]
      by_cases hu : u = z' ∘ singleWireEmb410 (regQ (Fin.last n))
      · rw [if_pos hu]
        have hu0 : u 0 = !(q (Fin.last n)) := heq.mp hu
        cases hql : q (Fin.last n) <;> cases h0 : u 0 <;> simp_all
      · rw [if_neg hu]
        have hne : u 0 ≠ !(q (Fin.last n)) := fun h => hu (heq.mpr h)
        cases hql : q (Fin.last n) <;> cases h0 : u 0 <;> simp_all
    · intro x _ hx; simp [hx]
    · simp
  · intro i hi
    refine packState410_eq_of_Q c mode q' q w fc fh fq pub neg a i fun j hj => ?_
    by_cases hjn : j = Fin.last n
    · subst hjn; exact absurd hj (fun h => hi ⟨0, by simp [singleWireEmb410_apply, h]⟩)
    · simp [q', Function.update_of_ne hjn]

lemma act_toffoliNeg (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    act (embedCircuit (embToffoliNeg (ps := ps) (r := r) (n := n) (M := M)) ps.toffoliCirc).unitary
        (ket (packState410 c mode q w fc fh fq pub neg a)) =
      ket (packState410 c mode q w fc fh fq pub (xor neg (fq && q (Fin.last n))) a) := by
  rw [embedCircuit_unitary]
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg a
  let z' := packState410 (ps := ps) (r := r) (n := n) (M := M)
    c mode q w fc fh fq pub (xor neg (fq && q (Fin.last n))) a
  let x' : Qubits 3 := fun i =>
    if i.1 = 0 then fq else if i.1 = 1 then q (Fin.last n) else xor neg (fq && q (Fin.last n))
  refine act_embedOp_basis_map embToffoliNeg ps.toffoliCirc.unitary z x' ?_ z' ?_ ?_
  · have hcomp : z ∘ embToffoliNeg (ps := ps) (r := r) (n := n) (M := M) =
        fun i : Fin 3 => if i.1 = 0 then fq else if i.1 = 1 then q (Fin.last n) else neg := by
      funext i; fin_cases i
      · simp [z, embToffoliNeg_apply, packState410_FQ]
      · simp [z, embToffoliNeg_apply, packState410_Q]
      · simp [z, embToffoliNeg_apply, packState410_Neg]
    rw [hcomp]; exact ps.toffoli_act fq (q (Fin.last n)) neg
  · funext i; fin_cases i
    · simp [z', x', embToffoliNeg_apply, packState410_FQ]
    · simp [z', x', embToffoliNeg_apply, packState410_Q]
    · simp [z', x', embToffoliNeg_apply, packState410_Neg]
  · intro i hi
    exact packState410_eq_of_flag (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun h => False.elim (hi ⟨2, by simp [embToffoliNeg_apply, h.symm]⟩))

lemma act_negPrepCirc410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    act (negPrepCirc410 (ps := ps) (r := r) (n := n) (M := M)).unitary
        (ket (packState410 c mode q w fc fh fq pub neg a)) =
      ket (packState410 c mode q w fc fh fq pub (xor neg (fq && !(q (Fin.last n)))) a) := by
  have hx1 : ∀ (q₁ : Qubits n') (neg₁ : Bool),
      act (Circuit.unitary ([xLastGate410 (ps := ps) (r := r) (n := n) (M := M)] : Circuit gates12 M'))
        (ket (packState410 c mode q₁ w fc fh fq pub neg₁ a)) =
      ket (packState410 c mode (Function.update q₁ (Fin.last n) !(q₁ (Fin.last n))) w fc fh fq pub neg₁ a) := by
    intro q₁ neg₁
    simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    exact act_xLastGate410 _ _ _ _ _ _ _ _ _ _
  simp only [negPrepCirc410, circuit_unitary_append, act_mul]
  rw [hx1, act_toffoliNeg, hx1]
  simp only [Function.update_self, Bool.not_not]
  congr 1; ext i
  by_cases hi : i.1 < r
  · simp [packState410, hi]
  · by_cases hi1 : i.1 < r + qw
    · simp [packState410, hi, hi1]
    · by_cases hi2 : i.1 < r + qw + n'
      · simp only [packState410, hi, hi1, hi2, ↓reduceDIte]
        by_cases hjn : (⟨i.1 - (r + qw), by omega⟩ : Fin n') = Fin.last n
        · simp [hjn]
        · simp [hjn]
      · simp [packState410, hi, hi1, hi2]

lemma act_cnEmbedCirc410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) :
    act (embedCircuit (embCN410 (ps := ps) (r := r) (n := n) (M := M)) (ps.cnCirc n)).unitary
        (ket (packState410 c mode q w fc fh fq pub neg (fun _ => false))) =
      ket (packState410 c mode
        (if neg then Fin.snoc (fun i : Fin n => !(Fin.init q i)) (q (Fin.last n)) else q)
        w fc fh fq pub neg (fun _ => false)) := by
  rw [embedCircuit_unitary]
  let q_tgt : Qubits n' := if neg then Fin.snoc (fun i : Fin n => !(Fin.init q i)) (q (Fin.last n)) else q
  let x' : Qubits n := if neg then (fun i => !(Fin.init q i)) else Fin.init q
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg (fun _ => false)
  let z' := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q_tgt w fc fh fq pub neg (fun _ => false)
  refine act_embedOp_basis_map embCN410 (ps.cnCirc n).unitary z
    (packCN n (ps.ancCN n) neg x' (fun _ => false)) ?_ z' ?_ ?_
  · have hcomp : z ∘ embCN410 (ps := ps) (r := r) (n := n) (M := M) =
        packCN n (ps.ancCN n) neg (Fin.init q) (fun _ => false) := by
      funext i
      by_cases h0 : i.1 = 0
      · rw [Function.comp_apply, embCN410_apply, dif_pos h0]; dsimp only [z]
        rw [packState410_Neg, packCN, dif_pos h0]
      · by_cases h1 : i.1 < 1 + n
        · rw [Function.comp_apply, embCN410_apply, dif_neg h0, dif_pos h1]; dsimp only [z]
          rw [packState410_Q, packCN, dif_neg h0, dif_pos h1]; rfl
        · rw [Function.comp_apply, embCN410_apply, dif_neg h0, dif_neg h1]; dsimp only [z]
          rw [packState410_Anc, packCN, dif_neg h0, dif_neg h1]
    rw [hcomp, ps.cn_act]
  · funext i
    by_cases h0 : i.1 = 0
    · rw [Function.comp_apply, embCN410_apply, dif_pos h0]; dsimp only [z']
      rw [packState410_Neg, packCN, dif_pos h0]
    · by_cases h1 : i.1 < 1 + n
      · rw [Function.comp_apply, embCN410_apply, dif_neg h0, dif_pos h1]; dsimp only [z']
        rw [packState410_Q, packCN, dif_neg h0, dif_pos h1]
        cases neg
        · rfl
        · change Fin.snoc (α := fun _ => Bool) (fun k : Fin n => !(Fin.init q k)) (q (Fin.last n))
              (⟨i.1 - 1, by omega⟩ : Fin n).castSucc = !(Fin.init q ⟨i.1 - 1, by omega⟩)
          rw [Fin.snoc_castSucc]
      · rw [Function.comp_apply, embCN410_apply, dif_neg h0, dif_neg h1]; dsimp only [z']
        rw [packState410_Anc, packCN, dif_neg h0, dif_neg h1]
  · intro i hi
    refine packState410_eq_of_Q c mode q_tgt q w fc fh fq pub neg (fun _ => false) i fun j hj => ?_
    by_cases hjn : j = Fin.last n
    · subst hjn; cases hneg : neg <;> simp [q_tgt, hneg, Fin.snoc_last]
    · have hjlt : j.1 < n := by have := j.isLt; have : j.1 ≠ n := fun h => hjn (Fin.ext h); omega
      exact False.elim (hi ⟨⟨1 + j.1, by omega⟩, by
        rw [embCN410_apply, dif_neg (by dsimp only; omega), dif_pos (by dsimp only; omega)]
        simpa using hj⟩)

lemma act_zNegGate410 (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (w : Qubits ℓ)
    (fc fh fq pub neg : Bool) (a : Qubits Amax) :
    act (embedOp (zNegGate410 (ps := ps) (r := r) (n := n) (M := M)).gate.mat
          (zNegGate410 (ps := ps) (r := r) (n := n) (M := M)).wires)
        (ket (packState410 c mode q w fc fh fq pub neg a)) =
      (if neg then (-1 : ℂ) else 1) • ket (packState410 c mode q w fc fh fq pub neg a) := by
  let z := packState410 (ps := ps) (r := r) (n := n) (M := M) c mode q w fc fh fq pub neg a
  change act (embedOp (pauliZ.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0))
      (singleWireEmb410 (ps := ps) (r := r) (n := n) (M := M) wireNeg)) (ket z) =
    (if neg then (-1 : ℂ) else 1) • ket z
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, embedOp, Matrix.of_apply,
    Matrix.submatrix_apply, ket, PiLp.single_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single z]
  · simp only [↓reduceIte, mul_one, Function.comp_apply, singleWireEmb410_apply, pauliZ,
      Matrix.diagonal_apply]
    by_cases hyz : y = z
    · subst hyz
      have hzn : z wireNeg = neg := packState410_Neg _ _ _ _ _ _ _ _ _ _
      simp [hzn]
    · rw [if_neg hyz, mul_zero]
      by_cases hout : ∀ a, a ∉ Set.range (singleWireEmb410 (ps := ps) (r := r) (n := n) (M := M) wireNeg) → y a = z a
      · have hne : y wireNeg ≠ z wireNeg := by
          intro heq; apply hyz; funext i
          by_cases hi : i = wireNeg
          · subst hi; exact heq
          · exact hout i (by rintro ⟨_, h⟩; exact hi h.symm)
        rw [if_pos hout, if_neg hne]
      · rw [if_neg hout]
  · intro u _ hu; rw [if_neg hu, mul_zero]
  · intro h; exact absurd (Finset.mem_univ z) h

noncomputable def liftedOracleCirc410 :
    OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (M' + 1) :=
  let np := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) negPrepCirc410
  let cn := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) (embedCircuit embCN410 (ps.cnCirc n))
  let zneg := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) [zNegGate410]
  np ++ cn ++ zneg ++ [queryStepFull410] ++ cn ++ np

lemma liftedOracleCirc410_queryCount :
    (liftedOracleCirc410 (ps := ps) (r := r) (n := n) (M := M)).queryCount 0 = 1 := by
  have hq : OracleCircuit.queryCount ([queryStepFull410 (ps := ps) (r := r) (n := n) (M := M)] :
      OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (M' + 1)) 0 = 1 := by
    simp [OracleCircuit.queryCount, OracleStep.IsQueryTo, queryStepFull410]
  dsimp only [liftedOracleCirc410]
  simp only [oracleCircuit_queryCount_append, liftToFull410_queryCount, hq]

lemma liftedOracleCirc410_gateCount :
    (liftedOracleCirc410 (ps := ps) (r := r) (n := n) (M := M)).gateCount =
      5 + 2 * ps.toffoliCirc.length + 2 * (ps.cnCirc n).length := by
  have hq : OracleCircuit.gateCount ([queryStepFull410 (ps := ps) (r := r) (n := n) (M := M)] :
      OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (M' + 1)) = 0 := by
    simp [OracleCircuit.gateCount, queryStepFull410]
  dsimp only [liftedOracleCirc410]
  simp only [oracleCircuit_gateCount_append, liftToFull410_gateCount, hq, negPrepCirc410_length,
    embedCircuit, List.length_map, List.length_singleton]
  ring

lemma liftedOracleCirc410_depth_le :
    nonOracleDepth (liftedOracleCirc410 (ps := ps) (r := r) (n := n) (M := M)) ≤
      5 + 2 * ps.toffoliDepth + 2 * ps.cnDepth n := by
  let a1 : Fin 1 → ℕ := fun _ => n + 1
  let np := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) negPrepCirc410
  let cn := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) (embedCircuit embCN410 (ps.cnCirc n))
  let zneg := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) [zNegGate410]
  have hnp : nonOracleDepth np ≤ 2 + ps.toffoliDepth := by
    refine le_trans (liftToFull410_depth_le _) ?_
    simp only [negPrepCirc410, List.map_append]
    have ha1 := nonOracleDepth_append
      ((([xLastGate410 (ps := ps) (r := r) (n := n) (M := M)] ++
          embedCircuit embToffoliNeg ps.toffoliCirc).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      ((([xLastGate410 (ps := ps) (r := r) (n := n) (M := M)]).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
    have ha2 := nonOracleDepth_append
      ((([xLastGate410 (ps := ps) (r := r) (n := n) (M := M)]).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
      (((embedCircuit embToffoliNeg ps.toffoliCirc).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
    have hx1 : nonOracleDepth (([xLastGate410 (ps := ps) (r := r) (n := n) (M := M)].map OracleStep.gate) :
        OracleCircuit gates12 a1 M') ≤ 1 :=
      le_trans (nonOracleDepth_le_length _) (by simp)
    have htof : nonOracleDepth (((embedCircuit embToffoliNeg ps.toffoliCirc).map OracleStep.gate) :
        OracleCircuit gates12 a1 M') ≤ ps.toffoliDepth :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.toffoli_hdepth 1 a1)
    simp only [List.map_append] at ha1
    omega
  have hcn : nonOracleDepth cn ≤ ps.cnDepth n :=
    le_trans (liftToFull410_depth_le _)
      (le_trans (nonOracleDepth_embedCircuit _ _) (ps.cn_hdepth n 1 a1))
  have hzneg : nonOracleDepth zneg ≤ 1 :=
    le_trans (liftToFull410_depth_le _) (le_trans (nonOracleDepth_le_length _) (by simp))
  have hq : nonOracleDepth ([queryStepFull410 (ps := ps) (r := r) (n := n) (M := M)] :
      OracleCircuit gates12 a1 (M' + 1)) = 0 :=
    nonOracleDepth_query_single _ _ _ _ _
  change nonOracleDepth (np ++ cn ++ zneg ++ [queryStepFull410] ++ cn ++ np) ≤ _
  have d1 := nonOracleDepth_append (np ++ cn ++ zneg ++ [queryStepFull410] ++ cn) np
  have d2 := nonOracleDepth_append (np ++ cn ++ zneg ++ [queryStepFull410]) cn
  have d3 := nonOracleDepth_append (np ++ cn ++ zneg) [queryStepFull410]
  have d4 := nonOracleDepth_append (np ++ cn) zneg
  have d5 := nonOracleDepth_append np cn
  omega

lemma act_liftedOracleCirc410 {k : ℕ} (A_bd : BoundedSupports n k)
    (c : Qubits r) (mode : Qubits qw) (q : Qubits n') (fq : Bool) :
    act ((liftedOracleCirc410 (ps := ps) (r := r) (n := n) (M := M)).unitary fun _ => majOracle A_bd.1)
        (withMinus (ket (packState410 c mode q (fun _ => false) false false fq false false (fun _ => false)))) =
      (if fq && majorityBit (liftOdd A_bd) q then (-1 : ℂ) else 1) •
        withMinus (ket (packState410 c mode q (fun _ => false) false false fq false false (fun _ => false))) := by
  let neg := fq && !(q (Fin.last n))
  let q' : Qubits n' := if neg then Fin.snoc (fun i : Fin n => !(Fin.init q i)) (q (Fin.last n)) else q
  let s0 := packState410 (ps := ps) (r := r) (n := n) (M := M)
    c mode q (fun _ => false) false false fq false false (fun _ => false)
  let s1 := packState410 (ps := ps) (r := r) (n := n) (M := M)
    c mode q (fun _ => false) false false fq false neg (fun _ => false)
  let s2 := packState410 (ps := ps) (r := r) (n := n) (M := M)
    c mode q' (fun _ => false) false false fq false neg (fun _ => false)
  have hnp1 : act ((liftToFull410 (ps := ps) (r := r) (n := n) (M := M) negPrepCirc410).unitary
      fun _ => majOracle A_bd.1) (withMinus (ket s0)) = withMinus (ket s1) := by
    rw [liftToFull410_act, act_negPrepCirc410]
    simp [s1, neg]
  have hcn1 : act ((liftToFull410 (ps := ps) (r := r) (n := n) (M := M)
      (embedCircuit embCN410 (ps.cnCirc n))).unitary fun _ => majOracle A_bd.1) (withMinus (ket s1)) =
      withMinus (ket s2) := by
    rw [liftToFull410_act, act_cnEmbedCirc410]
  have hzneg : act ((liftToFull410 (ps := ps) (r := r) (n := n) (M := M) [zNegGate410]).unitary
      fun _ => majOracle A_bd.1) (withMinus (ket s2)) =
      (if neg then (-1 : ℂ) else 1) • withMinus (ket s2) := by
    rw [liftToFull410_act]
    simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    rw [act_zNegGate410, withMinus_smul]
  have hqry : act (OracleCircuit.unitary [queryStepFull410 (ps := ps) (r := r) (n := n) (M := M)]
      fun _ => majOracle A_bd.1) (withMinus (ket s2)) =
      (if fq && majorityBit A_bd.1 (Fin.init q') then (-1 : ℂ) else 1) • withMinus (ket s2) := by
    have hqu : OracleCircuit.unitary [queryStepFull410 (ps := ps) (r := r) (n := n) (M := M)]
        (fun _ => majOracle A_bd.1) = OracleStep.mat (fun _ => majOracle A_bd.1) queryStepFull410 := by
      simp [OracleCircuit.unitary]
    rw [hqu]
    change act (OracleStep.mat (S := gates12) (fun _ => majOracle A_bd.1)
      (.query 0 false (some wireFQ.castSucc) oracleWires410 oracleWires410_hc)) (withMinus (ket s2)) = _
    rw [act_ctrl_majOracle_withMinus A_bd.1 wireFQ (Fin.castSuccEmb.trans regQ) oracleWires410
      oracleWires410_init oracleWires410_last oracleWires410_hc]
    have hphase : act (phaseCtrlOracle A_bd.1 wireFQ (Fin.castSuccEmb.trans regQ)) (ket s2) =
        (if fq && majorityBit A_bd.1 (Fin.init q') then (-1 : ℂ) else 1) • ket s2 := by
      ext y
      simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, phaseCtrlOracle,
        Matrix.diagonal_apply, ket, PiLp.single_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single s2]
      · by_cases hy : y = s2
        · subst hy
          have hfq_eq : s2 wireFQ = fq := packState410_FQ _ _ _ _ _ _ _ _ _ _
          have hq'_eq : s2 ∘ (Fin.castSuccEmb.trans regQ) = Fin.init q' := by
            funext i
            simp only [Function.comp_apply, Function.Embedding.trans_apply, Fin.castSuccEmb_apply, s2]
            rw [packState410_Q]; rfl
          rw [hfq_eq, hq'_eq]; simp
        · simp [hy]
      · intro z _ hz; simp [hz]
      · simp
    rw [hphase, withMinus_smul]
  have hcn2 : act ((liftToFull410 (ps := ps) (r := r) (n := n) (M := M)
      (embedCircuit embCN410 (ps.cnCirc n))).unitary fun _ => majOracle A_bd.1) (withMinus (ket s2)) =
      withMinus (ket s1) := by
    rw [liftToFull410_act, act_cnEmbedCirc410]
    congr 2; dsimp only [s1]
    have hqback : (if neg then Fin.snoc (fun i : Fin n => !(Fin.init q' i)) (q' (Fin.last n)) else q') = q := by
      cases hneg : neg
      · simp [q', hneg]
      · funext i
        refine Fin.lastCases ?_ ?_ i
        · simp [q', hneg]
        · intro j
          simp only [q', hneg, ↓reduceIte, Fin.snoc_castSucc, Fin.init_def, Bool.not_not]
    rw [hqback]
  have hnp2 : act ((liftToFull410 (ps := ps) (r := r) (n := n) (M := M) negPrepCirc410).unitary
      fun _ => majOracle A_bd.1) (withMinus (ket s1)) = withMinus (ket s0) := by
    rw [liftToFull410_act, act_negPrepCirc410]
    simp [s0, neg]
  dsimp only [liftedOracleCirc410]
  simp only [oracleCircuit_unitary_append, act_mul]
  rw [hnp1, hcn1, hzneg, act_smul, hqry, act_smul, act_smul, act_smul, hcn2, act_smul, hnp2, smul_smul]
  congr 1
  have hq_snoc : q = Fin.snoc (α := fun _ => Bool) (Fin.init q) (q (Fin.last n)) :=
    (Fin.snoc_init_self q).symm
  cases hfq : fq
  · simp [neg, hfq]
  · cases hql : q (Fin.last n)
    · have hnegT : neg = true := by simp [neg, hfq, hql]
      have hq'init : Fin.init q' = fun i : Fin n => !(Fin.init q i) := by
        simp [q', hnegT, Fin.init_snoc]
      have hmaj : majorityBit (liftOdd A_bd) q = !majorityBit A_bd.1 (fun i => !(Fin.init q i)) := by
        have h1 := liftOdd_majorityBit_snoc_false A_bd (fun i => !(Fin.init q i))
        have hinv : (fun i : Fin n => !(!(Fin.init q i))) = Fin.init q := funext fun i => Bool.not_not _
        rw [hinv] at h1
        conv_lhs => rw [hq_snoc, hql]
        exact h1
      rw [hnegT, hq'init, hmaj]
      cases majorityBit A_bd.1 (fun i => !(Fin.init q i)) <;> norm_num
    · have hnegF : neg = false := by simp [neg, hfq, hql]
      have hq'init : Fin.init q' = Fin.init q := by simp [q', hnegF]
      have hmaj : majorityBit (liftOdd A_bd) q = majorityBit A_bd.1 (Fin.init q) := by
        conv_lhs => rw [hq_snoc, hql]
        exact liftOdd_majorityBit_snoc_true A_bd (Fin.init q)
      rw [hnegF, hq'init, hmaj]
      cases majorityBit A_bd.1 (Fin.init q) <;> norm_num

noncomputable def stepCirc410 (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n') (c_step : Fin (2 ^ r)) :
    OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (M' + 1) :=
  let pat := natToBitsLSB r c_step.1
  let xc := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) (ctrl0XCirc410 pat)
  let fq := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) fqComputeCirc410
  let ubody := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) (uBodyCirc410 hM hle)
  xc ++ fq ++ liftedOracleCirc410 ++ fq ++ ubody ++ xc

lemma act_stepCirc410_basis {k : ℕ} (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n') (c_step : Fin (2 ^ r))
    (A_bd : BoundedSupports n k) (c : Qubits r) (mode : Qubits qw) (q : Qubits n') :
    act ((stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step).unitary fun _ => majOracle A_bd.1)
        (withMinus (ket (coreEmbHom410 (c, mode, q)))) =
      withMinus (
        if (if mode = modeKet M 0 then fun i => xor (c i) (natToBitsLSB r c_step.1 i) else c) = (fun _ => false) then
          (if mode ≠ modeKet M 0 && majorityBit (liftOdd A_bd) q then (-1 : ℂ) else 1) •
            ∑ p' : Qubits qw × Qubits n', (U_ideal410 M n' p' (mode, q)) •
              ket (coreEmbHom410 (if p'.1 = modeKet M 0 then natToBitsLSB r c_step.1 else fun _ => false, p'.1, p'.2))
        else
          ket (coreEmbHom410 (c, mode, q))) := by
  let pat := natToBitsLSB r c_step.1
  let c'' : Qubits r := if mode = modeKet M 0 then fun i => xor (c i) (pat i) else c
  let fqVal : Bool := decide (c'' = (fun _ => false) ∧ mode ≠ modeKet M 0)
  have h1 : act (ctrl0XCirc410 (ps := ps) (r := r) (n := n) (M := M) pat).unitary
      (ket (coreEmbHom410 (c, mode, q))) =
      ket (packState410 (ps := ps) c'' mode q (fun _ => false) false false false false false (fun _ => false)) := by
    change act (ctrl0XCirc410 pat).unitary
      (ket (packState410 c mode q (fun _ => false) false false false false false (fun _ => false))) = _
    rw [act_ctrl0XCirc410, ← modeKet_zero M]
    congr 2; by_cases hm : mode = modeKet M 0 <;> simp [c'', hm, pat]
  have h2 : act (fqComputeCirc410 (ps := ps) (r := r) (n := n) (M := M)).unitary
      (ket (packState410 (ps := ps) c'' mode q (fun _ => false) false false false false false (fun _ => false))) =
      ket (packState410 (ps := ps) c'' mode q (fun _ => false) false false fqVal false false (fun _ => false)) := by
    rw [act_fqComputeCirc410, ← modeKet_zero M]
    by_cases hc : c'' = (fun _ => false) <;> by_cases hm : mode = modeKet M 0 <;> simp [fqVal, hc, hm]
  have h3 : act ((liftedOracleCirc410 (ps := ps) (r := r) (n := n) (M := M)).unitary fun _ => majOracle A_bd.1)
      (withMinus (ket (packState410 (ps := ps) c'' mode q (fun _ => false) false false fqVal false false (fun _ => false)))) =
      (if fqVal && majorityBit (liftOdd A_bd) q then (-1 : ℂ) else 1) •
        withMinus (ket (packState410 (ps := ps) c'' mode q (fun _ => false) false false fqVal false false (fun _ => false))) :=
    act_liftedOracleCirc410 A_bd c'' mode q fqVal
  have h4 : act (fqComputeCirc410 (ps := ps) (r := r) (n := n) (M := M)).unitary
      (ket (packState410 (ps := ps) c'' mode q (fun _ => false) false false fqVal false false (fun _ => false))) =
      ket (packState410 (ps := ps) c'' mode q (fun _ => false) false false false false false (fun _ => false)) := by
    rw [act_fqComputeCirc410, ← modeKet_zero M]
    by_cases hc : c'' = (fun _ => false) <;> by_cases hm : mode = modeKet M 0 <;> simp [fqVal, hc, hm]
  simp only [stepCirc410, oracleCircuit_unitary_append, act_mul]
  rw [liftToFull410_act, h1, liftToFull410_act, h2, h3, act_smul, liftToFull410_act, h4,
    act_smul, liftToFull410_act, act_uBodyCirc410 hM hle]
  by_cases hc''0 : c'' = (fun _ => false)
  · have hif_pos : (if mode = modeKet M 0 then fun i => xor (c i) (natToBitsLSB r c_step.1 i) else c) =
        fun _ => false := hc''0
    have hfq_eq : (fqVal && majorityBit (liftOdd A_bd) q) =
        (mode ≠ modeKet M 0 && majorityBit (liftOdd A_bd) q) := by
      simp [fqVal, hc''0]
    rw [if_pos hc''0, if_pos hif_pos, hfq_eq, act_smul, liftToFull410_act, withMinus_smul, act_sum]
    have hfin : ∀ p' : Qubits qw × Qubits n',
        act (ctrl0XCirc410 (ps := ps) (r := r) (n := n) (M := M) (natToBitsLSB r c_step.1)).unitary
          ((U_ideal410 M n' p' (mode, q)) •
            ket (packState410 (ps := ps) c'' p'.1 p'.2 (fun _ => false) false false false false false (fun _ => false))) =
        (U_ideal410 M n' p' (mode, q)) •
          ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
            (if p'.1 = modeKet M 0 then natToBitsLSB r c_step.1 else fun _ => false, p'.1, p'.2)) := by
      intro p'
      rw [act_smul, hc''0, act_ctrl0XCirc410, ← modeKet_zero M]
      congr 2
      have hc_eq : (fun i : Fin r => if p'.1 = modeKet M 0 then xor false (natToBitsLSB r c_step.1 i) else false) =
          if p'.1 = modeKet M 0 then natToBitsLSB r c_step.1 else fun _ => false := by
        by_cases hp : p'.1 = modeKet M 0 <;> funext i <;> simp [hp]
      rw [hc_eq]
      rfl
    rw [Finset.sum_congr rfl fun p' _ => hfin p']
  · have hfq_f : fqVal = false := by simp [fqVal, hc''0]
    have hif_neg : ¬ ((if mode = modeKet M 0 then fun i => xor (c i) (natToBitsLSB r c_step.1 i) else c) =
        fun _ => false) := hc''0
    rw [if_neg hc''0, if_neg hif_neg, hfq_f]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, one_smul]
    rw [liftToFull410_act, act_ctrl0XCirc410, ← modeKet_zero M]
    congr 2
    have hback : (fun i : Fin r => if mode = modeKet M 0 then xor (c'' i) (natToBitsLSB r c_step.1 i) else c'' i) = c := by
      by_cases hm : mode = modeKet M 0 <;> funext i <;> simp [c'', hm, pat]
    rw [hback]
    rfl

end LiftedOracleAndStep410

section WalkCorrectnessAndComplexity410

variable {ps : PrimitiveSuite410} {r n M : ℕ}

local notation "qw" => qW M
local notation "ℓ" => Nat.clog 2 (n + 2)
local notation "Amax" => ancMax410 ps r n M
local notation "M'" => regM'410 ps r n M

private def qubitsConsEquiv (m : ℕ) : Qubits (m + 1) ≃ Bool × Qubits m where
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

private lemma majOracle_mem_unitaryGroup {n₀ : ℕ} (A : Finset (Fin n₀)) :
    majOracle A ∈ Matrix.unitaryGroup (Qubits (n₀ + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  let f : Qubits (n₀ + 1) → Qubits (n₀ + 1) := fun z =>
    Fin.snoc (α := fun _ => Bool) (Fin.init z)
      (xor (z (Fin.last n₀)) (decide (majJunta A (Finset.univ.filter fun i => Fin.init z i = true) = -1)))
  have hf_invol : ∀ z, f (f z) = z := fun z => by
    have hinit : Fin.init (f z) = Fin.init z := Fin.init_snoc _ _
    dsimp only [f]
    rw [hinit, Fin.snoc_last, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Fin.snoc_init_self]
  ext y z
  simp only [Matrix.mul_apply, Matrix.star_apply, majOracle, Matrix.of_apply, Matrix.one_apply]
  change ∑ x : Qubits (n₀ + 1), (if y = f x then (1 : ℂ) else 0) * star (if z = f x then (1 : ℂ) else 0) = _
  have hx_uniq : ∀ x : Qubits (n₀ + 1), y = f x ↔ x = f y := fun x => by
    constructor <;> intro h <;> rw [h, hf_invol]
  rw [Finset.sum_eq_single (f y)]
  · simp only [hf_invol, ↓reduceIte, one_mul]
    by_cases hyz : y = z
    · subst hyz; simp
    · simp [hyz, Ne.symm hyz]
  · intro x _ hx; have hne : y ≠ f x := fun h => hx ((hx_uniq x).mp h); simp [hne]
  · simp

private lemma oracleStep_mem_unitaryGroup {S : Set Gate} {a : Fin 1 → ℕ} {m₀ : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary)
    (orc : (k : Fin 1) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (horc : ∀ k, orc k ∈ Matrix.unitaryGroup (Qubits (a k)) ℂ)
    (st : OracleStep S a m₀) :
    OracleStep.mat orc st ∈ Matrix.unitaryGroup (Qubits m₀) ℂ := by
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

private lemma oracleCircuit_mem_unitaryGroup {S : Set Gate} {a : Fin 1 → ℕ} {m₀ : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary)
    (orc : (k : Fin 1) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (horc : ∀ k, orc k ∈ Matrix.unitaryGroup (Qubits (a k)) ℂ)
    (c : OracleCircuit S a m₀) :
    c.unitary orc ∈ Matrix.unitaryGroup (Qubits m₀) ℂ := by
  unfold OracleCircuit.unitary
  induction c with
  | nil => simp
  | cons st rest ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one] at ih ⊢
    exact Submonoid.mul_mem _ ih (oracleStep_mem_unitaryGroup hS orc horc st)

private lemma act_norm_of_mem_unitaryGroup410 {α : Type*} [Fintype α] [DecidableEq α]
    {U : Matrix α α ℂ} (hU : U ∈ Matrix.unitaryGroup α ℂ) (v : EuclideanSpace ℂ α) :
    ‖act U v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  have hunit : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hsum : ∀ (w : EuclideanSpace ℂ α),
      ((∑ x : α, ‖w x‖ ^ 2 : ℝ) : ℂ) = ∑ x : α, star (w x) * w x := fun w => by
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    have hmul : star (w x) * w x = (Complex.normSq (w x) : ℂ) := by
      simpa [mul_comm] using Complex.mul_conj (w x)
    rw [hmul, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  apply Complex.ofReal_injective
  rw [hsum, hsum]
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, star_sum, star_mul']
  calc ∑ x : α, (∑ y : α, star (U x y) * star (v y)) * ∑ z : α, U x z * v z
      = ∑ x : α, ∑ y : α, ∑ z : α, star (v y) * (star (U x y) * U x z) * v z := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by ring
    _ = ∑ y : α, ∑ z : α, star (v y) * (∑ x : α, star (U x y) * U x z) * v z := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ y : α, ∑ z : α, star (v y) * ((star U * U) y z) * v z := rfl
    _ = ∑ y : α, ∑ z : α, star (v y) * (if y = z then (1 : ℂ) else 0) * v z := by
        simp_rw [hunit, Matrix.one_apply]
    _ = ∑ y : α, star (v y) * v y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_eq_single y]
        · simp
        · intro z _ hz; simp [Ne.symm hz]
        · intro h; exact absurd (Finset.mem_univ y) h

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

private lemma act_ket_apply410 {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix α α ℂ) (a b : α) : act U (ket a) b = U b a := by
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply]
  rw [Finset.sum_eq_single a]
  · simp only [↓reduceIte, mul_one]
  · intro x _ hx; rw [if_neg hx, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

private lemma tensorVec_ket_eq_ket_prod {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (u : α) (v : β) : tensorVec (ket u) (ket v) = ket (u, v) := by
  ext ⟨a, b⟩
  simp [tensorVec, ket, PiLp.single_apply]
  by_cases ha : a = u <;> by_cases hb : b = v <;> simp [ha, hb]

private lemma wCatAfter410_mode_zero_eq_zero {m₀ M₀ l : ℕ} (B : Finset (Fin m₀)) (hB : B.card = 2 * l + 1)
    (S : Qubits m₀) :
    wCatAfter410 m₀ M₀ l B hB (modeKet M₀ 0, S) = 0 := by
  unfold wCatAfter410
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  have hne : modeKet M₀ 0 ≠ modeKet M₀ (c.1 + 1) :=
    modeKet_ne M₀ 0 (c.1 + 1) (by omega) (by omega) (by omega)
  simp [tensorVec, ket, PiLp.single_apply, hne]

noncomputable def ψStart410 (ps : PrimitiveSuite410) (r n M : ℕ) :
    EuclideanSpace ℂ (Qubits (regM'410 ps r n M)) :=
  (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
    ∑ c : Fin (2 ^ r), ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
      (natToBitsLSB r c.1, modeKet M 0, fun _ => false))

noncomputable def ψCat410 (ps : PrimitiveSuite410) (r n M m : ℕ)
    (B : Finset (Fin (n + 1))) (hB : B.card = 2 * m + 1) :
    EuclideanSpace ℂ (Qubits (regM'410 ps r n M)) :=
  (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
    ∑ p : Qubits (qW M) × Qubits (n + 1), (wCatVec410 (n + 1) M m B hB p) •
      ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (fun _ => false, p.1, p.2))

noncomputable def ψTarget410 (ps : PrimitiveSuite410) (r n M : ℕ) (B : Finset (Fin (n + 1))) :
    EuclideanSpace ℂ (Qubits (regM'410 ps r n M)) :=
  (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
    ∑ c : Fin (2 ^ r), ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
      (natToBitsLSB r c.1, modeKet M 0, fun i : Fin (n + 1) => decide (i ∈ B)))

noncomputable def ψIdeal410 (ps : PrimitiveSuite410) (r n M m : ℕ)
    (B : Finset (Fin (n + 1))) (hB : B.card = 2 * m + 1) (t : ℕ) :
    EuclideanSpace ℂ (Qubits (regM'410 ps r n M)) :=
  (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
    ((∑ c : Fin (2 ^ r), ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
        (natToBitsLSB r c.1, modeKet M 0,
          if c.1 < t then (fun i : Fin (n + 1) => decide (i ∈ B)) else (fun _ => false)))) +
      ∑ p : Qubits (qW M) × Qubits (n + 1), (wCatVec410 (n + 1) M m B hB p) •
        ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (fun _ => false, p.1, p.2)))

lemma ψIdeal410_zero (m : ℕ) (B : Finset (Fin (n + 1))) (hB : B.card = 2 * m + 1) :
    ψIdeal410 ps r n M m B hB 0 = ψStart410 ps r n M + ψCat410 ps r n M m B hB := by
  simp [ψIdeal410, ψStart410, ψCat410, smul_add]

lemma ψIdeal410_top (m : ℕ) (B : Finset (Fin (n + 1))) (hB : B.card = 2 * m + 1) :
    ψIdeal410 ps r n M m B hB (2 ^ r) = ψTarget410 ps r n M B + ψCat410 ps r n M m B hB := by
  have hsum : ∑ c : Fin (2 ^ r), ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
        (natToBitsLSB r c.1, modeKet M 0, if c.1 < 2 ^ r then (fun i : Fin (n + 1) => decide (i ∈ B)) else (fun _ => false))) =
      ∑ c : Fin (2 ^ r), ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
        (natToBitsLSB r c.1, modeKet M 0, fun i : Fin (n + 1) => decide (i ∈ B))) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [if_pos c.isLt]
  simp only [ψIdeal410, hsum, ψTarget410, ψCat410, smul_add]

lemma norm_sq_ψCat410 (m : ℕ) (B : Finset (Fin (n + 1))) (hB : B.card = 2 * m + 1) :
    ‖ψCat410 ps r n M m B hB‖ ^ 2 = ‖wCatVec410 (n + 1) M m B hB‖ ^ 2 / (2 ^ r : ℕ) := by
  have hnorm_sum : ‖∑ p : Qubits qw × Qubits (n + 1), (wCatVec410 (n + 1) M m B hB p) •
        ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (fun _ => false, p.1, p.2))‖ ^ 2 =
      ‖wCatVec410 (n + 1) M m B hB‖ ^ 2 := by
    let f : Qubits qw × Qubits (n + 1) → Qubits M' := fun p =>
      coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (fun _ => false, p.1, p.2)
    have hf_inj : Function.Injective f := fun p₁ p₂ h => by
      have h' := coreEmbHom410.injective h
      exact (Prod.ext_iff.mp h').2
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have hzero : ∀ y : Qubits M', y ∉ Finset.univ.image f →
        ‖(∑ p : Qubits qw × Qubits (n + 1), (wCatVec410 (n + 1) M m B hB p) • ket (f p)) y‖ ^ 2 = 0 := by
      intro y hy
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hy
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hs0 : (∑ p : Qubits qw × Qubits (n + 1), (wCatVec410 (n + 1) M m B hB p) * ket (f p) y) = 0 := by
        refine Finset.sum_eq_zero fun p _ => ?_
        have hne : y ≠ f p := Ne.symm (hy p)
        simp [ket, hne]
      rw [hs0, norm_zero, zero_pow (by norm_num)]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) (fun y _ hy => hzero y hy)]
    rw [Finset.sum_image (fun p₁ _ p₂ _ h => hf_inj h)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single p]
    · simp [ket]
    · intro p' _ hp'
      have hne : f p ≠ f p' := fun h => hp' (hf_inj h.symm)
      simp [ket, hne]
    · simp
  have h2pos : (0 : ℝ) < (2 ^ r : ℕ) := by positivity
  simp only [ψCat410, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    mul_pow, inv_pow, Real.sq_sqrt h2pos.le]
  rw [hnorm_sum]
  ring

lemma act_stepCirc410_ideal {k : ℕ} (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n + 1)
    (A_bd : BoundedSupports n k) (hmM : layerOf A_bd ≤ M)
    (t : ℕ) (ht : t < 2 ^ r) :
    let B := liftOdd A_bd
    let hB := (liftOdd_card_eq A_bd).1
    act ((stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle ⟨t, ht⟩).unitary
          fun _ => majOracle A_bd.1)
        (withMinus (ψIdeal410 ps r n M (layerOf A_bd) B hB t)) =
      withMinus (ψIdeal410 ps r n M (layerOf A_bd) B hB (t + 1)) := by
  intro B hB
  let m := layerOf A_bd
  let c_step : Fin (2 ^ r) := ⟨t, ht⟩
  let pat := natToBitsLSB r t
  let indB : Qubits (n + 1) := fun i => decide (i ∈ B)
  let stepU := (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step).unitary
    fun _ => majOracle A_bd.1
  have hother : ∀ c : Fin (2 ^ r), c ≠ c_step →
      act stepU (withMinus (ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
        (natToBitsLSB r c.1, modeKet M 0, if c.1 < t then indB else fun _ => false)))) =
      withMinus (ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
        (natToBitsLSB r c.1, modeKet M 0, if c.1 < t then indB else fun _ => false))) := by
    intro c hc
    dsimp only [stepU]
    rw [act_stepCirc410_basis hM hle c_step A_bd]
    have hne : (fun i : Fin r => xor (natToBitsLSB r c.1 i) (pat i)) ≠ (fun _ => false) := by
      intro heq
      apply hc; apply Fin.ext
      apply natToBitsLSB_inj_of_lt c.isLt ht
      funext i
      have hi := congrFun heq i
      dsimp only [pat] at hi
      cases h1 : natToBitsLSB r c.1 i <;> cases h2 : natToBitsLSB r t i <;> simp_all
    simp only [↓reduceIte]
    rw [if_neg (by simpa [c_step, pat] using hne)]
  have hslot : act stepU (withMinus (ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
        (pat, modeKet M 0, fun _ => false)))) =
      withMinus (∑ p' : Qubits qw × Qubits (n + 1), (U_ideal410 M (n + 1) p' (modeKet M 0, fun _ => false)) •
        ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
          (if p'.1 = modeKet M 0 then pat else fun _ => false, p'.1, p'.2))) := by
    dsimp only [stepU]
    rw [act_stepCirc410_basis hM hle c_step A_bd]
    simp [c_step, pat]
  have hcat_term : ∀ p : Qubits qw × Qubits (n + 1),
      act stepU (withMinus ((wCatVec410 (n + 1) M m B hB p) •
        ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (fun _ => false, p.1, p.2)))) =
      withMinus ((wCatAfter410 (n + 1) M m B hB p) •
        ∑ p' : Qubits qw × Qubits (n + 1), (U_ideal410 M (n + 1) p' p) •
          ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
            (if p'.1 = modeKet M 0 then pat else fun _ => false, p'.1, p'.2))) := by
    intro p
    by_cases hp0 : p.1 = modeKet M 0
    · have hw1 : wCatVec410 (n + 1) M m B hB p = 0 := by
        rcases p with ⟨m₀, S⟩; dsimp at hp0; subst hp0; exact wCatVec410_mode_zero_eq_zero B hB S
      have hw2 : wCatAfter410 (n + 1) M m B hB p = 0 := by
        rcases p with ⟨m₀, S⟩; dsimp at hp0; subst hp0; exact wCatAfter410_mode_zero_eq_zero B hB S
      rw [hw1, hw2, zero_smul, zero_smul, show withMinus (0 : EuclideanSpace ℂ (Qubits M')) = 0 by
        ext z; simp [withMinus], show act stepU 0 = 0 by ext y; simp [act]]
    · rw [withMinus_smul, act_smul]
      dsimp only [stepU]
      rw [act_stepCirc410_basis hM hle c_step A_bd]
      have hp_eq : (p.1, p.2) = p := Prod.mk.eta
      have hpat_eq : natToBitsLSB r c_step.1 = pat := rfl
      have hB_eq : liftOdd A_bd = B := rfl
      simp only [hp0, ↓reduceIte, ne_eq, not_false_eq_true, decide_true, Bool.true_and,
        withMinus_smul, hp_eq, hpat_eq, hB_eq]
      have hw_after : (wCatVec410 (n + 1) M m B hB p) * (if majorityBit B p.2 then (-1 : ℂ) else 1) =
          wCatAfter410 (n + 1) M m B hB p := by
        have hp := congrFun (congrArg WithLp.ofLp (act_phaseCtrl410_wCatVec410 B hB)) p
        simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, phaseCtrl410,
          Matrix.of_apply] at hp
        rw [Fintype.sum_prod_type, Finset.sum_eq_single p.1] at hp
        · rw [Finset.sum_eq_single p.2] at hp
          · simp only [↓reduceIte, hp0, ne_eq, not_false_eq_true, true_and] at hp
            rw [← hp]; ring
          · intro q' _ hq'; simp [hq'.symm]
          · simp
        · intro m' _ hm'
          refine Finset.sum_eq_zero fun q' _ => ?_
          simp [hm'.symm]
        · simp
      rw [smul_smul, hw_after]
  have hcomb :
      act stepU (withMinus (ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
          (pat, modeKet M 0, fun _ => false)) +
        ∑ p : Qubits qw × Qubits (n + 1), (wCatVec410 (n + 1) M m B hB p) •
          ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (fun _ => false, p.1, p.2)))) =
      withMinus (ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
          (pat, modeKet M 0, indB)) +
        ∑ p : Qubits qw × Qubits (n + 1), (wCatVec410 (n + 1) M m B hB p) •
          ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (fun _ => false, p.1, p.2))) := by
    rw [withMinus_add, withMinus_sum, act_add, act_sum, hslot,
      Finset.sum_congr rfl fun p _ => hcat_term p]
    rw [← withMinus_sum, ← withMinus_add]
    congr 1
    have hcoeff_sum :
        (∑ p' : Qubits qw × Qubits (n + 1), (U_ideal410 M (n + 1) p' (modeKet M 0, fun _ => false)) •
          ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
            (if p'.1 = modeKet M 0 then pat else fun _ => false, p'.1, p'.2))) +
        ∑ p : Qubits qw × Qubits (n + 1), (wCatAfter410 (n + 1) M m B hB p) •
          ∑ p' : Qubits qw × Qubits (n + 1), (U_ideal410 M (n + 1) p' p) •
            ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
              (if p'.1 = modeKet M 0 then pat else fun _ => false, p'.1, p'.2)) =
        ∑ p' : Qubits qw × Qubits (n + 1),
          (act (U_ideal410 M (n + 1)) (tensorVec (ket (modeKet M 0)) (zeroKet (n + 1)) +
            wCatAfter410 (n + 1) M m B hB)) p' •
            ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
              (if p'.1 = modeKet M 0 then pat else fun _ => false, p'.1, p'.2)) := by
      have hswap : (∑ p : Qubits qw × Qubits (n + 1), (wCatAfter410 (n + 1) M m B hB p) •
            ∑ p' : Qubits qw × Qubits (n + 1), (U_ideal410 M (n + 1) p' p) •
              ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
                (if p'.1 = modeKet M 0 then pat else fun _ => false, p'.1, p'.2))) =
          ∑ p' : Qubits qw × Qubits (n + 1),
            (∑ p : Qubits qw × Qubits (n + 1), wCatAfter410 (n + 1) M m B hB p * U_ideal410 M (n + 1) p' p) •
              ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
                (if p'.1 = modeKet M 0 then pat else fun _ => false, p'.1, p'.2)) := by
        simp_rw [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p' _ => ?_
        rw [← Finset.sum_smul]
      rw [hswap, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [← add_smul]
      have htz : tensorVec (ket (modeKet M 0)) (zeroKet (n + 1)) =
          ket (modeKet M 0, (fun _ : Fin (n + 1) => false)) :=
        tensorVec_ket_eq_ket_prod (modeKet M 0) (fun _ => false)
      have hact_eq : (act (U_ideal410 M (n + 1)) (tensorVec (ket (modeKet M 0)) (zeroKet (n + 1)) +
            wCatAfter410 (n + 1) M m B hB)) p' =
          U_ideal410 M (n + 1) p' (modeKet M 0, fun _ => false) +
            ∑ x : Qubits qw × Qubits (n + 1), wCatAfter410 (n + 1) M m B hB x * U_ideal410 M (n + 1) p' x := by
        rw [htz, act_add, WithLp.ofLp_add, Pi.add_apply, act_ket_apply410]
        exact congrArg (U_ideal410 M (n + 1) p' (modeKet M 0, fun _ => false) + ·) (by
          simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct]
          exact Finset.sum_congr rfl fun x _ => mul_comm _ _)
      exact congrArg (· • ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
        (if p'.1 = modeKet M 0 then pat else fun _ => false, p'.1, p'.2))) hact_eq.symm
    have htrans := U_ideal410_transduces (n' := n + 1) (M := M) (m := m) hM hmM (by omega) B hB
    have htrans_pt : ∀ p' : Qubits qw × Qubits (n + 1),
        (act (U_ideal410 M (n + 1)) (tensorVec (ket (modeKet M 0)) (zeroKet (n + 1)) +
          wCatAfter410 (n + 1) M m B hB)) p' =
        (tensorVec (ket (modeKet M 0)) (ket indB) + wCatVec410 (n + 1) M m B hB) p' :=
      fun p' => congrFun (congrArg WithLp.ofLp htrans) p'
    rw [hcoeff_sum, Finset.sum_congr rfl fun p' _ => by rw [htrans_pt p']]
    rw [Fintype.sum_prod_type]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (modeKet M 0))]
    have h0_part : (∑ q' : Qubits (n + 1),
          (tensorVec (ket (modeKet M 0)) (ket indB) + wCatVec410 (n + 1) M m B hB) (modeKet M 0, q') •
            ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
              (pat, modeKet M 0, q'))) =
        ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (pat, modeKet M 0, indB)) := by
      rw [Finset.sum_eq_single indB]
      · have hzero : wCatVec410 (n + 1) M m B hB (modeKet M 0, indB) = 0 :=
          wCatVec410_mode_zero_eq_zero (M := M) B hB indB
        have hket1 : tensorVec (ket (modeKet M 0)) (ket indB) (modeKet M 0, indB) = 1 := by
          rw [tensorVec_ket_eq_ket_prod]; simp [ket]
        rw [WithLp.ofLp_add, Pi.add_apply, hket1, hzero, add_zero, one_smul]
      · intro q' _ hq'
        have hzero : wCatVec410 (n + 1) M m B hB (modeKet M 0, q') = 0 :=
          wCatVec410_mode_zero_eq_zero (M := M) B hB q'
        have hket0 : tensorVec (ket (modeKet M 0)) (ket indB) (modeKet M 0, q') = 0 := by
          rw [tensorVec_ket_eq_ket_prod]; simp [ket, hq'.symm]
        rw [WithLp.ofLp_add, Pi.add_apply, hket0, hzero, add_zero, zero_smul]
      · simp
    have h0_empty : (∑ q' : Qubits (n + 1),
          (wCatVec410 (n + 1) M m B hB (modeKet M 0, q')) •
            ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
              (fun _ => false, modeKet M 0, q'))) = 0 := by
      refine Finset.sum_eq_zero fun q' _ => ?_
      rw [wCatVec410_mode_zero_eq_zero (M := M) B hB q', zero_smul]
    have hne_part : ∀ m' ∈ Finset.univ.erase (modeKet M 0),
        (∑ q' : Qubits (n + 1),
          (tensorVec (ket (modeKet M 0)) (ket indB) + wCatVec410 (n + 1) M m B hB) (m', q') •
            ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
              (if m' = modeKet M 0 then pat else fun _ => false, m', q'))) =
        ∑ q' : Qubits (n + 1),
          (wCatVec410 (n + 1) M m B hB (m', q')) •
            ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (fun _ => false, m', q')) := by
      intro m' hm'
      have hne : m' ≠ modeKet M 0 := (Finset.mem_erase.mp hm').1
      refine Finset.sum_congr rfl fun q' _ => ?_
      have hket0 : tensorVec (ket (modeKet M 0)) (ket indB) (m', q') = 0 := by
        rw [tensorVec_ket_eq_ket_prod]
        simp [ket, hne]
      rw [if_neg hne, WithLp.ofLp_add, Pi.add_apply, hket0, zero_add]
    simp only [↓reduceIte]
    rw [h0_part, Finset.sum_congr rfl hne_part]
    congr 1
    symm
    rw [Fintype.sum_prod_type, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (modeKet M 0)),
      h0_empty, zero_add]
  have hsplit_t : ψIdeal410 ps r n M m B hB t =
      (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
        ((∑ c ∈ Finset.univ.erase c_step, ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
            (natToBitsLSB r c.1, modeKet M 0, if c.1 < t then indB else fun _ => false))) +
         (ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (pat, modeKet M 0, fun _ => false)) +
          ∑ p : Qubits qw × Qubits (n + 1), (wCatVec410 (n + 1) M m B hB p) •
            ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (fun _ => false, p.1, p.2)))) := by
    unfold ψIdeal410
    congr 1
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c_step)]
    have hltf : ¬ (c_step.1 < t) := by dsimp [c_step]; omega
    simp only [hltf, ↓reduceIte]
    abel
  have hsplit_succ : ψIdeal410 ps r n M m B hB (t + 1) =
      (((Real.sqrt (2 ^ r : ℕ))⁻¹ : ℝ) : ℂ) •
        ((∑ c ∈ Finset.univ.erase c_step, ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
            (natToBitsLSB r c.1, modeKet M 0, if c.1 < t then indB else fun _ => false))) +
         (ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (pat, modeKet M 0, indB)) +
          ∑ p : Qubits qw × Qubits (n + 1), (wCatVec410 (n + 1) M m B hB p) •
            ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M) (fun _ => false, p.1, p.2)))) := by
    unfold ψIdeal410
    congr 1
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c_step)]
    have hlt_succ : c_step.1 < t + 1 := by dsimp [c_step]; omega
    have hrest : ∑ c ∈ Finset.univ.erase c_step,
          ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
            (natToBitsLSB r c.1, modeKet M 0, if c.1 < t + 1 then indB else fun _ => false)) =
        ∑ c ∈ Finset.univ.erase c_step,
          ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
            (natToBitsLSB r c.1, modeKet M 0, if c.1 < t then indB else fun _ => false)) := by
      refine Finset.sum_congr rfl fun c hc => ?_
      have hne : c.1 ≠ t := fun h => (Finset.mem_erase.mp hc).1 (Fin.ext h)
      have hiff : c.1 < t + 1 ↔ c.1 < t := by omega
      simp [hiff]
    rw [if_pos hlt_succ, hrest]
    abel
  rw [hsplit_t, withMinus_smul, act_smul, withMinus_add, act_add, withMinus_sum, act_sum]
  have hother_sum : ∑ c ∈ Finset.univ.erase c_step,
        act stepU (withMinus (ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
          (natToBitsLSB r c.1, modeKet M 0, if c.1 < t then indB else fun _ => false)))) =
      ∑ c ∈ Finset.univ.erase c_step,
        withMinus (ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
          (natToBitsLSB r c.1, modeKet M 0, if c.1 < t then indB else fun _ => false))) :=
    Finset.sum_congr rfl fun c hc => hother c (Finset.mem_erase.mp hc).1
  rw [hother_sum, hcomb, ← withMinus_sum, ← withMinus_add, ← withMinus_smul, ← hsplit_succ]

noncomputable def loopPrefix410 (ps : PrimitiveSuite410) (r n M : ℕ) (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n + 1) :
    (t : ℕ) → t ≤ 2 ^ r → OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (regM'410 ps r n M + 1)
  | 0, _ => []
  | t + 1, ht => loopPrefix410 ps r n M hM hle t (Nat.le_of_lt ht) ++
      stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle ⟨t, ht⟩

lemma loopPrefix410_queryCount (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n + 1) :
    ∀ (t : ℕ) (ht : t ≤ 2 ^ r),
      (loopPrefix410 ps r n M hM hle t ht).queryCount 0 = t := by
  intro t
  induction t with
  | zero => intro _; simp [loopPrefix410, OracleCircuit.queryCount]
  | succ t ih =>
    intro ht
    simp only [loopPrefix410, oracleCircuit_queryCount_append, ih (Nat.le_of_lt ht)]
    have hq_step : (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle ⟨t, ht⟩).queryCount 0 = 1 := by
      rw [stepCirc410]
      simp only [oracleCircuit_queryCount_append, liftToFull410_queryCount, liftedOracleCirc410_queryCount]
    omega

noncomputable def fullCirc410 (ps : PrimitiveSuite410) (r n M : ℕ) (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n + 1) :
    OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (regM'410 ps r n M + 1) :=
  [prepareMinusStep410 (n := n) (regM'410 ps r n M)] ++
  liftToFull410 (ps := ps) (r := r) (n := n) (M := M) (hadamardLayerC410 (ps := ps) (r := r) (n := n) (M := M)) ++
  loopPrefix410 ps r n M hM hle (2 ^ r) le_rfl

lemma fullCirc410_correct {k : ℕ} (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n + 1)
    (A_bd : BoundedSupports n k) (hmM : layerOf A_bd ≤ M)
    {ε : ℝ} (hK : 4 * ‖wCatVec410 (n + 1) M (layerOf A_bd) (liftOdd A_bd) (liftOdd_card_eq A_bd).1‖ ^ 2 / (2 ^ r : ℕ) ≤ ε) :
    open Classical in
    probEvent (act ((fullCirc410 ps r n M hM hle).unitary fun _ => majOracle A_bd.1)
          (zeroKet (regM'410 ps r n M + 1)))
      (fun z => ∀ i : Fin n,
        z (((Fin.castSuccEmb.trans (regQ (ps := ps) (r := r) (n := n) (M := M))).trans (Fin.castAddEmb 1)) i) =
          decide (i ∈ A_bd.1)) ≥ 1 - ε := by
  let B := liftOdd A_bd
  have hB : B.card = 2 * layerOf A_bd + 1 := (liftOdd_card_eq A_bd).1
  let Uloop := (loopPrefix410 ps r n M hM hle (2 ^ r) le_rfl).unitary fun _ => majOracle A_bd.1
  have hloop_ideal : ∀ (t : ℕ) (ht : t ≤ 2 ^ r),
      act ((loopPrefix410 ps r n M hM hle t ht).unitary fun _ => majOracle A_bd.1)
        (withMinus (ψIdeal410 ps r n M (layerOf A_bd) B hB 0)) =
      withMinus (ψIdeal410 ps r n M (layerOf A_bd) B hB t) := by
    intro t
    induction t with
    | zero => intro _; simp [loopPrefix410, OracleCircuit.unitary, act_one_vec]
    | succ t ih =>
      intro ht
      simp only [loopPrefix410, oracleCircuit_unitary_append, act_mul]
      rw [ih (Nat.le_of_lt ht), act_stepCirc410_ideal hM hle A_bd hmM t ht]
  have hloop_full := hloop_ideal (2 ^ r) le_rfl
  rw [ψIdeal410_zero, ψIdeal410_top] at hloop_full
  have hU_mem : Uloop ∈ Matrix.unitaryGroup (Qubits (M' + 1)) ℂ :=
    oracleCircuit_mem_unitaryGroup (fun _ hg => hg.1) _ (fun _ => majOracle_mem_unitaryGroup A_bd.1) _
  have hstart_prep :
      act (OracleCircuit.unitary ([prepareMinusStep410 (n := n) M'] ++
          liftToFull410 (ps := ps) (r := r) (n := n) (M := M) hadamardLayerC410) fun _ => majOracle A_bd.1)
        (zeroKet (M' + 1)) =
      withMinus (ψStart410 ps r n M) := by
    rw [oracleCircuit_unitary_append, act_mul]
    have hp : act (OracleCircuit.unitary [prepareMinusStep410 (n := n) M'] fun _ => majOracle A_bd.1)
        (zeroKet (M' + 1)) = withMinus (zeroKet M') := by
      simp [OracleCircuit.unitary, act_prepareMinusStep410]
    rw [hp, liftToFull410_act, act_hadamardLayerC410]
    congr 1; unfold ψStart410
    simp_rw [modeKet_zero M]
  have hfinal_eq :
      act ((fullCirc410 ps r n M hM hle).unitary fun _ => majOracle A_bd.1) (zeroKet (M' + 1)) =
      act Uloop (withMinus (ψStart410 ps r n M)) := by
    rw [oracleCircuit_unitary_append, act_mul] at hstart_prep
    simp only [fullCirc410, oracleCircuit_unitary_append, act_mul, hstart_prep]
    rfl
  have hnorm_final : ‖act ((fullCirc410 ps r n M hM hle).unitary fun _ => majOracle A_bd.1) (zeroKet (M' + 1))‖ = 1 := by
    have hfull_mem : (fullCirc410 ps r n M hM hle).unitary (fun _ => majOracle A_bd.1) ∈
        Matrix.unitaryGroup (Qubits (M' + 1)) ℂ :=
      oracleCircuit_mem_unitaryGroup (fun _ hg => hg.1) _ (fun _ => majOracle_mem_unitaryGroup A_bd.1) _
    rw [act_norm_of_mem_unitaryGroup410 hfull_mem]
    simp [zeroKet, ket]
  have hsub : act Uloop (withMinus (ψStart410 ps r n M)) - withMinus (ψTarget410 ps r n M B) =
      withMinus (ψCat410 ps r n M (layerOf A_bd) B hB) -
        act Uloop (withMinus (ψCat410 ps r n M (layerOf A_bd) B hB)) := by
    have h1 : act Uloop (withMinus (ψStart410 ps r n M)) =
        act Uloop (withMinus (ψStart410 ps r n M) + withMinus (ψCat410 ps r n M (layerOf A_bd) B hB)) -
          act Uloop (withMinus (ψCat410 ps r n M (layerOf A_bd) B hB)) := by
      rw [act_add]; abel
    rw [h1, ← withMinus_add, hloop_full, withMinus_add]
    abel
  have hdist_sq :
      ‖act ((fullCirc410 ps r n M hM hle).unitary fun _ => majOracle A_bd.1) (zeroKet (M' + 1)) -
        withMinus (ψTarget410 ps r n M B)‖ ^ 2 ≤ ε := by
    rw [hfinal_eq, hsub]
    have htri : ‖withMinus (ψCat410 ps r n M (layerOf A_bd) B hB) -
          act Uloop (withMinus (ψCat410 ps r n M (layerOf A_bd) B hB))‖ ≤
        2 * ‖ψCat410 ps r n M (layerOf A_bd) B hB‖ := by
      calc ‖withMinus (ψCat410 ps r n M (layerOf A_bd) B hB) -
            act Uloop (withMinus (ψCat410 ps r n M (layerOf A_bd) B hB))‖
          ≤ ‖withMinus (ψCat410 ps r n M (layerOf A_bd) B hB)‖ +
            ‖act Uloop (withMinus (ψCat410 ps r n M (layerOf A_bd) B hB))‖ := norm_sub_le _ _
        _ = ‖ψCat410 ps r n M (layerOf A_bd) B hB‖ + ‖ψCat410 ps r n M (layerOf A_bd) B hB‖ := by
            rw [act_norm_of_mem_unitaryGroup410 hU_mem, withMinus_norm]
        _ = 2 * ‖ψCat410 ps r n M (layerOf A_bd) B hB‖ := (two_mul _).symm
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, norm_sq_ψCat410, mul_div_assoc'] at hsq
    linarith
  have hsupp : ∀ z : Qubits (M' + 1),
      ¬ (∀ i : Fin n,
        z (((Fin.castSuccEmb.trans (regQ (ps := ps) (r := r) (n := n) (M := M))).trans (Fin.castAddEmb 1)) i) =
          decide (i ∈ A_bd.1)) →
      withMinus (ψTarget410 ps r n M B) z = 0 := by
    intro z hz
    simp only [withMinus, ψTarget410, WithLp.ofLp_toLp, WithLp.ofLp_smul, WithLp.ofLp_sum,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    have hsum0 : (∑ c : Fin (2 ^ r),
        ket (coreEmbHom410 (ps := ps) (r := r) (n := n) (M := M)
          (natToBitsLSB r c.1, modeKet M 0, fun i : Fin (n + 1) => decide (i ∈ B))) (Fin.init z)) = 0 := by
      refine Finset.sum_eq_zero fun c _ => ?_
      simp only [ket, PiLp.single_apply]
      split_ifs with heq
      · exfalso; apply hz; intro i
        have hi' := congrFun heq (regQ i.castSucc)
        rw [coreEmbHom410_apply, coreEmb410, packState410_Q] at hi'
        have heq_wire :
            ((Fin.castSuccEmb.trans (regQ (ps := ps) (r := r) (n := n) (M := M))).trans (Fin.castAddEmb 1)) i =
              (regQ (ps := ps) (r := r) (n := n) (M := M) i.castSucc).castSucc :=
          Fin.ext (by simp [Fin.castAddEmb])
        rw [heq_wire]
        change Fin.init z (regQ i.castSucc) = _
        rw [hi']
        dsimp only [B]
        have hb : i.castSucc ∈ liftOdd A_bd ↔ i ∈ A_bd.1 := liftOdd_mem_castSucc A_bd i
        by_cases h : i ∈ A_bd.1
        · rw [decide_eq_true h, decide_eq_true (hb.mpr h)]
        · rw [decide_eq_false h, decide_eq_false (mt hb.mp h)]
      · rfl
    rw [hsum0, mul_zero, zero_mul]
  exact probEvent_ge_of_norm_sub_sq _ _ _ hnorm_final hsupp hdist_sq

lemma fullCirc410_queryCount (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n + 1) :
    (fullCirc410 ps r n M hM hle).queryCount 0 = 2 ^ r := by
  have hprep : OracleCircuit.queryCount ([prepareMinusStep410 (n := n) M'] :
      OracleCircuit gates12 (fun _ : Fin 1 => n + 1) (M' + 1)) 0 = 0 := by
    simp [OracleCircuit.queryCount, OracleStep.IsQueryTo, prepareMinusStep410]
  simp only [fullCirc410, oracleCircuit_queryCount_append,
    hprep, liftToFull410_queryCount, loopPrefix410_queryCount hM hle (2 ^ r) le_rfl]
  omega

private lemma nat_clog2_le410 (x : ℕ) : Nat.clog 2 x ≤ x := by
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

private lemma stepCirc410_gateCount_le (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n + 1)
    (hn2 : 2 ≤ n) (c_step : Fin (2 ^ r)) :
    ((stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step).gateCount : ℝ) ≤
      2 * r + 4 * ps.C_eq * (qw + 1) + 6 * ps.C_eq * (r + qw + 1) +
        9 + 2 * ps.toffoliCirc.length + 2 * ps.C_cn * n +
        4 * ps.C_eq * (qw + 2) + 2 * ps.C_ch * (n + 1) + 2 * ps.C_hc * (n + 1) * Real.log (n + 1) +
        ps.C_ut * (n + 1) * Real.log (n + 1) := by
  have hn'2 : 2 ≤ n + 1 := by omega
  have hn'3 : 3 ≤ n + 1 := by omega
  have hgc : (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step).gateCount =
      2 * r +
      4 * (ps.eqCirc qw (fun _ => false) pauliX pauliX_mem_unitaryGroup).length +
      2 * (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup).length +
      2 * (ps.eqCirc (r + qw) (fun _ => false) pauliX pauliX_mem_unitaryGroup).length +
      (5 + 2 * ps.toffoliCirc.length + 2 * (ps.cnCirc n).length) +
      2 * (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup).length +
      4 +
      4 * (ps.eqCirc (1 + qw) (patFCMode0 M) pauliX pauliX_mem_unitaryGroup).length +
      2 * (ps.chCirc (n + 1)).length +
      2 * (ps.hcCirc (n + 1)).length +
      (ps.uTilde410Circ M (n + 1) hM hle).length := by
    dsimp only [stepCirc410, uBodyCirc410]
    simp only [oracleCircuit_gateCount_append, liftToFull410_gateCount, liftedOracleCirc410_gateCount,
      ctrl0XCirc410_length, fqComputeCirc410_length, List.length_append, embedCircuit, List.length_map,
      hHatCirc410_length, ps.hcAdj_length]
    ring
  have heq_qw := (ps.eq_bound qw (fun _ => false) pauliX pauliX_mem_unitaryGroup).1
  have heq_r := (ps.eq_bound r (fun _ => false) pauliX pauliX_mem_unitaryGroup).1
  have heq_rqw := (ps.eq_bound (r + qw) (fun _ => false) pauliX pauliX_mem_unitaryGroup).1
  have heq_1qw := (ps.eq_bound (1 + qw) (patFCMode0 M) pauliX pauliX_mem_unitaryGroup).1
  have hcn := (ps.cn_bound n hn2).1
  have hch := (ps.ch_bound (n + 1) hn'2).1
  have hhc := (ps.hc_bound (n + 1) hn'2).1
  have hut := (ps.uTilde410_bound M (n + 1) hM hle hn'3).1
  have hCeq : 0 < ps.C_eq := ps.hC_eq_pos
  have heqr_le : ps.C_eq * ((r : ℝ) + 1) ≤ ps.C_eq * ((r : ℝ) + qw + 1) := by
    gcongr; linarith
  have hgc_r : ((stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step).gateCount : ℝ) =
      2 * (r : ℝ) +
      4 * ((ps.eqCirc qw (fun _ => false) pauliX pauliX_mem_unitaryGroup).length : ℝ) +
      4 * ((ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup).length : ℝ) +
      2 * ((ps.eqCirc (r + qw) (fun _ => false) pauliX pauliX_mem_unitaryGroup).length : ℝ) +
      9 + 2 * (ps.toffoliCirc.length : ℝ) + 2 * ((ps.cnCirc n).length : ℝ) +
      4 * ((ps.eqCirc (1 + qw) (patFCMode0 M) pauliX pauliX_mem_unitaryGroup).length : ℝ) +
      2 * ((ps.chCirc (n + 1)).length : ℝ) +
      2 * ((ps.hcCirc (n + 1)).length : ℝ) +
      ((ps.uTilde410Circ M (n + 1) hM hle).length : ℝ) := by
    have : (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step).gateCount =
        2 * r + 4 * (ps.eqCirc qw (fun _ => false) pauliX pauliX_mem_unitaryGroup).length +
        4 * (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup).length +
        2 * (ps.eqCirc (r + qw) (fun _ => false) pauliX pauliX_mem_unitaryGroup).length +
        9 + 2 * ps.toffoliCirc.length + 2 * (ps.cnCirc n).length +
        4 * (ps.eqCirc (1 + qw) (patFCMode0 M) pauliX pauliX_mem_unitaryGroup).length +
        2 * (ps.chCirc (n + 1)).length + 2 * (ps.hcCirc (n + 1)).length +
        (ps.uTilde410Circ M (n + 1) hM hle).length := by rw [hgc]; ring
    exact_mod_cast this
  rw [hgc_r]
  push_cast at heq_qw heq_r heq_rqw heq_1qw heqr_le hch hhc hut
  linarith

private lemma loopPrefix410_gateCount_le (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n + 1)
    {G : ℝ} (hG : ∀ c_step : Fin (2 ^ r),
      ((stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step).gateCount : ℝ) ≤ G) :
    ∀ (t : ℕ) (ht : t ≤ 2 ^ r),
      ((loopPrefix410 ps r n M hM hle t ht).gateCount : ℝ) ≤ (t : ℝ) * G := by
  intro t
  induction t with
  | zero => intro _; simp [loopPrefix410, OracleCircuit.gateCount]
  | succ t ih =>
    intro ht
    simp only [loopPrefix410, oracleCircuit_gateCount_append, Nat.cast_add]
    have h1 := ih (Nat.le_of_lt ht)
    have h2 := hG ⟨t, ht⟩
    push_cast
    linarith

private lemma stepCirc410_nonOracleDepth_le (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n + 1)
    (hn2 : 2 ≤ n) (c_step : Fin (2 ^ r)) :
    (nonOracleDepth (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step) : ℝ) ≤
      2 * r + 4 * ps.C_eq * (qw + 2) + 6 * ps.C_eq * (r + qw + 2) +
        4 * ps.C_eq * (qw + 3) + 9 + 2 * ps.toffoliDepth + 2 * ps.C_cn * Real.log n +
        2 * ps.C_ch * Real.log (n + 1) + 2 * ps.C_hc * Real.log (n + 1) + ps.C_ut * Real.log (n + 1) := by
  have hn'2 : 2 ≤ n + 1 := by omega
  have hn'3 : 3 ≤ n + 1 := by omega
  let a1 : Fin 1 → ℕ := fun _ => n + 1
  have hxc_d : nonOracleDepth (liftToFull410 (ps := ps) (r := r) (n := n) (M := M)
      (ctrl0XCirc410 (natToBitsLSB r c_step.1))) ≤ 2 * ps.eqDepth qw + r := by
    refine le_trans (liftToFull410_depth_le _) ?_
    simp only [ctrl0XCirc410, List.map_append]
    have ha1 := nonOracleDepth_append
      (((embedCircuit (embEqPub (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc qw (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
          List.ofFn (ctrl0XStepGate410 (ps := ps) (r := r) (n := n) (M := M) (natToBitsLSB r c_step.1))).map
          OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((embedCircuit (embEqPub (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc qw (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map
          OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha2 := nonOracleDepth_append
      (((embedCircuit (embEqPub (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc qw (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map
          OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((List.ofFn (ctrl0XStepGate410 (ps := ps) (r := r) (n := n) (M := M) (natToBitsLSB r c_step.1))).map
          OracleStep.gate) : OracleCircuit gates12 a1 M')
    have heq_d : nonOracleDepth ((embedCircuit (embEqPub (ps := ps) (r := r) (n := n) (M := M))
        (ps.eqCirc qw (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map
        OracleStep.gate : OracleCircuit gates12 a1 M') ≤ ps.eqDepth qw :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.eq_hdepth _ _ _ _ 1 a1)
    have hmid_d : nonOracleDepth (((List.ofFn (ctrl0XStepGate410 (ps := ps) (r := r) (n := n) (M := M)
        (natToBitsLSB r c_step.1))).map OracleStep.gate) : OracleCircuit gates12 a1 M') ≤ r :=
      le_trans (nonOracleDepth_le_length _) (by simp)
    simp only [List.map_append] at ha1
    omega
  have hfq_d : nonOracleDepth (liftToFull410 (ps := ps) (r := r) (n := n) (M := M) fqComputeCirc410) ≤
      ps.eqDepth r + ps.eqDepth (r + qw) := by
    refine le_trans (liftToFull410_depth_le _) ?_
    simp only [fqComputeCirc410, List.map_append]
    have ha1 := nonOracleDepth_append
      (((embedCircuit (embEqFQC (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map
          OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((embedCircuit (embEqFQCMode (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc (r + qw) (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map
          OracleStep.gate) : OracleCircuit gates12 a1 M')
    have dr : nonOracleDepth ((embedCircuit (embEqFQC (ps := ps) (r := r) (n := n) (M := M))
        (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map
        OracleStep.gate : OracleCircuit gates12 a1 M') ≤ ps.eqDepth r :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.eq_hdepth _ _ _ _ 1 a1)
    have drq : nonOracleDepth ((embedCircuit (embEqFQCMode (ps := ps) (r := r) (n := n) (M := M))
        (ps.eqCirc (r + qw) (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map
        OracleStep.gate : OracleCircuit gates12 a1 M') ≤ ps.eqDepth (r + qw) :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.eq_hdepth _ _ _ _ 1 a1)
    omega
  have hlifted_d : nonOracleDepth (liftedOracleCirc410 (ps := ps) (r := r) (n := n) (M := M)) ≤
      5 + 2 * ps.toffoliDepth + 2 * ps.cnDepth n := liftedOracleCirc410_depth_le
  have hhat_d : nonOracleDepth ((hHatCirc410 (ps := ps) (r := r) (n := n) (M := M)).map OracleStep.gate :
      OracleCircuit gates12 a1 M') ≤ 2 + 2 * ps.eqDepth (1 + qw) + ps.chDepth (n + 1) := by
    let cnotFCH : GateApp gates12 M' := cnotGateAt410 wireFC wireFH (by
      intro h; have hv := congrArg Fin.val h; simp only [wireFC_val, wireFH_val] at hv; omega)
    let eqFH := embedCircuit (embEqFHMode0 (ps := ps) (r := r) (n := n) (M := M))
      (ps.eqCirc (1 + qw) (patFCMode0 M) pauliX pauliX_mem_unitaryGroup)
    let ch := embedCircuit (embCH410 (ps := ps) (r := r) (n := n) (M := M)) (ps.chCirc (n + 1))
    change nonOracleDepth ((([cnotFCH] ++ eqFH ++ ch ++ eqFH ++ [cnotFCH]).map OracleStep.gate) :
      OracleCircuit gates12 a1 M') ≤ _
    simp only [List.map_append]
    have ha1 := nonOracleDepth_append
      ((([cnotFCH] ++ eqFH ++ ch ++ eqFH).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      ((([cnotFCH]).map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha2 := nonOracleDepth_append
      ((([cnotFCH] ++ eqFH ++ ch).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      ((eqFH.map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha3 := nonOracleDepth_append
      ((([cnotFCH] ++ eqFH).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      ((ch.map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha4 := nonOracleDepth_append
      ((([cnotFCH]).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      ((eqFH.map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have hcnot_d : nonOracleDepth ((([cnotFCH]).map OracleStep.gate) : OracleCircuit gates12 a1 M') ≤ 1 :=
      le_trans (nonOracleDepth_le_length _) (by simp)
    have heq_d : nonOracleDepth ((eqFH.map OracleStep.gate) : OracleCircuit gates12 a1 M') ≤ ps.eqDepth (1 + qw) :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.eq_hdepth _ _ _ _ 1 a1)
    have hch_d : nonOracleDepth ((ch.map OracleStep.gate) : OracleCircuit gates12 a1 M') ≤ ps.chDepth (n + 1) :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.ch_hdepth (n + 1) 1 a1)
    simp only [List.map_append] at ha1 ha2 ha3
    omega
  have hubody_d : nonOracleDepth (liftToFull410 (ps := ps) (r := r) (n := n) (M := M) (uBodyCirc410 hM hle)) ≤
      2 * ps.eqDepth r + 4 + 4 * ps.eqDepth (1 + qw) + 2 * ps.chDepth (n + 1) + 2 * ps.hcDepth (n + 1) +
        ps.uTilde410Depth M (n + 1) := by
    refine le_trans (liftToFull410_depth_le _) ?_
    simp only [uBodyCirc410, List.map_append]
    have ha1 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
        hHatCirc410 ++
        embedCircuit embHC410 (ps.hcCirc (n + 1)) ++
        embedCircuit embUTilde410 (ps.uTilde410Circ M (n + 1) hM hle) ++
        embedCircuit embHC410 (ps.hcAdjCirc (n + 1)) ++
        hHatCirc410).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((embedCircuit embEqFC (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map
        OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha2 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
        hHatCirc410 ++
        embedCircuit embHC410 (ps.hcCirc (n + 1)) ++
        embedCircuit embUTilde410 (ps.uTilde410Circ M (n + 1) hM hle) ++
        embedCircuit embHC410 (ps.hcAdjCirc (n + 1))).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((hHatCirc410 (ps := ps) (r := r) (n := n) (M := M)).map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha3 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
        hHatCirc410 ++
        embedCircuit embHC410 (ps.hcCirc (n + 1)) ++
        embedCircuit embUTilde410 (ps.uTilde410Circ M (n + 1) hM hle)).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
      (((embedCircuit embHC410 (ps.hcAdjCirc (n + 1))).map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha4 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
        hHatCirc410 ++
        embedCircuit embHC410 (ps.hcCirc (n + 1))).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((embedCircuit embUTilde410 (ps.uTilde410Circ M (n + 1) hM hle)).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
    have ha5 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup) ++
        hHatCirc410).map OracleStep.gate) : OracleCircuit gates12 a1 M')
      (((embedCircuit embHC410 (ps.hcCirc (n + 1))).map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have ha6 := nonOracleDepth_append
      (((embedCircuit (embEqFC (ps := ps) (r := r) (n := n) (M := M))
          (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map OracleStep.gate) :
        OracleCircuit gates12 a1 M')
      (((hHatCirc410 (ps := ps) (r := r) (n := n) (M := M)).map OracleStep.gate) : OracleCircuit gates12 a1 M')
    have heqfc_d : nonOracleDepth ((embedCircuit (embEqFC (ps := ps) (r := r) (n := n) (M := M))
        (ps.eqCirc r (fun _ => false) pauliX pauliX_mem_unitaryGroup)).map OracleStep.gate :
        OracleCircuit gates12 a1 M') ≤ ps.eqDepth r :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.eq_hdepth _ _ _ _ 1 a1)
    have hhc_d : nonOracleDepth ((embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M))
        (ps.hcCirc (n + 1))).map OracleStep.gate : OracleCircuit gates12 a1 M') ≤ ps.hcDepth (n + 1) :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.hc_hdepth (n + 1) 1 a1).1
    have hhcadj_d : nonOracleDepth ((embedCircuit (embHC410 (ps := ps) (r := r) (n := n) (M := M))
        (ps.hcAdjCirc (n + 1))).map OracleStep.gate : OracleCircuit gates12 a1 M') ≤ ps.hcDepth (n + 1) :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.hc_hdepth (n + 1) 1 a1).2
    have hut_d : nonOracleDepth ((embedCircuit (embUTilde410 (ps := ps) (r := r) (n := n) (M := M))
        (ps.uTilde410Circ M (n + 1) hM hle)).map OracleStep.gate : OracleCircuit gates12 a1 M') ≤ ps.uTilde410Depth M (n + 1) :=
      le_trans (nonOracleDepth_embedCircuit _ _) (ps.uTilde410_hdepth M (n + 1) hM hle 1 a1)
    simp only [List.map_append] at ha1 ha2 ha3 ha4 ha5
    omega
  have hstep_d : nonOracleDepth (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step) ≤
      2 * r + 4 * ps.eqDepth qw + 4 * ps.eqDepth r + 2 * ps.eqDepth (r + qw) +
        4 * ps.eqDepth (1 + qw) + 9 + 2 * ps.toffoliDepth + 2 * ps.cnDepth n +
        2 * ps.chDepth (n + 1) + 2 * ps.hcDepth (n + 1) + ps.uTilde410Depth M (n + 1) := by
    let pat := natToBitsLSB r c_step.1
    let xc := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) (ctrl0XCirc410 pat)
    let fq := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) fqComputeCirc410
    let ubody := liftToFull410 (ps := ps) (r := r) (n := n) (M := M) (uBodyCirc410 hM hle)
    change nonOracleDepth (xc ++ fq ++ liftedOracleCirc410 ++ fq ++ ubody ++ xc) ≤ _
    have hs1 := nonOracleDepth_append (xc ++ fq ++ liftedOracleCirc410 ++ fq ++ ubody) xc
    have hs2 := nonOracleDepth_append (xc ++ fq ++ liftedOracleCirc410 ++ fq) ubody
    have hs3 := nonOracleDepth_append (xc ++ fq ++ liftedOracleCirc410) fq
    have hs4 := nonOracleDepth_append (xc ++ fq) liftedOracleCirc410
    have hs5 := nonOracleDepth_append xc fq
    have hxc' : nonOracleDepth xc ≤ 2 * ps.eqDepth qw + r := hxc_d
    have hfq' : nonOracleDepth fq ≤ ps.eqDepth r + ps.eqDepth (r + qw) := hfq_d
    have hub' : nonOracleDepth ubody ≤ 2 * ps.eqDepth r + 4 + 4 * ps.eqDepth (1 + qw) +
        2 * ps.chDepth (n + 1) + 2 * ps.hcDepth (n + 1) + ps.uTilde410Depth M (n + 1) := hubody_d
    have hli' : nonOracleDepth (liftedOracleCirc410 (ps := ps) (r := r) (n := n) (M := M)) ≤
        5 + 2 * ps.toffoliDepth + 2 * ps.cnDepth n := hlifted_d
    omega
  have hstep_r : (nonOracleDepth (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step) : ℝ) ≤
      2 * (r : ℝ) + 4 * (ps.eqDepth qw : ℝ) + 4 * (ps.eqDepth r : ℝ) + 2 * (ps.eqDepth (r + qw) : ℝ) +
        4 * (ps.eqDepth (1 + qw) : ℝ) + 9 + 2 * (ps.toffoliDepth : ℝ) + 2 * (ps.cnDepth n : ℝ) +
        2 * (ps.chDepth (n + 1) : ℝ) + 2 * (ps.hcDepth (n + 1) : ℝ) + (ps.uTilde410Depth M (n + 1) : ℝ) := by
    exact_mod_cast hstep_d
  have heq_qw := (ps.eq_bound qw (fun _ => false) pauliX pauliX_mem_unitaryGroup).2
  have heq_r := (ps.eq_bound r (fun _ => false) pauliX pauliX_mem_unitaryGroup).2
  have heq_rqw := (ps.eq_bound (r + qw) (fun _ => false) pauliX pauliX_mem_unitaryGroup).2
  have heq_1qw := (ps.eq_bound (1 + qw) (patFCMode0 M) pauliX pauliX_mem_unitaryGroup).2
  have hcn := (ps.cn_bound n hn2).2
  have hch := (ps.ch_bound (n + 1) hn'2).2
  have hhc := (ps.hc_bound (n + 1) hn'2).2
  have hut := (ps.uTilde410_bound M (n + 1) hM hle hn'3).2
  have hc_qw : (Nat.clog 2 (qw + 1) + 1 : ℕ) ≤ qw + 2 := by have := nat_clog2_le410 (qw + 1); omega
  have hc_r : (Nat.clog 2 (r + 1) + 1 : ℕ) ≤ r + qw + 2 := by have := nat_clog2_le410 (r + 1); omega
  have hc_rqw : (Nat.clog 2 ((r + qw) + 1) + 1 : ℕ) ≤ r + qw + 2 := by
    have := nat_clog2_le410 ((r + qw) + 1); omega
  have hc_1qw : (Nat.clog 2 ((1 + qw) + 1) + 1 : ℕ) ≤ qw + 3 := by
    have := nat_clog2_le410 ((1 + qw) + 1); omega
  have hCeq : 0 < ps.C_eq := ps.hC_eq_pos
  have b_qw : (ps.eqDepth qw : ℝ) ≤ ps.C_eq * ((qw : ℝ) + 2) := by
    refine le_trans heq_qw ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc_qw) hCeq.le
  have b_r : (ps.eqDepth r : ℝ) ≤ ps.C_eq * ((r : ℝ) + qw + 2) := by
    refine le_trans heq_r ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc_r) hCeq.le
  have b_rqw : (ps.eqDepth (r + qw) : ℝ) ≤ ps.C_eq * ((r : ℝ) + qw + 2) := by
    refine le_trans heq_rqw ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc_rqw) hCeq.le
  have b_1qw : (ps.eqDepth (1 + qw) : ℝ) ≤ ps.C_eq * ((qw : ℝ) + 3) := by
    refine le_trans heq_1qw ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc_1qw) hCeq.le
  push_cast at b_qw b_r b_rqw b_1qw hch hhc hut
  linarith

private lemma loopPrefix410_nonOracleDepth_le (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n + 1)
    {D : ℝ} (hD : ∀ c_step : Fin (2 ^ r),
      (nonOracleDepth (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step) : ℝ) ≤ D) :
    ∀ (t : ℕ) (ht : t ≤ 2 ^ r),
      (nonOracleDepth (loopPrefix410 ps r n M hM hle t ht) : ℝ) ≤ (t : ℝ) * D := by
  intro t
  induction t with
  | zero => intro _; simp [loopPrefix410, nonOracleDepth]
  | succ t ih =>
    intro ht
    simp only [loopPrefix410]
    have hnat : nonOracleDepth (loopPrefix410 ps r n M hM hle t (Nat.le_of_lt ht) ++
        stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle ⟨t, ht⟩) ≤
        nonOracleDepth (loopPrefix410 ps r n M hM hle t (Nat.le_of_lt ht)) +
        nonOracleDepth (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle ⟨t, ht⟩) :=
      nonOracleDepth_append _ _
    have hcast : (nonOracleDepth (loopPrefix410 ps r n M hM hle t (Nat.le_of_lt ht) ++
        stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle ⟨t, ht⟩) : ℝ) ≤
        (nonOracleDepth (loopPrefix410 ps r n M hM hle t (Nat.le_of_lt ht)) : ℝ) +
        (nonOracleDepth (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle ⟨t, ht⟩) : ℝ) := by
      exact_mod_cast hnat
    have h1 := ih (Nat.le_of_lt ht)
    have h2 := hD ⟨t, ht⟩
    push_cast
    linarith

end WalkCorrectnessAndComplexity410

private lemma qW_le_clog410 {M n : ℕ} (hle : 2 * M + 1 ≤ n + 1) :
    qW M ≤ Nat.clog 2 (n + 2) := by
  have hqw : qW M = Nat.clog 2 (M + 2) := rfl
  by_contra hgt
  have hlt : Nat.clog 2 (n + 2) < Nat.clog 2 (M + 2) := by omega
  have h1 : 1 ≤ Nat.clog 2 (M + 2) := by rw [← hqw]; exact one_le_qW M
  have hpred : Nat.clog 2 (n + 2) ≤ Nat.clog 2 (M + 2) - 1 := by omega
  have hpow1 : 2 ^ (Nat.clog 2 (M + 2) - 1) < M + 2 :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by omega)
  have hpow2 : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := Nat.le_pow_clog (by norm_num) (n + 2)
  have hpow3 : 2 ^ Nat.clog 2 (n + 2) ≤ 2 ^ (Nat.clog 2 (M + 2) - 1) :=
    Nat.pow_le_pow_right (by norm_num) hpred
  omega

theorem theorem_4_10_from_primitives (ps : PrimitiveSuite410) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ k n : ℕ, 2 ≤ k → k ≤ n →
        ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m) (out : Fin n ↪ Fin m),
          (c.queryCount 0 : ℝ) ≤ C * Real.log k ∧
          (c.gateCount : ℝ) ≤ C * n * Real.log n * Real.log k ∧
          (nonOracleDepth c : ℝ) ≤ C * Real.log n * Real.log k ∧
          ∀ A : Finset (Fin n), 1 ≤ A.card ∧ A.card ≤ k →
            open Classical in
            probEvent (act (c.unitary fun _ => majOracle A) (zeroKet m))
              (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 1 - ε := by
  intro ε hε0 _
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ := wCatVec410_energy_bound
  let L2 : ℝ := 1 / Real.log 2
  let C_K : ℝ := 8 * C₀ / ε + 4 * L2
  let C_ℓ : ℝ := 3 * L2
  let C_step_g : ℝ :=
    2 * C_K + 4 * ps.C_eq * (C_ℓ + L2) + 6 * ps.C_eq * (C_K + C_ℓ + L2) +
      9 * L2 + 2 * (ps.toffoliCirc.length : ℝ) * L2 + 2 * ps.C_cn * L2 +
      4 * ps.C_eq * (C_ℓ + 2 * L2) + 4 * ps.C_ch * L2 + 8 * ps.C_hc + 4 * ps.C_ut
  let C_step_d : ℝ :=
    2 * C_K + 4 * ps.C_eq * (C_ℓ + 2 * L2) + 6 * ps.C_eq * (C_K + C_ℓ + 2 * L2) +
      4 * ps.C_eq * (C_ℓ + 3 * L2) + 9 * L2 + 2 * (ps.toffoliDepth : ℝ) * L2 +
      2 * ps.C_cn + 4 * ps.C_ch + 4 * ps.C_hc + 2 * ps.C_ut
  let C : ℝ := max C_K (max (C_K * (C_step_g + L2 + C_K)) (C_K * (C_step_d + 2 * L2)))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2_pos : 0 < L2 := by dsimp [L2]; positivity
  have hCK_pos : 0 < C_K := by positivity
  have hC_pos : 0 < C := lt_of_lt_of_le hCK_pos (le_max_left _ _)
  refine ⟨C, hC_pos, ?_⟩
  intro k n hk2 hkn
  have hn2 : 2 ≤ n := le_trans hk2 hkn
  let M : ℕ := k / 2
  have hM : 1 ≤ M := by dsimp [M]; omega
  let n' : ℕ := n + 1
  have hle : 2 * M + 1 ≤ n' := by dsimp [M, n']; omega
  have hlogk_ge : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hk2)
  have hlogk_le_n : Real.log k ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hkn)
  have hlogn_ge : Real.log 2 ≤ Real.log n := le_trans hlogk_ge hlogk_le_n
  have hL2_logk : (1 : ℝ) ≤ L2 * Real.log k := by
    have h1 : 1 ≤ Real.log k / Real.log 2 := (one_le_div hlog2_pos).mpr hlogk_ge
    dsimp [L2]; linarith [show 1 / Real.log 2 * Real.log k = Real.log k / Real.log 2 from by ring]
  have hL2_logn : (1 : ℝ) ≤ L2 * Real.log n := by
    have h1 : 1 ≤ Real.log n / Real.log 2 := (one_le_div hlog2_pos).mpr hlogn_ge
    dsimp [L2]; linarith [show 1 / Real.log 2 * Real.log n = Real.log n / Real.log 2 from by ring]
  have hlogk_nn : 0 ≤ Real.log k := le_trans hlog2_pos.le hlogk_ge
  have hlogn_nn : 0 ≤ Real.log n := le_trans hlog2_pos.le hlogn_ge
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn'_le : (n' : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (by dsimp [n']; omega : n' ≤ 2 * n)
  have hn'_sq : (n' : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (by dsimp [n']; nlinarith : n' ≤ n ^ 2)
  have hlogn'_le : Real.log (n' : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hn'pos : (0 : ℝ) < (n' : ℝ) := by positivity
    have h1 := Real.log_le_log hn'pos hn'_sq
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  have hlogn'_nn : 0 ≤ Real.log (n' : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by dsimp [n']; omega : 1 ≤ n'))
  let M_req : ℕ := Nat.ceil (4 * C₀ * Real.log k / ε) + 1
  let r : ℕ := max 1 (Nat.clog 2 M_req)
  have hr1 : 1 ≤ r := le_max_left _ _
  have hM_req_pos : 1 ≤ M_req := by omega
  have hpow_ge_M : M_req ≤ 2 ^ r := by
    have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) M_req
    exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have hpow_ge_real : 4 * C₀ * Real.log k / ε ≤ (2 ^ r : ℕ) := by
    have hceil : 4 * C₀ * Real.log k / ε ≤ (M_req : ℝ) := by
      have h1 : 4 * C₀ * Real.log k / ε ≤ (Nat.ceil (4 * C₀ * Real.log k / ε) : ℝ) := Nat.le_ceil _
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
      have hpow_lt : 2 ^ (r - 1) < M_req := (Nat.lt_clog_iff_pow_lt (by norm_num)).mp hpred_lt
      calc 2 ^ r = 2 ^ ((r - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (r - 1) := by rw [pow_succ']
        _ ≤ 2 * M_req := by omega
  have hM_req_real : (M_req : ℝ) ≤ (4 * C₀ / ε + 2 * L2) * Real.log k := by
    have hnonneg : 0 ≤ 4 * C₀ * Real.log k / ε := by positivity
    have hceil_lt := Nat.ceil_lt_add_one hnonneg
    have hM_lt : (M_req : ℝ) ≤ 4 * C₀ * Real.log k / ε + 2 := by
      have : (M_req : ℝ) = (Nat.ceil (4 * C₀ * Real.log k / ε) : ℝ) + 1 := by
        dsimp [M_req]; push_cast; rfl
      linarith
    have h2 : (2 : ℝ) ≤ 2 * L2 * Real.log k := by linarith [hL2_logk]
    calc (M_req : ℝ) ≤ 4 * C₀ * Real.log k / ε + 2 := hM_lt
      _ ≤ (4 * C₀ / ε) * Real.log k + 2 * L2 * Real.log k := by
          have : 4 * C₀ * Real.log k / ε = (4 * C₀ / ε) * Real.log k := by ring
          linarith
      _ = (4 * C₀ / ε + 2 * L2) * Real.log k := by ring
  have hK_le : ((2 ^ r : ℕ) : ℝ) ≤ C_K * Real.log k := by
    have h2r : ((2 ^ r : ℕ) : ℝ) ≤ 2 * (M_req : ℝ) := by exact_mod_cast hpow_le_2M
    calc ((2 ^ r : ℕ) : ℝ) ≤ 2 * (M_req : ℝ) := h2r
      _ ≤ 2 * ((4 * C₀ / ε + 2 * L2) * Real.log k) := by linarith
      _ = C_K * Real.log k := by dsimp [C_K]; ring
  have hr_le : (r : ℝ) ≤ C_K * Real.log n := by
    have hr_lt : r < 2 ^ r := Nat.lt_two_pow_self
    have hr_real : (r : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast hr_lt.le
    calc (r : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := hr_real
      _ ≤ C_K * Real.log k := hK_le
      _ ≤ C_K * Real.log n := mul_le_mul_of_nonneg_left hlogk_le_n hCK_pos.le
  let ℓval : ℕ := Nat.clog 2 (n + 2)
  have hℓ_le : (ℓval : ℝ) ≤ C_ℓ * Real.log n := by
    have h4 : 4 ≤ n + 2 := by omega
    have hℓ_ge2 : 2 ≤ ℓval := by
      by_contra hlt
      have hpow : n + 2 ≤ 2 ^ ℓval := Nat.le_pow_clog (b := 2) (by norm_num) (n + 2)
      have h2 : 2 ^ ℓval ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega : ℓval ≤ 1)
      norm_num at h2; omega
    have hpred_lt : ℓval - 1 < Nat.clog 2 (n + 2) := by omega
    have hpow_lt : 2 ^ (ℓval - 1) < n + 2 :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).mp hpred_lt
    have hpow_le_nsq : ((2 ^ (ℓval - 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (by nlinarith : 2 ^ (ℓval - 1) ≤ n ^ 2)
    have hpos2 : (0 : ℝ) < ((2 ^ (ℓval - 1) : ℕ) : ℝ) := by positivity
    have hlog_pow : ((ℓval - 1 : ℕ) : ℝ) * Real.log 2 ≤ 2 * Real.log n := by
      calc ((ℓval - 1 : ℕ) : ℝ) * Real.log 2
          = Real.log ((2 : ℝ) ^ (ℓval - 1)) := (Real.log_pow 2 (ℓval - 1)).symm
        _ = Real.log (((2 ^ (ℓval - 1) : ℕ) : ℝ)) := by norm_cast
        _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log hpos2 hpow_le_nsq
        _ = 2 * Real.log n := by rw [Real.log_pow, Nat.cast_ofNat]
    have hdiv : ((ℓval - 1 : ℕ) : ℝ) ≤ 2 * L2 * Real.log n := by
      have h1 := (le_div_iff₀ hlog2_pos).mpr hlog_pow
      dsimp [L2]; linarith [show 2 * Real.log n / Real.log 2 = 2 * (1 / Real.log 2) * Real.log n from by ring]
    have hcast : (ℓval : ℝ) = ((ℓval - 1 : ℕ) : ℝ) + 1 := by
      have hℓ_eq : ℓval = ℓval - 1 + 1 := by omega
      rw [hℓ_eq]; push_cast; rfl
    rw [hcast]
    calc ((ℓval - 1 : ℕ) : ℝ) + 1 ≤ 2 * L2 * Real.log n + L2 * Real.log n := by linarith [hL2_logn]
      _ = C_ℓ * Real.log n := by dsimp [C_ℓ]; ring
  have hqw_le_real : ((qW M : ℕ) : ℝ) ≤ C_ℓ * Real.log n := by
    have hqw_le : qW M ≤ ℓval := qW_le_clog410 hle
    exact le_trans (by exact_mod_cast hqw_le) hℓ_le
  let M_tot : ℕ := regM'410 ps r n M + 1
  let c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) M_tot := fullCirc410 ps r n M hM hle
  let out : Fin n ↪ Fin M_tot :=
    (Fin.castSuccEmb.trans (regQ (ps := ps) (r := r) (n := n) (M := M))).trans (Fin.castAddEmb 1)
  refine ⟨M_tot, c, out, ?_, ?_, ?_, ?_⟩
  · -- queryCount
    rw [show (c.queryCount 0 : ℝ) = ((2 ^ r : ℕ) : ℝ) by
      exact_mod_cast fullCirc410_queryCount (ps := ps) (r := r) (n := n) (M := M) hM hle]
    calc ((2 ^ r : ℕ) : ℝ) ≤ C_K * Real.log k := hK_le
      _ ≤ C * Real.log k := mul_le_mul_of_nonneg_right (le_max_left _ _) hlogk_nn
  · -- gateCount
    have hstep_g : ∀ c_step : Fin (2 ^ r),
        ((stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step).gateCount : ℝ) ≤
          C_step_g * n * Real.log n := by
      intro c_step
      have hs := stepCirc410_gateCount_le (ps := ps) (r := r) (n := n) (M := M) hM hle hn2 c_step
      have hCeq_nn : 0 ≤ ps.C_eq := ps.hC_eq_pos.le
      have hCcn_nn : 0 ≤ ps.C_cn := ps.hC_cn_pos.le
      have hCch_nn : 0 ≤ ps.C_ch := ps.hC_ch_pos.le
      have hChc_nn : 0 ≤ ps.C_hc := ps.hC_hc_pos.le
      have hCut_nn : 0 ≤ ps.C_ut := ps.hC_ut_pos.le
      have hrl_to_nrl : ∀ a : ℝ, 0 ≤ a → a * Real.log n ≤ a * (n : ℝ) * Real.log n := fun a ha => by
        have : 0 ≤ a * Real.log n := mul_nonneg ha hlogn_nn
        calc a * Real.log n = (a * Real.log n) * 1 := (mul_one _).symm
          _ ≤ (a * Real.log n) * (n : ℝ) := mul_le_mul_of_nonneg_left hn_ge1 this
          _ = a * (n : ℝ) * Real.log n := by ring
      have h1 : 2 * (r : ℝ) ≤ 2 * C_K * (n : ℝ) * Real.log n :=
        le_trans (by linarith) (hrl_to_nrl (2 * C_K) (by positivity))
      have h2 : 4 * ps.C_eq * ((qW M : ℝ) + 1) ≤ 4 * ps.C_eq * (C_ℓ + L2) * (n : ℝ) * Real.log n := by
        have h2a : (qW M : ℝ) + 1 ≤ (C_ℓ + L2) * Real.log n := by linarith
        exact le_trans (mul_le_mul_of_nonneg_left h2a (by positivity))
          (by simpa [mul_assoc] using hrl_to_nrl (4 * ps.C_eq * (C_ℓ + L2)) (by positivity))
      have h3 : 6 * ps.C_eq * ((r : ℝ) + (qW M : ℝ) + 1) ≤
          6 * ps.C_eq * (C_K + C_ℓ + L2) * (n : ℝ) * Real.log n := by
        have h3a : (r : ℝ) + (qW M : ℝ) + 1 ≤ (C_K + C_ℓ + L2) * Real.log n := by linarith
        exact le_trans (mul_le_mul_of_nonneg_left h3a (by positivity))
          (by simpa [mul_assoc] using hrl_to_nrl (6 * ps.C_eq * (C_K + C_ℓ + L2)) (by positivity))
      have h4 : (9 : ℝ) ≤ 9 * L2 * (n : ℝ) * Real.log n :=
        le_trans (by linarith [hL2_logn]) (hrl_to_nrl (9 * L2) (by positivity))
      have h5 : 2 * (ps.toffoliCirc.length : ℝ) ≤
          2 * (ps.toffoliCirc.length : ℝ) * L2 * (n : ℝ) * Real.log n := by
        have h5a : 2 * (ps.toffoliCirc.length : ℝ) ≤ 2 * (ps.toffoliCirc.length : ℝ) * L2 * Real.log n := by
          calc 2 * (ps.toffoliCirc.length : ℝ) = (2 * (ps.toffoliCirc.length : ℝ)) * 1 := (mul_one _).symm
            _ ≤ (2 * (ps.toffoliCirc.length : ℝ)) * (L2 * Real.log n) :=
                mul_le_mul_of_nonneg_left hL2_logn (by positivity)
            _ = 2 * (ps.toffoliCirc.length : ℝ) * L2 * Real.log n := by ring
        exact le_trans h5a (hrl_to_nrl (2 * (ps.toffoliCirc.length : ℝ) * L2) (by positivity))
      have h6 : 2 * ps.C_cn * (n : ℝ) ≤ 2 * ps.C_cn * L2 * (n : ℝ) * Real.log n := by
        calc 2 * ps.C_cn * (n : ℝ) = (2 * ps.C_cn * (n : ℝ)) * 1 := (mul_one _).symm
          _ ≤ (2 * ps.C_cn * (n : ℝ)) * (L2 * Real.log n) :=
              mul_le_mul_of_nonneg_left hL2_logn (by positivity)
          _ = 2 * ps.C_cn * L2 * (n : ℝ) * Real.log n := by ring
      have h7 : 4 * ps.C_eq * ((qW M : ℝ) + 2) ≤ 4 * ps.C_eq * (C_ℓ + 2 * L2) * (n : ℝ) * Real.log n := by
        have h7a : (qW M : ℝ) + 2 ≤ (C_ℓ + 2 * L2) * Real.log n := by linarith
        exact le_trans (mul_le_mul_of_nonneg_left h7a (by positivity))
          (by simpa [mul_assoc] using hrl_to_nrl (4 * ps.C_eq * (C_ℓ + 2 * L2)) (by positivity))
      have h8 : 2 * ps.C_ch * (n' : ℝ) ≤ 4 * ps.C_ch * L2 * (n : ℝ) * Real.log n := by
        calc 2 * ps.C_ch * (n' : ℝ) ≤ 2 * ps.C_ch * (2 * (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hn'_le (by positivity)
          _ = (4 * ps.C_ch * (n : ℝ)) * 1 := by ring
          _ ≤ (4 * ps.C_ch * (n : ℝ)) * (L2 * Real.log n) :=
              mul_le_mul_of_nonneg_left hL2_logn (by positivity)
          _ = 4 * ps.C_ch * L2 * (n : ℝ) * Real.log n := by ring
      have h9 : 2 * ps.C_hc * (n' : ℝ) * Real.log (n' : ℝ) ≤ 8 * ps.C_hc * (n : ℝ) * Real.log n := by
        have hprod : (n' : ℝ) * Real.log (n' : ℝ) ≤ 4 * (n : ℝ) * Real.log n := by
          calc (n' : ℝ) * Real.log (n' : ℝ) ≤ (2 * (n : ℝ)) * (2 * Real.log n) :=
                mul_le_mul hn'_le hlogn'_le hlogn'_nn (by positivity)
            _ = 4 * (n : ℝ) * Real.log n := by ring
        calc 2 * ps.C_hc * (n' : ℝ) * Real.log (n' : ℝ)
            = 2 * ps.C_hc * ((n' : ℝ) * Real.log (n' : ℝ)) := by ring
          _ ≤ 2 * ps.C_hc * (4 * (n : ℝ) * Real.log n) :=
              mul_le_mul_of_nonneg_left hprod (by positivity)
          _ = 8 * ps.C_hc * (n : ℝ) * Real.log n := by ring
      have h10 : ps.C_ut * (n' : ℝ) * Real.log (n' : ℝ) ≤ 4 * ps.C_ut * (n : ℝ) * Real.log n := by
        have hprod : (n' : ℝ) * Real.log (n' : ℝ) ≤ 4 * (n : ℝ) * Real.log n := by
          calc (n' : ℝ) * Real.log (n' : ℝ) ≤ (2 * (n : ℝ)) * (2 * Real.log n) :=
                mul_le_mul hn'_le hlogn'_le hlogn'_nn (by positivity)
            _ = 4 * (n : ℝ) * Real.log n := by ring
        calc ps.C_ut * (n' : ℝ) * Real.log (n' : ℝ)
            = ps.C_ut * ((n' : ℝ) * Real.log (n' : ℝ)) := by ring
          _ ≤ ps.C_ut * (4 * (n : ℝ) * Real.log n) :=
              mul_le_mul_of_nonneg_left hprod (by positivity)
          _ = 4 * ps.C_ut * (n : ℝ) * Real.log n := by ring
      calc ((stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step).gateCount : ℝ)
          ≤ 2 * (r : ℝ) + 4 * ps.C_eq * ((qW M : ℝ) + 1) +
              6 * ps.C_eq * ((r : ℝ) + (qW M : ℝ) + 1) + 9 +
              2 * (ps.toffoliCirc.length : ℝ) + 2 * ps.C_cn * (n : ℝ) +
              4 * ps.C_eq * ((qW M : ℝ) + 2) + 2 * ps.C_ch * (n' : ℝ) +
              2 * ps.C_hc * (n' : ℝ) * Real.log (n' : ℝ) +
              ps.C_ut * (n' : ℝ) * Real.log (n' : ℝ) := by dsimp only [n']; push_cast; exact hs
        _ ≤ C_step_g * (n : ℝ) * Real.log n := by dsimp [C_step_g]; linarith
    have hloop_g := loopPrefix410_gateCount_le (ps := ps) (r := r) (n := n) (M := M)
      hM hle hstep_g (2 ^ r) le_rfl
    have hprep_g : OracleCircuit.gateCount ([prepareMinusStep410 (n := n) (regM'410 ps r n M)] :
        OracleCircuit gates12 (fun _ : Fin 1 => n + 1) M_tot) = 1 := by
      simp [OracleCircuit.gateCount, prepareMinusStep410]
    have hfull_g : (c.gateCount : ℝ) =
        1 + (r : ℝ) + ((loopPrefix410 ps r n M hM hle (2 ^ r) le_rfl).gateCount : ℝ) := by
      have hnat : c.gateCount =
          1 + r + (loopPrefix410 ps r n M hM hle (2 ^ r) le_rfl).gateCount := by
        change (fullCirc410 ps r n M hM hle).gateCount = _
        simp only [fullCirc410, oracleCircuit_gateCount_append,
          hprep_g, liftToFull410_gateCount, hadamardLayerC410_length]
      exact_mod_cast hnat
    have h1r : 1 + (r : ℝ) ≤ (L2 + C_K) * (n : ℝ) * Real.log n := by
      have h1r_log : 1 + (r : ℝ) ≤ (L2 + C_K) * Real.log n := by linarith
      have hnonneg : 0 ≤ (L2 + C_K) * Real.log n := by positivity
      calc 1 + (r : ℝ) ≤ (L2 + C_K) * Real.log n := h1r_log
        _ ≤ ((L2 + C_K) * Real.log n) * (n : ℝ) := le_mul_of_one_le_right hnonneg hn_ge1
        _ = (L2 + C_K) * (n : ℝ) * Real.log n := by ring
    have hK_ge1 : (1 : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    have h1r_K : 1 + (r : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) * ((L2 + C_K) * (n : ℝ) * Real.log n) := by
      have hnonneg : 0 ≤ (L2 + C_K) * (n : ℝ) * Real.log n := by positivity
      exact le_trans h1r (le_mul_of_one_le_left hnonneg hK_ge1)
    have htot_g : (c.gateCount : ℝ) ≤
        ((2 ^ r : ℕ) : ℝ) * ((C_step_g + L2 + C_K) * (n : ℝ) * Real.log n) := by
      calc (c.gateCount : ℝ)
          = (1 + (r : ℝ)) + ((loopPrefix410 ps r n M hM hle (2 ^ r) le_rfl).gateCount : ℝ) := hfull_g
        _ ≤ ((2 ^ r : ℕ) : ℝ) * ((L2 + C_K) * (n : ℝ) * Real.log n) +
              ((2 ^ r : ℕ) : ℝ) * (C_step_g * (n : ℝ) * Real.log n) := add_le_add h1r_K hloop_g
        _ = ((2 ^ r : ℕ) : ℝ) * ((C_step_g + L2 + C_K) * (n : ℝ) * Real.log n) := by ring
    have hC_ge : C_K * (C_step_g + L2 + C_K) ≤ C :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hnonneg_mid : 0 ≤ (C_step_g + L2 + C_K) * (n : ℝ) * Real.log n := by
      have hCeq := ps.hC_eq_pos
      have hCcn := ps.hC_cn_pos
      have hCch := ps.hC_ch_pos
      have hChc := ps.hC_hc_pos
      have hCut := ps.hC_ut_pos
      dsimp only [C_step_g, C_ℓ, C_K, L2]; positivity
    calc (c.gateCount : ℝ)
        ≤ ((2 ^ r : ℕ) : ℝ) * ((C_step_g + L2 + C_K) * (n : ℝ) * Real.log n) := htot_g
      _ ≤ (C_K * Real.log k) * ((C_step_g + L2 + C_K) * (n : ℝ) * Real.log n) :=
          mul_le_mul_of_nonneg_right hK_le hnonneg_mid
      _ = (C_K * (C_step_g + L2 + C_K)) * (n : ℝ) * Real.log n * Real.log k := by ring
      _ ≤ C * (n : ℝ) * Real.log n * Real.log k := by
          have hnn : 0 ≤ (n : ℝ) * Real.log n * Real.log k := by positivity
          calc (C_K * (C_step_g + L2 + C_K)) * (n : ℝ) * Real.log n * Real.log k
              = (C_K * (C_step_g + L2 + C_K)) * ((n : ℝ) * Real.log n * Real.log k) := by ring
            _ ≤ C * ((n : ℝ) * Real.log n * Real.log k) := mul_le_mul_of_nonneg_right hC_ge hnn
            _ = C * (n : ℝ) * Real.log n * Real.log k := by ring
  · -- nonOracleDepth
    have hstep_d : ∀ c_step : Fin (2 ^ r),
        (nonOracleDepth (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step) : ℝ) ≤
          C_step_d * Real.log n := by
      intro c_step
      have hs := stepCirc410_nonOracleDepth_le (ps := ps) (r := r) (n := n) (M := M) hM hle hn2 c_step
      have hCeq_nn : 0 ≤ ps.C_eq := ps.hC_eq_pos.le
      have hCch_nn : 0 ≤ ps.C_ch := ps.hC_ch_pos.le
      have hChc_nn : 0 ≤ ps.C_hc := ps.hC_hc_pos.le
      have hCut_nn : 0 ≤ ps.C_ut := ps.hC_ut_pos.le
      have h1 : 2 * (r : ℝ) ≤ 2 * C_K * Real.log n := by linarith
      have h2 : 4 * ps.C_eq * ((qW M : ℝ) + 2) ≤ 4 * ps.C_eq * (C_ℓ + 2 * L2) * Real.log n := by
        have h2a : (qW M : ℝ) + 2 ≤ (C_ℓ + 2 * L2) * Real.log n := by linarith
        exact le_trans (mul_le_mul_of_nonneg_left h2a (by positivity)) (by ring_nf; rfl)
      have h3 : 6 * ps.C_eq * ((r : ℝ) + (qW M : ℝ) + 2) ≤
          6 * ps.C_eq * (C_K + C_ℓ + 2 * L2) * Real.log n := by
        have h3a : (r : ℝ) + (qW M : ℝ) + 2 ≤ (C_K + C_ℓ + 2 * L2) * Real.log n := by linarith
        exact le_trans (mul_le_mul_of_nonneg_left h3a (by positivity)) (by ring_nf; rfl)
      have h4 : 4 * ps.C_eq * ((qW M : ℝ) + 3) ≤ 4 * ps.C_eq * (C_ℓ + 3 * L2) * Real.log n := by
        have h4a : (qW M : ℝ) + 3 ≤ (C_ℓ + 3 * L2) * Real.log n := by linarith
        exact le_trans (mul_le_mul_of_nonneg_left h4a (by positivity)) (by ring_nf; rfl)
      have h5 : (9 : ℝ) ≤ 9 * L2 * Real.log n := by linarith [hL2_logn]
      have h6 : 2 * (ps.toffoliDepth : ℝ) ≤ 2 * (ps.toffoliDepth : ℝ) * L2 * Real.log n := by
        calc 2 * (ps.toffoliDepth : ℝ) = (2 * (ps.toffoliDepth : ℝ)) * 1 := (mul_one _).symm
          _ ≤ (2 * (ps.toffoliDepth : ℝ)) * (L2 * Real.log n) :=
              mul_le_mul_of_nonneg_left hL2_logn (by positivity)
          _ = 2 * (ps.toffoliDepth : ℝ) * L2 * Real.log n := by ring
      have h7 : 2 * ps.C_ch * Real.log (n' : ℝ) ≤ 4 * ps.C_ch * Real.log n := by
        have h := mul_le_mul_of_nonneg_left hlogn'_le (by positivity : 0 ≤ 2 * ps.C_ch)
        linarith
      have h8 : 2 * ps.C_hc * Real.log (n' : ℝ) ≤ 4 * ps.C_hc * Real.log n := by
        have h := mul_le_mul_of_nonneg_left hlogn'_le (by positivity : 0 ≤ 2 * ps.C_hc)
        linarith
      have h9 : ps.C_ut * Real.log (n' : ℝ) ≤ 2 * ps.C_ut * Real.log n := by
        have h := mul_le_mul_of_nonneg_left hlogn'_le hCut_nn
        linarith
      calc (nonOracleDepth (stepCirc410 (ps := ps) (r := r) (n := n) (M := M) hM hle c_step) : ℝ)
          ≤ 2 * (r : ℝ) + 4 * ps.C_eq * ((qW M : ℝ) + 2) +
              6 * ps.C_eq * ((r : ℝ) + (qW M : ℝ) + 2) +
              4 * ps.C_eq * ((qW M : ℝ) + 3) + 9 + 2 * (ps.toffoliDepth : ℝ) +
              2 * ps.C_cn * Real.log n + 2 * ps.C_ch * Real.log (n' : ℝ) +
              2 * ps.C_hc * Real.log (n' : ℝ) + ps.C_ut * Real.log (n' : ℝ) := by dsimp only [n']; push_cast; exact hs
        _ ≤ C_step_d * Real.log n := by dsimp [C_step_d]; linarith
    have hloop_d := loopPrefix410_nonOracleDepth_le (ps := ps) (r := r) (n := n) (M := M)
      hM hle hstep_d (2 ^ r) le_rfl
    have hprep_d : nonOracleDepth ([prepareMinusStep410 (n := n) (regM'410 ps r n M)] :
        OracleCircuit gates12 (fun _ : Fin 1 => n + 1) M_tot) ≤ 1 := by
      simpa using nonOracleDepth_le_length
        ([prepareMinusStep410 (n := n) (regM'410 ps r n M)] :
          OracleCircuit gates12 (fun _ : Fin 1 => n + 1) M_tot)
    have hhad_d : nonOracleDepth (liftToFull410 (ps := ps) (r := r) (n := n) (M := M) hadamardLayerC410) ≤ 1 :=
      le_trans (liftToFull410_depth_le _) (hadamardLayerC410_depth_le_one (ps := ps) (r := r) (n := n) (M := M))
    have hfull_d : nonOracleDepth c ≤ 2 + nonOracleDepth (loopPrefix410 ps r n M hM hle (2 ^ r) le_rfl) := by
      change nonOracleDepth (([prepareMinusStep410 (n := n) (regM'410 ps r n M)] ++
          liftToFull410 (ps := ps) (r := r) (n := n) (M := M) hadamardLayerC410) ++
          loopPrefix410 ps r n M hM hle (2 ^ r) le_rfl) ≤ _
      have ha1 := nonOracleDepth_append
        ([prepareMinusStep410 (n := n) (regM'410 ps r n M)] ++
          liftToFull410 (ps := ps) (r := r) (n := n) (M := M) hadamardLayerC410)
        (loopPrefix410 ps r n M hM hle (2 ^ r) le_rfl)
      have ha2 := nonOracleDepth_cons
        (prepareMinusStep410 (n := n) (regM'410 ps r n M))
        (liftToFull410 (ps := ps) (r := r) (n := n) (M := M) hadamardLayerC410)
      exact le_trans ha1 (Nat.add_le_add_right (le_trans ha2 (Nat.add_le_add hprep_d hhad_d)) _)
    have hfull_dr : (nonOracleDepth c : ℝ) ≤
        2 + (nonOracleDepth (loopPrefix410 ps r n M hM hle (2 ^ r) le_rfl) : ℝ) := by
      exact_mod_cast hfull_d
    have hK_ge1 : (1 : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    have h2_K : (2 : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) * (2 * L2 * Real.log n) := by
      have : (2 : ℝ) ≤ 2 * L2 * Real.log n := by linarith [hL2_logn]
      exact le_trans this (le_mul_of_one_le_left (by positivity) hK_ge1)
    have htot_d : (nonOracleDepth c : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) * ((C_step_d + 2 * L2) * Real.log n) := by
      calc (nonOracleDepth c : ℝ)
          ≤ 2 + (nonOracleDepth (loopPrefix410 ps r n M hM hle (2 ^ r) le_rfl) : ℝ) := hfull_dr
        _ ≤ ((2 ^ r : ℕ) : ℝ) * (2 * L2 * Real.log n) +
              ((2 ^ r : ℕ) : ℝ) * (C_step_d * Real.log n) := add_le_add h2_K hloop_d
        _ = ((2 ^ r : ℕ) : ℝ) * ((C_step_d + 2 * L2) * Real.log n) := by ring
    have hC_ge : C_K * (C_step_d + 2 * L2) ≤ C :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hnonneg_mid : 0 ≤ (C_step_d + 2 * L2) * Real.log n := by
      have hCeq := ps.hC_eq_pos
      have hCcn := ps.hC_cn_pos
      have hCch := ps.hC_ch_pos
      have hChc := ps.hC_hc_pos
      have hCut := ps.hC_ut_pos
      dsimp only [C_step_d, C_ℓ, C_K, L2]; positivity
    calc (nonOracleDepth c : ℝ)
        ≤ ((2 ^ r : ℕ) : ℝ) * ((C_step_d + 2 * L2) * Real.log n) := htot_d
      _ ≤ (C_K * Real.log k) * ((C_step_d + 2 * L2) * Real.log n) :=
          mul_le_mul_of_nonneg_right hK_le hnonneg_mid
      _ = (C_K * (C_step_d + 2 * L2)) * (Real.log n * Real.log k) := by ring
      _ ≤ C * (Real.log n * Real.log k) := by
          have hnn : 0 ≤ Real.log n * Real.log k := by positivity
          exact mul_le_mul_of_nonneg_right hC_ge hnn
      _ = C * Real.log n * Real.log k := by ring
  · -- Correctness for every A with 1 ≤ A.card ≤ k
    rintro A ⟨hA1, hA2⟩
    let A_bd : BoundedSupports n k := ⟨A, Finset.card_pos.mp hA1, hA2⟩
    have hmM : layerOf A_bd ≤ M := (liftOdd_card_eq A_bd).2
    have hK_err :
        4 * ‖wCatVec410 n' M (layerOf A_bd) (liftOdd A_bd) (liftOdd_card_eq A_bd).1‖ ^ 2 / (2 ^ r : ℕ) ≤ ε := by
      have hw := hC₀_bound k n hk2 hkn A_bd
      have h2r_pos : (0 : ℝ) < (2 ^ r : ℕ) := by positivity
      rw [div_le_iff₀ h2r_pos]
      calc 4 * ‖wCatVec410 n' M (layerOf A_bd) (liftOdd A_bd) (liftOdd_card_eq A_bd).1‖ ^ 2
          ≤ 4 * (C₀ * Real.log k) := by linarith
        _ = ε * (4 * C₀ * Real.log k / ε) := by field_simp
        _ ≤ ε * (2 ^ r : ℕ) := mul_le_mul_of_nonneg_left hpow_ge_real hε0.le
    exact fullCirc410_correct (ps := ps) (r := r) (n := n) (M := M) hM hle A_bd hmM hK_err


end Thm410Walk

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement in
theorem solution :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ k n : ℕ, 2 ≤ k → k ≤ n →
        ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m) (out : Fin n ↪ Fin m),
          (c.queryCount 0 : ℝ) ≤ C * Real.log k ∧
          (c.gateCount : ℝ) ≤ C * n * Real.log n * Real.log k ∧
          (nonOracleDepth c : ℝ) ≤ C * Real.log n * Real.log k ∧
          ∀ A : Finset (Fin n), 1 ≤ A.card ∧ A.card ≤ k →
            open Classical in
            probEvent (act (c.unitary fun _ => majOracle A) (zeroKet m))
              (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 1 - ε :=
  Thm410Walk.theorem_4_10_from_primitives (Classical.choice primitive_suite_410)
