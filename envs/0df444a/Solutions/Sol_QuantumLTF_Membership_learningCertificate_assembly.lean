-- Prove2me | solution 1 for QuantumLTF.Membership.learningCertificate_assembly
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T23:26:42.332851+00:00
-- url     : https://prove2.me/submissions/4638bbca-22e4-4d88-b459-8181f0fcbfaa

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_LearningCertificate
import Definitions.Def_QuantumLTF_Membership_Leps
import Definitions.Def_QuantumLTF_Membership_Teps
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_addrOf
import Definitions.Def_QuantumLTF_Membership_boundarySearchTreeStrict
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_regBasis
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_sgn
import Theorems.Thm_QuantumLTF_Membership_boundarySearchTreeStrict_run
import Theorems.Thm_QuantumLTF_Membership_orientedBisectValue_error

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.constructorNameAsVariable false
set_option linter.deprecated false

-- ===== module Embed =====

open QAlgorithms

namespace LTFC

section Embed

variable {k n : ℕ}

/-- `y` and `z` agree off the range of `w`. -/
def AgreeOff (w : Fin k ↪ Fin n) (y z : Qubits n) : Prop :=
  ∀ a : Fin n, a ∉ Set.range w → y a = z a

/-- Replace the part of `z` on the wires `w` by `u`. -/
noncomputable def setPart (z : Qubits n) (w : Fin k ↪ Fin n) (u : Qubits k) : Qubits n := by
  classical
  exact fun v => if h : v ∈ Set.range w then u (w.invOfMemRange ⟨v, h⟩) else z v

theorem setPart_emb (z : Qubits n) (w : Fin k ↪ Fin n) (u : Qubits k) (a : Fin k) :
    setPart z w u (w a) = u a := by
  unfold setPart
  rw [dif_pos ⟨a, rfl⟩]
  congr 1
  apply w.injective
  rw [Function.Embedding.left_inv_of_invOfMemRange]

theorem setPart_off (z : Qubits n) (w : Fin k ↪ Fin n) (u : Qubits k) {v : Fin n}
    (h : v ∉ Set.range w) : setPart z w u v = z v := by
  unfold setPart
  rw [dif_neg h]

theorem setPart_comp (z : Qubits n) (w : Fin k ↪ Fin n) (u : Qubits k) :
    setPart z w u ∘ w = u := funext (setPart_emb z w u)

theorem agreeOff_setPart (z : Qubits n) (w : Fin k ↪ Fin n) (u : Qubits k) :
    AgreeOff w (setPart z w u) z := fun _ h => setPart_off z w u h

theorem eq_of_comp_agree {w : Fin k ↪ Fin n} {y z : Qubits n} (h1 : y ∘ w = z ∘ w)
    (h2 : AgreeOff w y z) : y = z := by
  funext v
  by_cases hv : v ∈ Set.range w
  · obtain ⟨a, rfl⟩ := hv
    exact congrFun h1 a
  · exact h2 v hv

theorem eq_setPart_iff {w : Fin k ↪ Fin n} {y z : Qubits n} {u : Qubits k} :
    y = setPart z w u ↔ y ∘ w = u ∧ AgreeOff w y z := by
  constructor
  · rintro rfl
    exact ⟨setPart_comp z w u, agreeOff_setPart z w u⟩
  · rintro ⟨h1, h2⟩
    apply eq_of_comp_agree
    · rw [h1, setPart_comp]
    · intro a ha
      rw [h2 a ha, setPart_off z w u ha]

theorem setPart_setPart (z : Qubits n) (w : Fin k ↪ Fin n) (u u' : Qubits k) :
    setPart (setPart z w u) w u' = setPart z w u' := by
  apply eq_of_comp_agree
  · rw [setPart_comp, setPart_comp]
  · intro a ha
    rw [setPart_off _ w u' ha, setPart_off _ w u' ha, setPart_off _ w u ha]

theorem embedOp_of_agree (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n)
    {y z : Qubits n} (h : AgreeOff w y z) : embedOp M w y z = M (y ∘ w) (z ∘ w) := by
  unfold embedOp
  rw [Matrix.of_apply]
  exact if_pos h

theorem embedOp_of_not_agree (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n)
    {y z : Qubits n} (h : ¬ AgreeOff w y z) : embedOp M w y z = 0 := by
  unfold embedOp
  rw [Matrix.of_apply]
  exact if_neg h

/-- Basis vector as a plain function. -/
noncomputable abbrev bv (z : Qubits n) : Qubits n → ℂ := Pi.single z 1

theorem mat_ext_bv {A B : Matrix (Qubits n) (Qubits n) ℂ}
    (h : ∀ z, A.mulVec (bv z) = B.mulVec (bv z)) : A = B := by
  ext y z
  have := congrFun (h z) y
  simpa [Matrix.mulVec_single_one] using this

/-- Column formula for an embedded operator. -/
theorem embedOp_mulVec_bv (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n)
    (z : Qubits n) :
    (embedOp M w).mulVec (bv z) = ∑ u, M u (z ∘ w) • bv (setPart z w u) := by
  rw [Matrix.mulVec_single_one]
  funext y
  simp only [Matrix.col_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bv,
    Pi.single_apply]
  by_cases h : AgreeOff w y z
  · rw [embedOp_of_agree M w h]
    rw [Finset.sum_eq_single (y ∘ w)]
    · rw [if_pos ((eq_setPart_iff).2 ⟨rfl, h⟩), mul_one]
    · intro u _ hu
      rw [if_neg, mul_zero]
      intro hy
      exact hu ((eq_setPart_iff.1 hy).1).symm
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [embedOp_of_not_agree M w h]
    symm
    apply Finset.sum_eq_zero
    intro u _
    rw [if_neg, mul_zero]
    intro hy
    exact h (eq_setPart_iff.1 hy).2

theorem embedOp_mul (A B : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  apply mat_ext_bv
  intro z
  rw [← Matrix.mulVec_mulVec, embedOp_mulVec_bv, embedOp_mulVec_bv, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, embedOp_mulVec_bv, setPart_comp, setPart_setPart,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u' _
  rw [← Finset.sum_smul, Matrix.mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem agreeOff_trans_iff {m : ℕ} (w : Fin k ↪ Fin m) (e : Fin m ↪ Fin n) (y z : Qubits n) :
    AgreeOff (w.trans e) y z ↔ AgreeOff e y z ∧ AgreeOff w (y ∘ e) (z ∘ e) := by
  constructor
  · intro h
    refine ⟨fun a ha => h a ?_, fun b hb => h (e b) ?_⟩
    · rintro ⟨c, rfl⟩; exact ha ⟨w c, rfl⟩
    · rintro ⟨c, hc⟩
      apply hb
      exact ⟨c, e.injective hc⟩
  · rintro ⟨h1, h2⟩ a ha
    by_cases hae : a ∈ Set.range e
    · obtain ⟨b, rfl⟩ := hae
      apply h2 b
      rintro ⟨c, rfl⟩
      exact ha ⟨c, rfl⟩
    · exact h1 a hae

theorem embedOp_trans {m : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin m)
    (e : Fin m ↪ Fin n) : embedOp M (w.trans e) = embedOp (embedOp M w) e := by
  ext y z
  by_cases h : AgreeOff (w.trans e) y z
  · obtain ⟨h1, h2⟩ := (agreeOff_trans_iff w e y z).1 h
    rw [embedOp_of_agree M _ h, embedOp_of_agree _ e h1, embedOp_of_agree M w h2]
    rfl
  · rw [embedOp_of_not_agree M _ h]
    by_cases h1 : AgreeOff e y z
    · rw [embedOp_of_agree _ e h1, embedOp_of_not_agree]
      intro h2
      exact h ((agreeOff_trans_iff w e y z).2 ⟨h1, h2⟩)
    · rw [embedOp_of_not_agree _ e h1]

end Embed

/-! ### Oracle circuits: append, relabel -/

section Circ

variable {S : Set Gate} {r : ℕ} {a : Fin r → ℕ}

theorem unitary_nil {n : ℕ} (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary ([] : OracleCircuit S a n) orc = 1 := by
  simp [OracleCircuit.unitary]

theorem unitary_append {n : ℕ} (c₁ c₂ : OracleCircuit S a n)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary (c₁ ++ c₂) orc = c₂.unitary orc * c₁.unitary orc := by
  simp [OracleCircuit.unitary, List.map_append, List.reverse_append, List.prod_append]

theorem unitary_cons {n : ℕ} (s : OracleStep S a n) (c : OracleCircuit S a n)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    OracleCircuit.unitary (s :: c) orc = c.unitary orc * s.mat orc := by
  simp [OracleCircuit.unitary]

theorem queryCount_append {n : ℕ} (c₁ c₂ : OracleCircuit S a n) (k : Fin r) :
    (c₁ ++ c₂).queryCount k = c₁.queryCount k + c₂.queryCount k := by
  simp [OracleCircuit.queryCount, List.countP_append]

theorem gateCount_append {n : ℕ} (c₁ c₂ : OracleCircuit S a n) :
    (c₁ ++ c₂).gateCount = c₁.gateCount + c₂.gateCount := by
  simp [OracleCircuit.gateCount, List.countP_append]

/-- Relabel the wires of a step along `e`, dropping any control. -/
def relabelStep {m n : ℕ} (e : Fin m ↪ Fin n) : OracleStep S a m → OracleStep S a n
  | .gate g => .gate ⟨g.gate, g.mem, g.wires.trans e⟩
  | .query k adj _ wires _ => .query k adj none (wires.trans e) (by simp)

def relabel {m n : ℕ} (c : OracleCircuit S a m) (e : Fin m ↪ Fin n) : OracleCircuit S a n :=
  c.map (relabelStep e)

theorem relabel_unitary {m n : ℕ} (c : OracleCircuit S a m) (e : Fin m ↪ Fin n)
    (hc : QuantumLTF.Membership.Uncontrolled c)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    (relabel c e).unitary orc = embedOp (c.unitary orc) e := by
  induction c with
  | nil => simp [relabel, unitary_nil, embedOp_one]
  | cons s c ih =>
    have hc' : QuantumLTF.Membership.Uncontrolled c := fun st hst => hc st (List.mem_cons_of_mem _ hst)
    have hs := hc s List.mem_cons_self
    change OracleCircuit.unitary (relabelStep e s :: relabel c e) orc = _
    rw [unitary_cons, unitary_cons, ih hc', embedOp_mul]
    congr 1
    cases s with
    | gate g => simp only [relabelStep, OracleStep.mat]; exact embedOp_trans _ _ _
    | query k adj ctl wires hcw =>
      simp only at hs
      subst hs
      simp only [relabelStep, OracleStep.mat]
      exact embedOp_trans _ _ _

theorem relabel_queryCount {m n : ℕ} (c : OracleCircuit S a m) (e : Fin m ↪ Fin n) (k : Fin r) :
    (relabel c e).queryCount k = c.queryCount k := by
  unfold relabel OracleCircuit.queryCount
  rw [List.countP_map]
  congr 1
  funext s
  cases s <;> rfl

theorem relabel_gateCount {m n : ℕ} (c : OracleCircuit S a m) (e : Fin m ↪ Fin n) :
    (relabel c e).gateCount = c.gateCount := by
  unfold relabel OracleCircuit.gateCount
  rw [List.countP_map]
  congr 1
  funext s
  cases s <;> rfl

theorem relabel_uncontrolled {m n : ℕ} (c : OracleCircuit S a m) (e : Fin m ↪ Fin n) :
    QuantumLTF.Membership.Uncontrolled (relabel c e) := by
  intro st hst
  obtain ⟨s, _, rfl⟩ := List.mem_map.1 hst
  cases s <;> simp [relabelStep]

end Circ

end LTFC

-- ===== module Gates =====

open QAlgorithms

namespace LTFC

/-! ### Single and two-wire embeddings -/

def w1 {n : ℕ} (t : Fin n) : Fin 1 ↪ Fin n := ⟨fun _ => t, fun x y _ => Subsingleton.elim x y⟩

def w2 {n : ℕ} (a b : Fin n) (h : a ≠ b) : Fin 2 ↪ Fin n :=
  ⟨![a, b], by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [eq_comm]⟩

@[simp] theorem w1_apply {n : ℕ} (t : Fin n) (x : Fin 1) : w1 t x = t := rfl
@[simp] theorem w2_apply0 {n : ℕ} (a b : Fin n) (h : a ≠ b) : w2 a b h 0 = a := rfl
@[simp] theorem w2_apply1 {n : ℕ} (a b : Fin n) (h : a ≠ b) : w2 a b h 1 = b := rfl

theorem setPart_w1 {n : ℕ} (z : Qubits n) (t : Fin n) (u : Qubits 1) :
    setPart z (w1 t) u = Function.update z t (u 0) := by
  symm
  rw [eq_setPart_iff]
  refine ⟨?_, ?_⟩
  · funext x
    have : x = 0 := Subsingleton.elim _ _
    subst this
    simp
  · intro v hv
    have : v ≠ t := fun h => hv ⟨0, h.symm⟩
    simp [Function.update_of_ne this]

theorem setPart_w2 {n : ℕ} (z : Qubits n) (a b : Fin n) (h : a ≠ b) (u : Qubits 2) :
    setPart z (w2 a b h) u = Function.update (Function.update z a (u 0)) b (u 1) := by
  symm
  rw [eq_setPart_iff]
  refine ⟨?_, ?_⟩
  · funext x
    fin_cases x
    · simp [Function.update_of_ne h]
    · simp
  · intro v hv
    have h1 : v ≠ a := fun e => hv ⟨0, by simp [e]⟩
    have h2 : v ≠ b := fun e => hv ⟨1, by simp [e]⟩
    simp [Function.update_of_ne h1, Function.update_of_ne h2]

/-- Column formula for a one-qubit gate. -/
theorem mulVec_gate1 {n : ℕ} (M : Matrix Bool Bool ℂ) (t : Fin n) (z : Qubits n) :
    (embedOp (Gate.ofMatrix1 M).mat (w1 t)).mulVec (bv z) =
      ∑ c : Bool, M c (z t) • bv (Function.update z t c) := by
  refine (embedOp_mulVec_bv (k := 1) _ _ _).trans ?_
  simp only [setPart_w1]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) _ _ ?_
  intro u
  simp [Gate.ofMatrix1, Matrix.submatrix_apply]

/-- Column formula for a two-qubit gate. -/
theorem mulVec_gate2 {n : ℕ} (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) (a b : Fin n)
    (h : a ≠ b) (z : Qubits n) :
    (embedOp (Gate.ofMatrix2 M).mat (w2 a b h)).mulVec (bv z) =
      ∑ p : Bool × Bool, M p (z a, z b) • bv (Function.update (Function.update z a p.1) b p.2) := by
  refine (embedOp_mulVec_bv (k := 2) _ _ _).trans ?_
  simp only [setPart_w2]
  refine Fintype.sum_equiv (finTwoArrowEquiv Bool) _ _ ?_
  intro u
  simp [Gate.ofMatrix2, Matrix.submatrix_apply]

/-! ### The gates -/

theorem submatrix_unitary {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {M : Matrix β β ℂ} (hM : M ∈ Matrix.unitaryGroup β ℂ) :
    M.submatrix e e ∈ Matrix.unitaryGroup α ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, hM, Matrix.submatrix_one_equiv]

theorem ofMatrix1_unitary {M : Matrix Bool Bool ℂ} (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    (Gate.ofMatrix1 M).IsUnitary :=
  submatrix_unitary (Equiv.funUnique (Fin 1) Bool) hM

theorem ofMatrix2_unitary {M : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) : (Gate.ofMatrix2 M).IsUnitary := by
  exact submatrix_unitary (finTwoArrowEquiv Bool) hM

theorem ofMatrix1_mem {M : Matrix Bool Bool ℂ} (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    Gate.ofMatrix1 M ∈ QuantumLTF.Membership.gates12 :=
  ⟨ofMatrix1_unitary hM, le_refl _, by show 1 ≤ 2; norm_num⟩

theorem ofMatrix2_mem {M : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Gate.ofMatrix2 M ∈ QuantumLTF.Membership.gates12 :=
  ⟨ofMatrix2_unitary hM, by show 1 ≤ 2; norm_num, le_refl _⟩

theorem pauliX_unitary : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext x y
  cases x <;> cases y <;>
    simp [pauliX, Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply]

theorem cnot_unitary : cnot ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;>
    simp [cnot, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, Matrix.star_apply]

theorem hadamard_unitary : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : star hadamard = hadamard := by
    ext x y
    cases x <;> cases y <;> simp [hadamard, Matrix.star_apply, Complex.conj_ofReal]
  rw [hs, hadamard_mul_self]

/-- Two-qubit diagonal phase `diag(1,1,1,ζ)`. -/
def dphase (ζ : ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.diagonal fun p => if p.1 && p.2 then ζ else 1

theorem dphase_unitary {ζ : ℂ} (hζ : star ζ * ζ = 1) :
    dphase ζ ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [dphase, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext p
  simp only [Pi.star_apply]
  split_ifs
  · exact hζ
  · simp

theorem I_unit : star Complex.I * Complex.I = 1 := by
  simp [Complex.conj_I]

theorem negI_unit : star (-Complex.I) * (-Complex.I) = 1 := by
  simp [Complex.conj_I]

theorem mulVec_X {n : ℕ} (t : Fin n) (z : Qubits n) :
    (embedOp (Gate.ofMatrix1 pauliX).mat (w1 t)).mulVec (bv z) =
      bv (Function.update z t (!z t)) := by
  rw [mulVec_gate1]
  cases h : z t <;> simp [Fintype.sum_bool, pauliX]

theorem mulVec_cnot {n : ℕ} (a b : Fin n) (h : a ≠ b) (z : Qubits n) :
    (embedOp (Gate.ofMatrix2 cnot).mat (w2 a b h)).mulVec (bv z) =
      bv (Function.update z b (xor (z b) (z a))) := by
  rw [mulVec_gate2, Finset.sum_eq_single (z a, xor (z b) (z a))]
  · simp [cnot, Function.update_eq_self]
  · rintro ⟨p1, p2⟩ _ hp
    have : ¬ (p1 = z a ∧ p2 = xor (z b) (z a)) := fun ⟨h1, h2⟩ => hp (by rw [h1, h2])
    simp [cnot, this]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem mulVec_dphase {n : ℕ} (ζ : ℂ) (a b : Fin n) (h : a ≠ b) (z : Qubits n) :
    (embedOp (Gate.ofMatrix2 (dphase ζ)).mat (w2 a b h)).mulVec (bv z) =
      (if z a && z b then ζ else 1) • bv z := by
  rw [mulVec_gate2, Finset.sum_eq_single (z a, z b)]
  · simp [dphase, Function.update_eq_self]
  · rintro ⟨p1, p2⟩ _ hp
    have : (p1, p2) ≠ (z a, z b) := hp
    simp [dphase, Matrix.diagonal_apply_ne _ this]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem mulVec_H {n : ℕ} (t : Fin n) (z : Qubits n) :
    (embedOp (Gate.ofMatrix1 hadamard).mat (w1 t)).mulVec (bv z) =
      ∑ c : Bool, hadamard c (z t) • bv (Function.update z t c) :=
  mulVec_gate1 _ _ _

/-! ### Circuits implementing classical maps -/

section Impl

variable {r : ℕ} {ar : Fin r → ℕ}

/-- `c` maps every basis vector `|z⟩` to `|F z⟩`, for all oracles. -/
def Implements {S : Set Gate} {n : ℕ} (c : OracleCircuit S ar n) (F : Qubits n → Qubits n) :
    Prop :=
  ∀ (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ) (z : Qubits n),
    (c.unitary orc).mulVec (bv z) = bv (F z)

theorem Implements.nil {S : Set Gate} {n : ℕ} : Implements ([] : OracleCircuit S ar n) id := by
  intro orc z; rw [unitary_nil, Matrix.one_mulVec]; rfl

theorem Implements.append {S : Set Gate} {n : ℕ} {c₁ c₂ : OracleCircuit S ar n}
    {F₁ F₂ : Qubits n → Qubits n} (h₁ : Implements c₁ F₁) (h₂ : Implements c₂ F₂) :
    Implements (c₁ ++ c₂) (F₂ ∘ F₁) := by
  intro orc z
  rw [unitary_append, ← Matrix.mulVec_mulVec, h₁, h₂]
  rfl

theorem Implements.congr {S : Set Gate} {n : ℕ} {c : OracleCircuit S ar n}
    {F G : Qubits n → Qubits n} (h : Implements c F) (hFG : ∀ z, F z = G z) :
    Implements c G := by
  intro orc z; rw [h, hFG]

abbrev G12 := QuantumLTF.Membership.gates12

def stepX {n : ℕ} (t : Fin n) : OracleStep G12 ar n :=
  .gate ⟨Gate.ofMatrix1 pauliX, ofMatrix1_mem pauliX_unitary, w1 t⟩

def stepCNOT {n : ℕ} (a b : Fin n) (h : a ≠ b) : OracleStep G12 ar n :=
  .gate ⟨Gate.ofMatrix2 cnot, ofMatrix2_mem cnot_unitary, w2 a b h⟩

noncomputable def stepH {n : ℕ} (t : Fin n) : OracleStep G12 ar n :=
  .gate ⟨Gate.ofMatrix1 hadamard, ofMatrix1_mem hadamard_unitary, w1 t⟩

def stepD {n : ℕ} (ζ : ℂ) (hζ : star ζ * ζ = 1) (a b : Fin n) (h : a ≠ b) :
    OracleStep G12 ar n :=
  .gate ⟨Gate.ofMatrix2 (dphase ζ), ofMatrix2_mem (dphase_unitary hζ), w2 a b h⟩

theorem single_unitary {S : Set Gate} {n : ℕ} (s : OracleStep S ar n)
    (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ) :
    OracleCircuit.unitary [s] orc = s.mat orc := by
  simp [OracleCircuit.unitary]

theorem impl_X {n : ℕ} (t : Fin n) :
    Implements ([stepX t] : OracleCircuit G12 ar n) (fun z => Function.update z t (!z t)) := by
  intro orc z
  rw [single_unitary]
  exact mulVec_X t z

theorem impl_CNOT {n : ℕ} (a b : Fin n) (h : a ≠ b) :
    Implements ([stepCNOT a b h] : OracleCircuit G12 ar n)
      (fun z => Function.update z b (xor (z b) (z a))) := by
  intro orc z
  rw [single_unitary]
  exact mulVec_cnot a b h z

/-- The middle (diagonal) part of the Toffoli decomposition. -/
def toffMid {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    OracleCircuit G12 ar n :=
  [stepD Complex.I I_unit a t hat, stepD Complex.I I_unit b t hbt, stepCNOT a b hab,
    stepD (-Complex.I) negI_unit b t hbt, stepCNOT a b hab]

theorem toffMid_mulVec {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ) (y : Qubits n) :
    ((toffMid a b t hab hat hbt : OracleCircuit G12 ar n).unitary orc).mulVec (bv y) =
      (if y a && y b && y t then (-1 : ℂ) else 1) • bv y := by
  simp only [toffMid, OracleCircuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one,
    List.singleton_append]
  simp only [stepD, stepCNOT, OracleStep.mat]
  simp only [← Matrix.mulVec_mulVec, mulVec_dphase, Matrix.mulVec_smul, mulVec_cnot]
  have hta : t ≠ a := Ne.symm hat
  have htb : t ≠ b := Ne.symm hbt
  have hba : b ≠ a := Ne.symm hab
  simp only [Function.update_self, Function.update_of_ne hta, Function.update_of_ne htb,
    Function.update_of_ne hab, Function.update_idem, smul_smul]
  have hy : Function.update y b (xor (xor (y b) (y a)) (y a)) = y := by
    rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Function.update_eq_self]
  rw [hy]
  congr 1
  cases y a <;> cases y b <;> cases y t <;> simp

noncomputable def toffoli12 {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    OracleCircuit G12 ar n :=
  [stepH t] ++ toffMid a b t hab hat hbt ++ [stepH t]

theorem hzh (s x d : Bool) :
    ∑ c : Bool, hadamard d c * ((if s && c then (-1 : ℂ) else 1) * hadamard c x) =
      if d = xor x s then 1 else 0 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ 2 = 1 / 2 := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  cases s <;> cases x <;> cases d <;>
    simp [Fintype.sum_bool, hadamard] <;> ring_nf <;> simp only [h2] <;> norm_num

theorem impl_toffoli12 {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    Implements (toffoli12 a b t hab hat hbt : OracleCircuit G12 ar n)
      (fun z => Function.update z t (xor (z t) (z a && z b))) := by
  intro orc z
  unfold toffoli12
  rw [unitary_append, unitary_append, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [single_unitary]
  simp only [stepH, OracleStep.mat]
  rw [mulVec_H, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, toffMid_mulVec, smul_smul, Matrix.mulVec_sum, mulVec_H,
    Finset.smul_sum]
  have hta : t ≠ a := Ne.symm hat
  have htb : t ≠ b := Ne.symm hbt
  simp only [Function.update_self, Function.update_of_ne hat, Function.update_of_ne hbt,
    Function.update_idem]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have key2 : ∀ d : Bool, (∑ c : Bool, (hadamard c (z t) *
      (if (z a && z b && c) = true then (-1 : ℂ) else 1)) * hadamard d c) =
      if d = xor (z t) (z a && z b) then 1 else 0 := by
    intro d; rw [← hzh (z a && z b) (z t) d]; apply Finset.sum_congr rfl; intro c _; ring
  simp only [key2]
  rw [Finset.sum_eq_single (xor (z t) (z a && z b))]
  · simp
  · intro d _ hd; simp [hd]
  · intro h'; exact absurd (Finset.mem_univ _) h'

end Impl

end LTFC

-- ===== module SSA =====

open QAlgorithms

namespace LTFC

/-! ### Straight-line Boolean programs (SSA) -/

structure Instr where
  f : Bool → Bool → Bool
  a : ℕ
  b : ℕ

/-! ### Holds: properties of all evaluations of all extensions -/

def Ext (p p' : List Instr) : Prop := ∃ r, p' = p ++ r

theorem Ext.trans {p p' p'' : List Instr} (h₁ : Ext p p') (h₂ : Ext p' p'') : Ext p p'' := by
  obtain ⟨r, rfl⟩ := h₁; obtain ⟨r', rfl⟩ := h₂; exact ⟨r ++ r', by simp⟩

/-! ### Compilation to `gates12` -/

section Compile

variable {r : ℕ} {ar : Fin r → ℕ}

def toN {M : ℕ} (z : Qubits M) : ℕ → Bool := fun v => if h : v < M then z ⟨v, h⟩ else false

def flipT {M : ℕ} (t : Fin M) (φ : Qubits M → Bool) (z : Qubits M) : Qubits M :=
  Function.update z t (xor (z t) (φ z))

theorem impl_cond {S : Set Gate} {M : ℕ} {c : Bool} {L : OracleCircuit S ar M}
    {F : Qubits M → Qubits M} (h : Implements L F) :
    Implements (if c then L else []) (if c then F else id) := by
  cases c
  · exact Implements.nil
  · exact h

theorem impl_X_c {M : ℕ} (t : Fin M) (c : Bool) :
    Implements (if c then ([stepX t] : OracleCircuit G12 ar M) else []) (flipT t (fun _ => c)) := by
  apply (impl_cond (c := c) (impl_X t)).congr
  intro z
  cases c <;> simp [flipT]

theorem impl_CNOT_c {M : ℕ} (a t : Fin M) (h : a ≠ t) (c : Bool) :
    Implements (if c then ([stepCNOT a t h] : OracleCircuit G12 ar M) else [])
      (flipT t (fun z => c && z a)) := by
  apply (impl_cond (c := c) (impl_CNOT a t h)).congr
  intro z
  cases c <;> simp [flipT]

theorem impl_toff_c {M : ℕ} (a b t : Fin M) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (c : Bool) :
    Implements (if c then (toffoli12 a b t hab hat hbt : OracleCircuit G12 ar M) else [])
      (flipT t (fun z => c && (z a && z b))) := by
  apply (impl_cond (c := c) (impl_toffoli12 a b t hab hat hbt)).congr
  intro z
  cases c <;> simp [flipT]

theorem flipT_comp {M : ℕ} (t : Fin M) (φ₁ φ₂ : Qubits M → Bool)
    (h₂ : ∀ z v, φ₂ (Function.update z t v) = φ₂ z) (z : Qubits M) :
    flipT t φ₂ (flipT t φ₁ z) = flipT t (fun z => xor (φ₁ z) (φ₂ z)) z := by
  simp only [flipT, h₂, Function.update_self, Function.update_idem, Bool.xor_assoc]

/-- Circuit for instruction `g` writing variable `pos`. -/
noncomputable def instrCirc (M : ℕ) (g : Instr) (pos : ℕ) : OracleCircuit G12 ar M :=
  if h : pos < M ∧ g.a < pos ∧ g.b < pos then
    if hab : g.a = g.b then
      (if g.f false false then [stepX ⟨pos, h.1⟩] else []) ++
      (if xor (g.f false false) (g.f true true) then
        [stepCNOT ⟨g.a, by omega⟩ ⟨pos, h.1⟩ (by simp; omega)] else [])
    else
      (if g.f false false then [stepX ⟨pos, h.1⟩] else []) ++
      (if xor (g.f false false) (g.f true false) then
        [stepCNOT ⟨g.a, by omega⟩ ⟨pos, h.1⟩ (by simp; omega)] else []) ++
      (if xor (g.f false false) (g.f false true) then
        [stepCNOT ⟨g.b, by omega⟩ ⟨pos, h.1⟩ (by simp; omega)] else []) ++
      (if xor (xor (g.f false false) (g.f true false)) (xor (g.f false true) (g.f true true)) then
        toffoli12 ⟨g.a, by omega⟩ ⟨g.b, by omega⟩ ⟨pos, h.1⟩ (by simp; omega) (by simp; omega)
          (by simp; omega) else [])
  else []

def stepF (M : ℕ) (g : Instr) (pos : ℕ) (z : Qubits M) : Qubits M :=
  if h : pos < M ∧ g.a < pos ∧ g.b < pos then
    Function.update z ⟨pos, h.1⟩
      (xor (z ⟨pos, h.1⟩) (g.f (z ⟨g.a, by omega⟩) (z ⟨g.b, by omega⟩)))
  else z

theorem impl_instr (M : ℕ) (g : Instr) (pos : ℕ) :
    Implements (instrCirc M g pos : OracleCircuit G12 ar M) (stepF M g pos) := by
  unfold instrCirc stepF
  by_cases h : pos < M ∧ g.a < pos ∧ g.b < pos
  · rw [dif_pos h]
    have hne : ∀ x : ℕ, ∀ hx : x < pos, (⟨x, by omega⟩ : Fin M) ≠ ⟨pos, h.1⟩ := by
      intro x hx e; simp at e; omega
    by_cases hab : g.a = g.b
    · rw [dif_pos hab]
      refine ((impl_X_c _ _).append (impl_CNOT_c _ _ _ _)).congr ?_
      intro z
      simp only [Function.comp_apply]
      rw [flipT_comp]
      · simp only [flipT, dif_pos h]
        congr 2
        have e : (⟨g.b, by omega⟩ : Fin M) = ⟨g.a, by omega⟩ := by simp [hab]
        rw [e]
        cases z ⟨g.a, by omega⟩ <;> cases g.f false false <;> cases g.f true true <;> rfl
      · intro z v; rw [Function.update_of_ne (hne _ h.2.1)]
    · rw [dif_neg hab]
      refine ((((impl_X_c _ _).append (impl_CNOT_c _ _ _ _)).append
        (impl_CNOT_c _ _ _ _)).append (impl_toff_c _ _ _ _ _ _ _)).congr ?_
      intro z
      simp only [Function.comp_apply]
      have hp : ∀ (z : Qubits M) (v : Bool) (x : ℕ) (hx : x < pos),
          Function.update z (⟨pos, h.1⟩ : Fin M) v (⟨x, by omega⟩ : Fin M) = z ⟨x, by omega⟩ :=
        fun z v x hx => Function.update_of_ne (hne x hx) _ _
      rw [flipT_comp, flipT_comp, flipT_comp]
      · simp only [flipT, dif_pos h]
        congr 2
        cases z ⟨g.a, by omega⟩ <;> cases z ⟨g.b, by omega⟩ <;> cases g.f false false <;>
          cases g.f true false <;> cases g.f false true <;> cases g.f true true <;> rfl
      all_goals intro z v; simp only [hp _ _ _ h.2.1, hp _ _ _ h.2.2]
  · rw [dif_neg h]
    exact Implements.nil.congr (fun z => by rw [dif_neg h]; rfl)

/-! Resource counts. -/

def AllGates {S : Set Gate} {M : ℕ} (c : OracleCircuit S ar M) : Prop :=
  ∀ s ∈ c, ∃ g, s = OracleStep.gate g

theorem AllGates.append {S : Set Gate} {M : ℕ} {c₁ c₂ : OracleCircuit S ar M}
    (h₁ : AllGates c₁) (h₂ : AllGates c₂) : AllGates (c₁ ++ c₂) := by
  intro s hs
  rcases List.mem_append.1 hs with h | h
  · exact h₁ s h
  · exact h₂ s h

theorem AllGates.nil {S : Set Gate} {M : ℕ} : AllGates ([] : OracleCircuit S ar M) := by
  intro s hs; simp at hs

theorem AllGates.cond {S : Set Gate} {M : ℕ} {c : OracleCircuit S ar M} (h : AllGates c)
    (b : Bool) : AllGates (if b then c else []) := by
  cases b
  · exact AllGates.nil
  · exact h

theorem AllGates.queryCount {S : Set Gate} {M : ℕ} {c : OracleCircuit S ar M} (h : AllGates c)
    (k : Fin r) : c.queryCount k = 0 := by
  unfold OracleCircuit.queryCount
  rw [List.countP_eq_zero]
  intro s hs
  obtain ⟨g, rfl⟩ := h s hs
  simp [OracleStep.IsQueryTo]

theorem AllGates.gateCount {S : Set Gate} {M : ℕ} {c : OracleCircuit S ar M} (h : AllGates c) :
    c.gateCount = c.length := by
  unfold OracleCircuit.gateCount
  rw [List.countP_eq_length]
  intro s hs
  obtain ⟨g, rfl⟩ := h s hs
  rfl

theorem AllGates.uncontrolled {S : Set Gate} {M : ℕ} {c : OracleCircuit S ar M}
    (h : AllGates c) : QuantumLTF.Membership.Uncontrolled c := by
  intro s hs
  obtain ⟨g, rfl⟩ := h s hs
  trivial

theorem allGates_toffoli12 {M : ℕ} (a b t : Fin M) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    AllGates (toffoli12 a b t hab hat hbt : OracleCircuit G12 ar M) := by
  intro s hs
  simp only [toffoli12, toffMid, List.cons_append, List.singleton_append, List.nil_append,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h <;> subst h <;> exact ⟨_, rfl⟩

theorem allGates_single {M : ℕ} (s : OracleStep G12 ar M) (h : ∃ g, s = OracleStep.gate g) :
    AllGates ([s] : OracleCircuit G12 ar M) := by
  intro s' hs; simp at hs; subst hs; exact h

theorem allGates_instr (M : ℕ) (g : Instr) (pos : ℕ) :
    AllGates (instrCirc M g pos : OracleCircuit G12 ar M) := by
  unfold instrCirc
  by_cases h : pos < M ∧ g.a < pos ∧ g.b < pos
  · rw [dif_pos h]
    by_cases hab : g.a = g.b
    · rw [dif_pos hab]
      exact (AllGates.cond (allGates_single _ ⟨_, rfl⟩) _).append
        (AllGates.cond (allGates_single _ ⟨_, rfl⟩) _)
    · rw [dif_neg hab]
      exact (((AllGates.cond (allGates_single _ ⟨_, rfl⟩) _).append
        (AllGates.cond (allGates_single _ ⟨_, rfl⟩) _)).append
        (AllGates.cond (allGates_single _ ⟨_, rfl⟩) _)).append
        (AllGates.cond (allGates_toffoli12 _ _ _ _ _ _) _)
  · rw [dif_neg h]
    exact AllGates.nil

theorem length_cond {α : Type} (b : Bool) (l : List α) : (if b then l else []).length ≤ l.length := by
  cases b <;> simp

theorem length_instr (M : ℕ) (g : Instr) (pos : ℕ) :
    (instrCirc M g pos : OracleCircuit G12 ar M).length ≤ 10 := by
  unfold instrCirc
  by_cases h : pos < M ∧ g.a < pos ∧ g.b < pos
  · rw [dif_pos h]
    by_cases hab : g.a = g.b
    · rw [dif_pos hab]
      simp only [List.length_append]
      have h1 := length_cond (g.f false false) ([stepX (ar := ar) ⟨pos, h.1⟩])
      have h2 := length_cond (xor (g.f false false) (g.f true true))
        ([stepCNOT (ar := ar) (n := M) ⟨g.a, by omega⟩ ⟨pos, h.1⟩ (by simp; omega)])
      simp only [List.length_singleton] at h1 h2
      omega
    · rw [dif_neg hab]
      simp only [List.length_append]
      have h1 := length_cond (g.f false false) ([stepX (ar := ar) ⟨pos, h.1⟩])
      have h2 := length_cond (xor (g.f false false) (g.f true false))
        ([stepCNOT (ar := ar) (n := M) ⟨g.a, by omega⟩ ⟨pos, h.1⟩ (by simp; omega)])
      have h3 := length_cond (xor (g.f false false) (g.f false true))
        ([stepCNOT (ar := ar) (n := M) ⟨g.b, by omega⟩ ⟨pos, h.1⟩ (by simp; omega)])
      have h4 := length_cond (xor (xor (g.f false false) (g.f true false))
        (xor (g.f false true) (g.f true true)))
        (toffoli12 (ar := ar) (n := M) ⟨g.a, by omega⟩ ⟨g.b, by omega⟩ ⟨pos, h.1⟩
          (by simp; omega) (by simp; omega) (by simp; omega))
      simp only [List.length_singleton] at h1 h2 h3
      have h5 : (toffoli12 (ar := ar) (n := M) ⟨g.a, by omega⟩ ⟨g.b, by omega⟩ ⟨pos, h.1⟩
          (by simp; omega) (by simp; omega) (by simp; omega)).length = 7 := rfl
      omega
  · rw [dif_neg h]; simp

end Compile

end LTFC

-- ===== module MedMath =====

namespace LTFC

/-- Most-significant-bit-first value with accumulator. -/
def msb : ℕ → List Bool → ℕ
  | acc, [] => acc
  | acc, b :: bs => msb (2 * acc + b.toNat) bs

end LTFC

-- ===== module Build =====

namespace LTFC

def numVal (σ : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | x :: xs => (σ x).toNat + 2 * numVal σ xs

section Build

variable (B : ℕ)

/-! ### Ripple-carry adder (LSB first) -/

theorem full_adder (a b c : Bool) :
    a.toNat + b.toNat + c.toNat =
      (xor (xor a b) c).toNat + 2 * ((a && b) || (c && xor a b)).toNat := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ### Counting tree -/

/-! ### Comparison with a constant -/

/-! ### Threshold -/

end Build

end LTFC

-- ===== module Median =====

namespace LTFC

section Median

variable (B : ℕ)

/-! ### The bit loop -/

/-! ### All coordinates -/

end Median

end LTFC

-- ===== module Prog =====

open QAlgorithms

namespace LTFC

theorem msb_acc : ∀ (l : List Bool) (acc : ℕ), msb acc l = acc * 2 ^ l.length + msb 0 l := by
  intro l
  induction l with
  | nil => intro acc; simp [msb]
  | cons b l ih =>
    intro acc
    simp only [msb, List.length_cons]
    rw [ih, ih (0 * 2 + b.toNat)]
    rw [pow_succ]; ring

theorem msb_ofFn {ℓ : ℕ} (b : Fin ℓ → Bool) : msb 0 (List.ofFn b) = bitsToNat b := by
  induction ℓ with
  | zero => simp [msb, bitsToNat]
  | succ ℓ ih =>
    rw [List.ofFn_succ, msb, msb_acc, ih, bitsToNat, bitsToNat, Fin.sum_univ_succ]
    simp only [List.length_ofFn, Fin.val_zero, Fin.val_succ]
    congr 1
    · cases b 0 <;> simp
    · apply Finset.sum_congr rfl
      intro i _
      congr 2
      omega

section Prog

variable (k m n ℓo : ℕ) (oa : Fin n → (Fin ℓo ↪ Fin m))

end Prog

end LTFC

-- ===== module Quantum =====

open QAlgorithms

namespace LTFC

/-! ### Unitarity -/

theorem agreeOff_symm {k n : ℕ} {w : Fin k ↪ Fin n} {y z : Qubits n} (h : AgreeOff w y z) :
    AgreeOff w z y := fun a ha => (h a ha).symm

theorem embedOp_star {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (star M) w = star (embedOp M w) := by
  ext y z
  rw [Matrix.star_apply]
  by_cases h : AgreeOff w y z
  · rw [embedOp_of_agree _ w h, embedOp_of_agree _ w (agreeOff_symm h), Matrix.star_apply]
  · rw [embedOp_of_not_agree _ w h, embedOp_of_not_agree _ w (fun h' => h (agreeOff_symm h')),
      star_zero]

theorem embedOp_unitary {k n : ℕ} {M : Matrix (Qubits k) (Qubits k) ℂ} (w : Fin k ↪ Fin n)
    (hM : M ∈ Matrix.unitaryGroup (Qubits k) ℂ) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  rw [← embedOp_star, ← embedOp_mul, hM, embedOp_one]

theorem circuit_unitary {r : ℕ} {ar : Fin r → ℕ} {M : ℕ} (c : OracleCircuit G12 ar M)
    (hc : QuantumLTF.Membership.Uncontrolled c)
    (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ)
    (horc : ∀ k, orc k ∈ Matrix.unitaryGroup (Qubits (ar k)) ℂ) :
    c.unitary orc ∈ Matrix.unitaryGroup (Qubits M) ℂ := by
  induction c with
  | nil => rw [unitary_nil]; exact one_mem _
  | cons s c ih =>
    have hc' : QuantumLTF.Membership.Uncontrolled c :=
      fun st hst => hc st (List.mem_cons_of_mem _ hst)
    have hs := hc s List.mem_cons_self
    rw [unitary_cons]
    refine mul_mem (ih hc') ?_
    cases s with
    | gate g => exact embedOp_unitary _ g.mem.1
    | query k adj ctl wires hcw =>
      simp only at hs
      subst hs
      simp only [OracleStep.mat]
      apply embedOp_unitary
      split_ifs
      · exact Unitary.star_mem (horc k)
      · exact horc k

/-! ### Probabilities -/

theorem probEvent_zero {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (E : Qubits n → Prop)
    [DecidablePred E] :
    probEvent (act U (zeroKet n)) E =
      ∑ y ∈ Finset.univ.filter E, ‖(U.mulVec (bv (fun _ => false))) y‖ ^ 2 := by
  unfold probEvent prob
  apply Finset.sum_congr rfl
  intro y _
  rw [ket, EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul]
  rfl

theorem colsum_one {n : ℕ} {U : Matrix (Qubits n) (Qubits n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (z : Qubits n) :
    ∑ y, ‖U y z‖ ^ 2 = 1 := by
  rw [Matrix.mem_unitaryGroup_iff'] at hU
  have := congrFun (congrFun hU z) z
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
  simp only [Matrix.star_apply] at this
  have h2 : ∀ y, star (U y z) * U y z = ((‖U y z‖ ^ 2 : ℝ) : ℂ) := by
    intro y; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  simp only [h2] at this
  exact_mod_cast this

/-! ### Repeated copies -/

section Copies

variable {r : ℕ} {ar : Fin r → ℕ}

def embJ (m M j : ℕ) (h : (j + 1) * m ≤ M) : Fin m ↪ Fin M :=
  ⟨fun u => ⟨j * m + u, by have := u.isLt; rw [Nat.add_mul, one_mul] at h; omega⟩, by
    intro u v huv; simp at huv; exact Fin.ext huv⟩

@[simp] theorem embJ_val (m M j : ℕ) (h : (j + 1) * m ≤ M) (u : Fin m) :
    (embJ m M j h u).val = j * m + u.val := rfl

end Copies

end LTFC

-- ===== module Main1 =====

open QAlgorithms

namespace LTFC

/-! ### Injectivity of the classical part -/

theorem stepF_invol (M : ℕ) (g : Instr) (pos : ℕ) (z : Qubits M) :
    stepF M g pos (stepF M g pos z) = z := by
  unfold stepF
  by_cases h : pos < M ∧ g.a < pos ∧ g.b < pos
  · rw [dif_pos h, dif_pos h]
    have ha : (⟨g.a, by omega⟩ : Fin M) ≠ ⟨pos, h.1⟩ := by simp; omega
    have hb : (⟨g.b, by omega⟩ : Fin M) ≠ ⟨pos, h.1⟩ := by simp; omega
    rw [Function.update_of_ne ha, Function.update_of_ne hb, Function.update_self,
      Function.update_idem, Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Function.update_eq_self]
  · rw [dif_neg h, dif_neg h]

/-! ### Counting for copies -/

section Counts

variable {r : ℕ} {ar : Fin r → ℕ}

theorem uncontrolled_append {S : Set Gate} {M : ℕ} {c₁ c₂ : OracleCircuit S ar M}
    (h₁ : QuantumLTF.Membership.Uncontrolled c₁) (h₂ : QuantumLTF.Membership.Uncontrolled c₂) :
    QuantumLTF.Membership.Uncontrolled (c₁ ++ c₂) := by
  intro st hst
  rcases List.mem_append.1 hst with h | h
  · exact h₁ st h
  · exact h₂ st h

end Counts

/-! ### Spreading `k` blocks into a register -/

/-! ### The amplified circuit -/

section Amp

variable (a k m n ℓo : ℕ) (oa : Fin n → (Fin ℓo ↪ Fin m))

end Amp

end LTFC

-- ===== module SSAO =====

/-!
# Straight-line programs with oracle instructions

An instruction is either a binary Boolean instruction (`Instr`) or an oracle call reading `K`
earlier variables `addr` and writing `O (values of addr)`. Compiled, an oracle instruction is one
plain (uncontrolled) query on the wires `addr ++ [pos]`.
-/

open QAlgorithms

namespace LTFC

inductive OIns (K : ℕ) where
  | bin (g : Instr)
  | orc (addr : Fin K → ℕ)

section SvalO

variable {K : ℕ} (O : (Fin K → Bool) → Bool) (B : ℕ)

open Classical in
noncomputable def evalIns (g : OIns K) (v : ℕ) (val : (u : ℕ) → u < v → Bool) : Bool :=
  match g with
  | .bin g => if ha : g.a < v ∧ g.b < v then g.f (val g.a ha.1) (val g.b ha.2) else false
  | .orc addr =>
    if ha : (∀ j, addr j < v) ∧ Function.Injective addr then
      O (fun j => val (addr j) (ha.1 j)) else false

theorem evalIns_congr (g : OIns K) (v : ℕ) (val val' : (u : ℕ) → u < v → Bool)
    (h : ∀ u hu, val u hu = val' u hu) : evalIns O g v val = evalIns O g v val' := by
  cases g with
  | bin g => simp only [evalIns]; split_ifs <;> simp [h]
  | orc addr => simp only [evalIns]; split_ifs <;> simp [h]

theorem evalIns_bin (g : Instr) (v : ℕ) (val : (u : ℕ) → u < v → Bool)
    (ha : g.a < v) (hb : g.b < v) : evalIns O (.bin g) v val = g.f (val g.a ha) (val g.b hb) := by
  simp only [evalIns, dif_pos (And.intro ha hb)]

theorem evalIns_bin_invalid (g : Instr) (v : ℕ) (val : (u : ℕ) → u < v → Bool)
    (h : ¬ (g.a < v ∧ g.b < v)) : evalIns O (.bin g) v val = false := by
  simp only [evalIns, dif_neg h]

theorem evalIns_orc (addr : Fin K → ℕ) (v : ℕ) (val : (u : ℕ) → u < v → Bool)
    (ha : ∀ j, addr j < v) (hinj : Function.Injective addr) :
    evalIns O (.orc addr) v val = O (fun j => val (addr j) (ha j)) := by
  simp only [evalIns, dif_pos (And.intro ha hinj)]

theorem evalIns_orc_invalid (addr : Fin K → ℕ) (v : ℕ) (val : (u : ℕ) → u < v → Bool)
    (h : ¬ ((∀ j, addr j < v) ∧ Function.Injective addr)) :
    evalIns O (.orc addr) v val = false := by
  simp only [evalIns, dif_neg h]

noncomputable def svalO (P : List (OIns K)) (inp : ℕ → Bool) (v : ℕ) : Bool :=
  if v < B then inp v else
    if h : v - B < P.length then
      evalIns O P[v - B] v (fun u _ => svalO P inp u)
    else false
termination_by v

theorem svalO_lt (P : List (OIns K)) (inp : ℕ → Bool) {v : ℕ} (hv : v < B) :
    svalO O B P inp v = inp v := by
  rw [svalO, if_pos hv]

theorem svalO_at (P : List (OIns K)) (inp : ℕ → Bool) (i : ℕ) (hi : i < P.length) :
    svalO O B P inp (B + i) = evalIns O P[i] (B + i) (fun u _ => svalO O B P inp u) := by
  rw [svalO, if_neg (by omega)]
  have e : B + i - B = i := by omega
  simp only [e]
  rw [dif_pos hi]

theorem svalO_at_bin (P : List (OIns K)) (inp : ℕ → Bool) (i : ℕ) (hi : i < P.length)
    (g : Instr) (hg : P[i] = .bin g) (ha : g.a < B + i) (hb : g.b < B + i) :
    svalO O B P inp (B + i) = g.f (svalO O B P inp g.a) (svalO O B P inp g.b) := by
  rw [svalO_at O B P inp i hi, hg, evalIns_bin O g _ _ ha hb]

theorem svalO_at_bin_invalid (P : List (OIns K)) (inp : ℕ → Bool) (i : ℕ) (hi : i < P.length)
    (g : Instr) (hg : P[i] = .bin g) (h : ¬ (g.a < B + i ∧ g.b < B + i)) :
    svalO O B P inp (B + i) = false := by
  rw [svalO_at O B P inp i hi, hg, evalIns_bin_invalid O g _ _ h]

theorem svalO_at_orc (P : List (OIns K)) (inp : ℕ → Bool) (i : ℕ) (hi : i < P.length)
    (addr : Fin K → ℕ) (hg : P[i] = .orc addr) (ha : ∀ j, addr j < B + i)
    (hinj : Function.Injective addr) :
    svalO O B P inp (B + i) = O (fun j => svalO O B P inp (addr j)) := by
  rw [svalO_at O B P inp i hi, hg, evalIns_orc O addr _ _ ha hinj]

theorem svalO_at_orc_invalid (P : List (OIns K)) (inp : ℕ → Bool) (i : ℕ) (hi : i < P.length)
    (addr : Fin K → ℕ) (hg : P[i] = .orc addr)
    (h : ¬ ((∀ j, addr j < B + i) ∧ Function.Injective addr)) :
    svalO O B P inp (B + i) = false := by
  rw [svalO_at O B P inp i hi, hg, evalIns_orc_invalid O addr _ _ h]

open Classical in
/-- Value written by the first instruction of a program at base `B`, from the inputs. -/
noncomputable def firstVal (g : OIns K) (inp : ℕ → Bool) : Bool :=
  match g with
  | .bin g => if g.a < B ∧ g.b < B then g.f (inp g.a) (inp g.b) else false
  | .orc addr => if (∀ j, addr j < B) ∧ Function.Injective addr then O (fun j => inp (addr j))
      else false

theorem svalO_cons (g : OIns K) (gs : List (OIns K)) (inp : ℕ → Bool) :
    ∀ v, svalO O B (g :: gs) inp v =
      svalO O (B + 1) gs (Function.update inp B (firstVal O B g inp)) v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  by_cases hB : v < B
  · rw [svalO_lt _ _ _ _ hB, svalO_lt _ _ _ _ (show v < B + 1 by omega),
      Function.update_of_ne (show v ≠ B by omega)]
  by_cases hB1 : v = B
  · rw [hB1, svalO_lt _ _ _ _ (show B < B + 1 by omega), Function.update_self]
    cases g with
    | bin g =>
      have h0 := svalO_at_bin O B (.bin g :: gs) inp 0 (by simp) g rfl
      have h0' := svalO_at_bin_invalid O B (.bin g :: gs) inp 0 (by simp) g rfl
      simp only [Nat.add_zero] at h0 h0'
      simp only [firstVal]
      by_cases hc : g.a < B ∧ g.b < B
      · rw [if_pos hc, h0 hc.1 hc.2, svalO_lt _ _ _ _ hc.1, svalO_lt _ _ _ _ hc.2]
      · rw [if_neg hc]; exact h0' hc
    | orc addr =>
      have h0 := svalO_at_orc O B (.orc addr :: gs) inp 0 (by simp) addr rfl
      have h0' := svalO_at_orc_invalid O B (.orc addr :: gs) inp 0 (by simp) addr rfl
      simp only [Nat.add_zero] at h0 h0'
      simp only [firstVal]
      by_cases hc : (∀ j, addr j < B) ∧ Function.Injective addr
      · rw [if_pos hc, h0 hc.1 hc.2]
        congr 1; funext j; exact svalO_lt _ _ _ _ (hc.1 j)
      · rw [if_neg hc]; exact h0' hc
  · rw [svalO, svalO, if_neg hB, if_neg (show ¬ v < B + 1 by omega)]
    have e : v - B = (v - (B + 1)) + 1 := by omega
    by_cases hl : v - (B + 1) < gs.length
    · have hl' : v - B < (g :: gs).length := by simp; omega
      rw [dif_pos hl', dif_pos hl]
      have he : (g :: gs)[v - B] = gs[v - (B + 1)] := by
        simp only [e, List.getElem_cons_succ]
      rw [he]
      exact evalIns_congr O _ _ _ _ (fun u hu => ih u hu)
    · have hl' : ¬ (v - B < (g :: gs).length) := by simp; omega
      rw [dif_neg hl', dif_neg hl]

/-! ### Holds / extensions for oracle programs -/

def HoldsO (p : List (OIns K)) (Q : (ℕ → Bool) → Prop) : Prop :=
  ∀ q inp, Q (svalO O B (p ++ q) inp)

def ExtL {α : Type} (p p' : List α) : Prop := ∃ r, p' = p ++ r

theorem ExtL.refl {α : Type} (p : List α) : ExtL p p := ⟨[], by simp⟩

theorem ExtL.trans {α : Type} {p p' p'' : List α} (h₁ : ExtL p p') (h₂ : ExtL p' p'') :
    ExtL p p'' := by
  obtain ⟨r, rfl⟩ := h₁; obtain ⟨r', rfl⟩ := h₂; exact ⟨r ++ r', by simp⟩

theorem ExtL.app {α : Type} (p r : List α) : ExtL p (p ++ r) := ⟨r, rfl⟩

theorem ExtL.length_le {α : Type} {p p' : List α} (h : ExtL p p') : p.length ≤ p'.length := by
  obtain ⟨r, rfl⟩ := h; simp

variable {O B}

theorem HoldsO.mono {p p' : List (OIns K)} {Q : (ℕ → Bool) → Prop} (h : HoldsO O B p Q)
    (he : ExtL p p') : HoldsO O B p' Q := by
  obtain ⟨r, rfl⟩ := he
  intro q inp
  have := h (r ++ q) inp
  simpa [List.append_assoc] using this

theorem HoldsO.and {p : List (OIns K)} {Q₁ Q₂ : (ℕ → Bool) → Prop} (h₁ : HoldsO O B p Q₁)
    (h₂ : HoldsO O B p Q₂) : HoldsO O B p (fun σ => Q₁ σ ∧ Q₂ σ) :=
  fun q inp => ⟨h₁ q inp, h₂ q inp⟩

theorem HoldsO.imp {p : List (OIns K)} {Q₁ Q₂ : (ℕ → Bool) → Prop} (h₁ : HoldsO O B p Q₁)
    (h : ∀ σ, Q₁ σ → Q₂ σ) : HoldsO O B p Q₂ := fun q inp => h _ (h₁ q inp)

variable (O B)

theorem holdsO_list (p : List (OIns K)) (gs : List Instr)
    (hg : ∀ i (hi : i < gs.length), gs[i].a < B + p.length + i ∧ gs[i].b < B + p.length + i) :
    HoldsO O B (p ++ gs.map OIns.bin) (fun σ => ∀ i (hi : i < gs.length),
      σ (B + p.length + i) = gs[i].f (σ gs[i].a) (σ gs[i].b)) := by
  intro q inp i hi
  have hi' : p.length + i < (p ++ gs.map OIns.bin ++ q).length := by simp; omega
  have hget : (p ++ gs.map OIns.bin ++ q)[p.length + i] = .bin gs[i] := by
    rw [List.getElem_append_left (by simp only [List.length_append, List.length_map]; omega)]
    rw [List.getElem_append_right (by omega)]
    simp
  have := svalO_at_bin O B (p ++ gs.map OIns.bin ++ q) inp (p.length + i) hi' gs[i] hget
    (by have := (hg i hi).1; omega) (by have := (hg i hi).2; omega)
  rw [← this, Nat.add_assoc]

theorem holdsO_orc (p : List (OIns K)) (addr : Fin K → ℕ) (ha : ∀ j, addr j < B + p.length)
    (hinj : Function.Injective addr) :
    HoldsO O B (p ++ [.orc addr]) (fun σ => σ (B + p.length) = O (fun j => σ (addr j))) := by
  intro q inp
  have hi' : p.length < (p ++ [OIns.orc addr] ++ q).length := by simp
  have hget : (p ++ [OIns.orc addr] ++ q)[p.length] = .orc addr := by simp
  exact svalO_at_orc O B _ inp p.length hi' addr hget ha hinj

end SvalO

/-! ### Compilation with the membership oracle -/

section CompileO

variable {a : ℕ}

/-- `c` maps `|z⟩` to `|F z⟩` for the given oracle. -/
def ImplAt {S : Set Gate} {M : ℕ} (c : OracleCircuit S (fun _ : Fin 1 => a) M)
    (orc : Matrix (Qubits a) (Qubits a) ℂ) (F : Qubits M → Qubits M) : Prop :=
  ∀ z, (c.unitary fun _ => orc).mulVec (bv z) = bv (F z)

theorem ImplAt.append {S : Set Gate} {M : ℕ} {c₁ c₂ : OracleCircuit S (fun _ : Fin 1 => a) M}
    {orc : Matrix (Qubits a) (Qubits a) ℂ} {F₁ F₂ : Qubits M → Qubits M}
    (h₁ : ImplAt c₁ orc F₁) (h₂ : ImplAt c₂ orc F₂) : ImplAt (c₁ ++ c₂) orc (F₂ ∘ F₁) := by
  intro z
  rw [unitary_append, ← Matrix.mulVec_mulVec, h₁, h₂]
  rfl

theorem ImplAt.of_impl {S : Set Gate} {M : ℕ} {c : OracleCircuit S (fun _ : Fin 1 => a) M}
    {F : Qubits M → Qubits M} (h : Implements c F) (orc : Matrix (Qubits a) (Qubits a) ℂ) :
    ImplAt c orc F := fun z => h _ z

end CompileO

end LTFC

-- ===== module CompO =====

open QAlgorithms

namespace LTFC

section CompO

variable {K : ℕ}

/-- A classical oracle matrix: `|y, b⟩ ↦ |y, b ⊕ O y⟩`. -/
def IsClassicalOracle (O : (Fin K → Bool) → Bool) (Mo : Matrix (Qubits (K + 1)) (Qubits (K + 1)) ℂ) :
    Prop :=
  ∀ y x, Mo y x = if y = Fin.snoc (α := fun _ => Bool) (Fin.init x)
      (xor (x (Fin.last _)) (O (Fin.init x))) then 1 else 0

theorem memOracle_classical (n ℓ f : ℕ) (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    IsClassicalOracle (K := n * ℓ)
      (fun y => decide (QuantumLTF.Membership.ltf w θ (QuantumLTF.Membership.addrOf n ℓ f y) = -1))
      (QuantumLTF.Membership.memOracle n ℓ f w θ) := by
  intro y x; rfl

def wiresFun (M pos : ℕ) (addr : Fin K → ℕ) (hpos : pos < M) (ha : ∀ j, addr j < pos)
    (j : Fin (K + 1)) : Fin M :=
  if h : j.val < K then ⟨addr ⟨j.val, h⟩, by have := ha ⟨j.val, h⟩; omega⟩ else ⟨pos, hpos⟩

theorem wiresFun_last (M pos : ℕ) (addr : Fin K → ℕ) (hpos : pos < M) (ha : ∀ j, addr j < pos) :
    (wiresFun M pos addr hpos ha (Fin.last K)).val = pos := by
  unfold wiresFun; rw [dif_neg (by simp)]

theorem wiresFun_cast (M pos : ℕ) (addr : Fin K → ℕ) (hpos : pos < M) (ha : ∀ j, addr j < pos)
    (j : Fin K) : (wiresFun M pos addr hpos ha j.castSucc).val = addr j := by
  unfold wiresFun; rw [dif_pos (by simp)]; rfl

theorem wiresFun_val (M pos : ℕ) (addr : Fin K → ℕ) (hpos : pos < M) (ha : ∀ j, addr j < pos)
    (j : Fin (K + 1)) : (wiresFun M pos addr hpos ha j).val =
      if h : j.val < K then addr ⟨j.val, h⟩ else pos := by
  unfold wiresFun; split_ifs <;> rfl

def wiresO (M pos : ℕ) (addr : Fin K → ℕ) (hpos : pos < M) (ha : ∀ j, addr j < pos)
    (hinj : Function.Injective addr) : Fin (K + 1) ↪ Fin M :=
  ⟨wiresFun M pos addr hpos ha, by
    intro i j hij
    have h := congrArg Fin.val hij
    rw [wiresFun_val, wiresFun_val] at h
    split_ifs at h with h1 h2 h2
    · have := hinj h
      simp only [Fin.mk.injEq] at this
      exact Fin.ext this
    · have := ha ⟨i.val, h1⟩; omega
    · have := ha ⟨j.val, h2⟩; omega
    · apply Fin.ext; omega⟩

theorem wiresO_last (M pos : ℕ) (addr : Fin K → ℕ) (hpos : pos < M) (ha : ∀ j, addr j < pos)
    (hinj : Function.Injective addr) :
    (wiresO M pos addr hpos ha hinj (Fin.last K)).val = pos :=
  wiresFun_last M pos addr hpos ha

theorem wiresO_cast (M pos : ℕ) (addr : Fin K → ℕ) (hpos : pos < M) (ha : ∀ j, addr j < pos)
    (hinj : Function.Injective addr) (j : Fin K) :
    (wiresO M pos addr hpos ha hinj j.castSucc).val = addr j :=
  wiresFun_cast M pos addr hpos ha j

theorem classical_oracle_mulVec (O : (Fin K → Bool) → Bool)
    (Mo : Matrix (Qubits (K + 1)) (Qubits (K + 1)) ℂ) (hMo : IsClassicalOracle O Mo) {M : ℕ}
    (W : Fin (K + 1) ↪ Fin M) (z : Qubits M) :
    (embedOp Mo W).mulVec (bv z) =
      bv (Function.update z (W (Fin.last K))
        (xor (z (W (Fin.last K))) (O (fun j => z (W j.castSucc))))) := by
  rw [embedOp_mulVec_bv]
  set u0 : Qubits (K + 1) := Fin.snoc (α := fun _ => Bool) (Fin.init (z ∘ W))
    (xor ((z ∘ W) (Fin.last _)) (O (Fin.init (z ∘ W)))) with hu0
  rw [Finset.sum_eq_single u0]
  · rw [hMo, if_pos rfl, one_smul]
    congr 1
    symm
    rw [eq_setPart_iff]
    constructor
    · funext j
      simp only [Function.comp_apply]
      by_cases hj : j = Fin.last K
      · subst hj
        rw [Function.update_self, hu0, Fin.snoc_last]
        rfl
      · have hne : W j ≠ W (Fin.last K) := fun h => hj (W.injective h)
        rw [Function.update_of_ne hne]
        obtain ⟨j', rfl⟩ : ∃ j' : Fin K, j = j'.castSucc :=
          ⟨j.castPred hj, (Fin.castSucc_castPred j hj).symm⟩
        rw [hu0, Fin.snoc_castSucc]
        rfl
    · intro v hv
      have hne : v ≠ W (Fin.last K) := fun h => hv ⟨_, h.symm⟩
      rw [Function.update_of_ne hne]
  · intro u _ hu
    rw [hMo, if_neg hu, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

variable {a : ℕ}

/-- Circuit of one oracle-program instruction writing variable `pos`. -/
noncomputable def instrCircO (M : ℕ) (g : OIns K) (pos : ℕ) :
    OracleCircuit G12 (fun _ : Fin 1 => K + 1) M :=
  match g with
  | .bin g => instrCirc M g pos
  | .orc addr =>
    if h : pos < M ∧ (∀ j, addr j < pos) ∧ Function.Injective addr then
      [OracleStep.query 0 false none (wiresO M pos addr h.1 h.2.1 h.2.2) (by simp)]
    else []

def stepFO (M : ℕ) (O : (Fin K → Bool) → Bool) (g : OIns K) (pos : ℕ) (z : Qubits M) : Qubits M :=
  match g with
  | .bin g => stepF M g pos z
  | .orc addr =>
    if h : pos < M ∧ (∀ j, addr j < pos) ∧ Function.Injective addr then
      Function.update z ⟨pos, h.1⟩ (xor (z ⟨pos, h.1⟩)
        (O (fun j => z ⟨addr j, by have := h.2.1 j; omega⟩)))
    else z

theorem impl_instrO (M : ℕ) (O : (Fin K → Bool) → Bool)
    (Mo : Matrix (Qubits (K + 1)) (Qubits (K + 1)) ℂ) (hMo : IsClassicalOracle O Mo)
    (g : OIns K) (pos : ℕ) : ImplAt (instrCircO M g pos) Mo (stepFO M O g pos) := by
  cases g with
  | bin g => exact ImplAt.of_impl (impl_instr M g pos) Mo
  | orc addr =>
    by_cases h : pos < M ∧ (∀ j, addr j < pos) ∧ Function.Injective addr
    · intro z
      simp only [instrCircO, stepFO, dif_pos h]
      rw [single_unitary]
      simp only [OracleStep.mat, Bool.false_eq_true, if_false]
      rw [classical_oracle_mulVec O Mo hMo]
      congr 2
      · exact Fin.ext (wiresO_last M pos addr h.1 h.2.1 h.2.2)
      · congr 1
        · exact congrArg z (Fin.ext (wiresO_last M pos addr h.1 h.2.1 h.2.2))
        · congr 1; funext j
          exact congrArg z (Fin.ext (wiresO_cast M pos addr h.1 h.2.1 h.2.2 j))
    · intro z
      simp only [instrCircO, stepFO, dif_neg h]
      rw [unitary_nil, Matrix.one_mulVec]

theorem stepFO_invol (M : ℕ) (O : (Fin K → Bool) → Bool) (g : OIns K) (pos : ℕ) (z : Qubits M) :
    stepFO M O g pos (stepFO M O g pos z) = z := by
  cases g with
  | bin g => exact stepF_invol M g pos z
  | orc addr =>
    simp only [stepFO]
    by_cases h : pos < M ∧ (∀ j, addr j < pos) ∧ Function.Injective addr
    · rw [dif_pos h, dif_pos h]
      have hfn : (fun j => Function.update z ⟨pos, h.1⟩ (xor (z ⟨pos, h.1⟩)
          (O (fun j => z ⟨addr j, by have := h.2.1 j; omega⟩))) ⟨addr j, by have := h.2.1 j; omega⟩)
          = fun j => z ⟨addr j, by have := h.2.1 j; omega⟩ := by
        funext j
        rw [Function.update_of_ne]
        intro e; simp at e; have := h.2.1 j; omega
      rw [hfn, Function.update_self, Function.update_idem, Bool.xor_assoc, Bool.xor_self,
        Bool.xor_false, Function.update_eq_self]
    · rw [dif_neg h, dif_neg h]

noncomputable def compileO (M : ℕ) : List (OIns K) → ℕ → OracleCircuit G12 (fun _ : Fin 1 => K + 1) M
  | [], _ => []
  | g :: gs, pos => instrCircO M g pos ++ compileO M gs (pos + 1)

/-- The same blocks in reverse order (the inverse classical map). -/
noncomputable def compileRevO (M : ℕ) :
    List (OIns K) → ℕ → OracleCircuit G12 (fun _ : Fin 1 => K + 1) M
  | [], _ => []
  | g :: gs, pos => compileRevO M gs (pos + 1) ++ instrCircO M g pos

def runPO (M : ℕ) (O : (Fin K → Bool) → Bool) : List (OIns K) → ℕ → Qubits M → Qubits M
  | [], _ => id
  | g :: gs, pos => runPO M O gs (pos + 1) ∘ stepFO M O g pos

def runRevO (M : ℕ) (O : (Fin K → Bool) → Bool) : List (OIns K) → ℕ → Qubits M → Qubits M
  | [], _ => id
  | g :: gs, pos => stepFO M O g pos ∘ runRevO M O gs (pos + 1)

theorem impl_compileO (M : ℕ) (O : (Fin K → Bool) → Bool)
    (Mo : Matrix (Qubits (K + 1)) (Qubits (K + 1)) ℂ) (hMo : IsClassicalOracle O Mo)
    (P : List (OIns K)) (pos : ℕ) : ImplAt (compileO M P pos) Mo (runPO M O P pos) := by
  induction P generalizing pos with
  | nil =>
    intro z
    show (OracleCircuit.unitary [] _).mulVec _ = _
    rw [unitary_nil, Matrix.one_mulVec]; rfl
  | cons g gs ih => exact (impl_instrO M O Mo hMo g pos).append (ih (pos + 1))

theorem impl_compileRevO (M : ℕ) (O : (Fin K → Bool) → Bool)
    (Mo : Matrix (Qubits (K + 1)) (Qubits (K + 1)) ℂ) (hMo : IsClassicalOracle O Mo)
    (P : List (OIns K)) (pos : ℕ) : ImplAt (compileRevO M P pos) Mo (runRevO M O P pos) := by
  induction P generalizing pos with
  | nil =>
    intro z
    show (OracleCircuit.unitary [] _).mulVec _ = _
    rw [unitary_nil, Matrix.one_mulVec]; rfl
  | cons g gs ih => exact (ih (pos + 1)).append (impl_instrO M O Mo hMo g pos)

theorem runRevO_runPO (M : ℕ) (O : (Fin K → Bool) → Bool) (P : List (OIns K)) :
    ∀ pos z, runRevO M O P pos (runPO M O P pos z) = z := by
  induction P with
  | nil => intro pos z; rfl
  | cons g gs ih =>
    intro pos z
    simp only [runRevO, runPO, Function.comp_apply]
    rw [ih, stepFO_invol]

theorem run_correctO (M : ℕ) (O : (Fin K → Bool) → Bool) (P : List (OIns K)) :
    ∀ (pos : ℕ) (z : Qubits M), pos + P.length ≤ M → (∀ v : Fin M, pos ≤ v.val → z v = false) →
      toN (runPO M O P pos z) = fun v => if v < M then svalO O pos P (toN z) v else false := by
  induction P with
  | nil =>
    intro pos z _ hz
    funext v
    simp only [runPO, id]
    split_ifs with hv
    · rw [svalO]
      by_cases h1 : v < pos
      · rw [if_pos h1]
      · rw [if_neg h1, dif_neg (by simp)]
        have := hz ⟨v, hv⟩ (by show pos ≤ v; omega)
        simp only [toN, dif_pos hv]; exact this
    · simp [toN, hv]
  | cons g gs ih =>
    intro pos z hlen hz
    simp only [runPO, Function.comp_apply]
    have hpos : pos < M := by simp at hlen; omega
    have hzp : z ⟨pos, hpos⟩ = false := hz _ le_rfl
    have hz' : ∀ v : Fin M, pos + 1 ≤ v.val → stepFO M O g pos z v = false := by
      intro v hv
      cases g with
      | bin g =>
        try simp only [stepFO]
        unfold stepF
        split_ifs with h
        · rw [Function.update_of_ne]; · exact hz v (by omega)
          intro e; rw [e] at hv; simp at hv
        · exact hz v (by omega)
      | orc addr =>
        try simp only [stepFO]
        split_ifs with h
        · rw [Function.update_of_ne]; · exact hz v (by omega)
          intro e; rw [e] at hv; simp at hv
        · exact hz v (by omega)
    rw [ih (pos + 1) _ (by simp at hlen; omega) hz']
    funext v
    split_ifs with hv
    · rw [svalO_cons]
      congr 1
      funext x
      by_cases hx : x = pos
      · subst hx
        rw [Function.update_self]
        simp only [toN, dif_pos hpos]
        cases g with
        | bin g =>
          simp only [stepFO, firstVal]
          unfold stepF
          by_cases h : x < M ∧ g.a < x ∧ g.b < x
          · rw [dif_pos h, if_pos ⟨h.2.1, h.2.2⟩, Function.update_self, hzp, Bool.false_xor]
            first | rfl | simp [toN, show g.a < M by omega, show g.b < M by omega]
          · have h' : ¬ (g.a < x ∧ g.b < x) := fun h' => h ⟨hpos, h'⟩
            rw [dif_neg h, if_neg h', hzp]
        | orc addr =>
          simp only [stepFO, firstVal]
          by_cases h : x < M ∧ (∀ j, addr j < x) ∧ Function.Injective addr
          · rw [dif_pos h, if_pos ⟨h.2.1, h.2.2⟩, Function.update_self, hzp, Bool.false_xor]
            congr 1; funext j
            first | rfl | simp [toN, show addr j < M by have := h.2.1 j; omega]
          · have h' : ¬ ((∀ j, addr j < x) ∧ Function.Injective addr) := fun h' => h ⟨hpos, h'⟩
            rw [dif_neg h, if_neg h', hzp]
      · rw [Function.update_of_ne hx]
        simp only [toN]
        split_ifs with hxM
        · cases g with
          | bin g =>
            try simp only [stepFO]
            unfold stepF
            split_ifs with h
            · rw [Function.update_of_ne]; intro e; simp at e; exact hx e
            · rfl
          | orc addr =>
            try simp only [stepFO]
            split_ifs with h
            · rw [Function.update_of_ne]; intro e; simp at e; exact hx e
            · rfl
        · rfl
    · rfl

theorem compile_semO (M B : ℕ) (O : (Fin K → Bool) → Bool) (P : List (OIns K))
    (hM : B + P.length ≤ M) (z : Qubits M)
    (hz : ∀ v : Fin M, B ≤ v.val → z v = false) (v : Fin M) :
    runPO M O P B z v = svalO O B P (toN z) v := by
  have := congrFun (run_correctO M O P B z hM hz) v
  simp only [toN, v.isLt, dif_pos, if_true] at this
  simpa using this

/-! Counts. -/

def isOrc : OIns K → Bool
  | .bin _ => false
  | .orc _ => true

theorem counts_instrO (M : ℕ) (g : OIns K) (pos : ℕ) :
    QuantumLTF.Membership.Uncontrolled (instrCircO M g pos) ∧
    (instrCircO M g pos).gateCount ≤ 10 ∧
    (instrCircO M g pos).queryCount 0 ≤ (isOrc g).toNat := by
  cases g with
  | bin g =>
    have hall := allGates_instr (ar := fun _ : Fin 1 => K + 1) M g pos
    refine ⟨hall.uncontrolled, ?_, ?_⟩
    · simp only [instrCircO]; rw [hall.gateCount]; exact length_instr M g pos
    · simp only [instrCircO]; rw [hall.queryCount]; simp
  | orc addr =>
    simp only [instrCircO, isOrc]
    split_ifs with h
    · refine ⟨?_, ?_, ?_⟩
      · intro st hst; simp at hst; subst hst; rfl
      · simp [OracleCircuit.gateCount]
      · simp [OracleCircuit.queryCount, OracleStep.IsQueryTo]
    · refine ⟨fun st hst => by simp at hst, by simp [OracleCircuit.gateCount],
        by simp [OracleCircuit.queryCount]⟩

def orcCount : List (OIns K) → ℕ
  | [] => 0
  | g :: gs => (isOrc g).toNat + orcCount gs

theorem counts_compileO (M : ℕ) (P : List (OIns K)) (pos : ℕ) :
    QuantumLTF.Membership.Uncontrolled (compileO M P pos) ∧
    (compileO M P pos).gateCount ≤ 10 * P.length ∧
    (compileO M P pos).queryCount 0 ≤ orcCount P ∧
    QuantumLTF.Membership.Uncontrolled (compileRevO M P pos) ∧
    (compileRevO M P pos).gateCount ≤ 10 * P.length ∧
    (compileRevO M P pos).queryCount 0 ≤ orcCount P := by
  induction P generalizing pos with
  | nil =>
    simp only [compileO, compileRevO]
    exact ⟨fun st hst => by simp at hst, by simp [OracleCircuit.gateCount],
      by simp [OracleCircuit.queryCount], fun st hst => by simp at hst,
      by simp [OracleCircuit.gateCount], by simp [OracleCircuit.queryCount]⟩
  | cons g gs ih =>
    obtain ⟨u1, g1, q1, u2, g2, q2⟩ := ih (pos + 1)
    obtain ⟨u0, g0, q0⟩ := counts_instrO M g pos
    simp only [compileO, compileRevO, orcCount, List.length_cons]
    refine ⟨uncontrolled_append u0 u1, ?_, ?_, uncontrolled_append u2 u0, ?_, ?_⟩
    · rw [gateCount_append]; omega
    · rw [queryCount_append]; omega
    · rw [gateCount_append]; omega
    · rw [queryCount_append]; omega

end CompO

end LTFC

-- ===== module BuildO =====

/-! Builders for oracle programs: emission, blocks, ripple adder, modular add/sub. -/

open QAlgorithms

namespace LTFC

/-- Binary value of a Boolean list, least significant first. -/
def bval : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bval bs

theorem numVal_eq_bval (σ : ℕ → Bool) (l : List ℕ) : numVal σ l = bval (l.map σ) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [numVal, bval, ih]

theorem bval_lt (l : List Bool) : bval l < 2 ^ l.length := by
  induction l with
  | nil => simp [bval]
  | cons b bs ih => simp only [bval, List.length_cons, pow_succ]; cases b <;> simp <;> omega

theorem bval_append (l₁ l₂ : List Bool) : bval (l₁ ++ l₂) = bval l₁ + 2 ^ l₁.length * bval l₂ := by
  induction l₁ with
  | nil => simp [bval]
  | cons b bs ih => simp only [List.cons_append, bval, ih, List.length_cons, pow_succ]; ring

theorem bval_replicate_false (k : ℕ) : bval (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, bval, ih]

theorem natmod_modEq (N L : ℕ) : (((N % 2 ^ L : ℕ)) : ℤ) ≡ (N : ℤ) [ZMOD 2 ^ L] := by
  have := Int.mod_modEq (N : ℤ) (2 ^ L)
  simpa [Int.natCast_mod] using this

theorem mod_two_mul (b x N : ℕ) (hb : b < 2) (hN : 0 < N) :
    (b + 2 * x) % (N * 2) = b + 2 * (x % N) := by
  conv_lhs => rw [← Nat.mod_add_div x N]
  rw [show b + 2 * (x % N + N * (x / N)) = (b + 2 * (x % N)) + (N * 2) * (x / N) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by have := Nat.mod_lt x hN; omega)]

theorem bval_take (l : List Bool) : ∀ L, bval (l.take L) = bval l % 2 ^ L := by
  induction l with
  | nil => intro L; simp [bval]
  | cons b bs ih =>
    intro L
    cases L with
    | zero => simp [bval, Nat.mod_one]
    | succ L =>
      simp only [List.take_succ_cons, bval, ih, pow_succ]
      rw [mod_two_mul _ _ _ (by cases b <;> simp) (by positivity)]

theorem bval_not (l : List Bool) : bval (l.map (fun x => !x)) + bval l = 2 ^ l.length - 1 := by
  induction l with
  | nil => simp [bval]
  | cons b bs ih =>
    simp only [List.map_cons, bval, List.length_cons, pow_succ]
    have := bval_lt bs
    cases b <;> simp <;> omega

/-- Constant list (of the wires `zero`, `one`) for the value `c mod 2^L`. -/
def constL (zero one : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | L + 1, c => (if c % 2 = 1 then one else zero) :: constL zero one L (c / 2)

theorem constL_length (zero one L c : ℕ) : (constL zero one L c).length = L := by
  induction L generalizing c with
  | zero => rfl
  | succ L ih => simp [constL, ih]

theorem constL_val (σ : ℕ → Bool) (zero one : ℕ) (h0 : σ zero = false) (h1 : σ one = true) :
    ∀ L c, bval ((constL zero one L c).map σ) = c % 2 ^ L := by
  intro L
  induction L with
  | zero => intro c; simp [constL, bval, Nat.mod_one]
  | succ L ih =>
    intro c
    simp only [constL, List.map_cons, bval, ih, pow_succ]
    conv_rhs => rw [← Nat.mod_add_div c 2]
    rw [mod_two_mul _ _ _ (Nat.mod_lt _ (by norm_num)) (by positivity)]
    congr 1
    split_ifs with h
    · simp [h1, h]
    · have : c % 2 = 0 := by omega
      simp [h0, this]

theorem constL_mem (zero one L c v : ℕ) (hv : v ∈ constL zero one L c) : v = zero ∨ v = one := by
  induction L generalizing c with
  | zero => simp [constL] at hv
  | succ L ih =>
    simp only [constL, List.mem_cons] at hv
    rcases hv with h | h
    · split_ifs at h <;> simp [h]
    · exact ih _ h

section BuildO

variable {K : ℕ} (O : (Fin K → Bool) → Bool) (B : ℕ)

abbrev BldO (K : ℕ) (α : Type) := List (OIns K) → α × List (OIns K)

def emitO (f : Bool → Bool → Bool) (a b : ℕ) : BldO K ℕ :=
  fun p => (B + p.length, p ++ [.bin ⟨f, a, b⟩])

theorem emitO_spec (f : Bool → Bool → Bool) (a b : ℕ) (p : List (OIns K))
    (ha : a < B + p.length) (hb : b < B + p.length) :
    ExtL p (emitO B f a b p).2 ∧ (emitO B f a b p).2.length = p.length + 1 ∧
    (emitO B f a b p).1 < B + (emitO B f a b p).2.length ∧
    HoldsO O B (emitO B f a b p).2 (fun σ => σ (emitO B f a b p).1 = f (σ a) (σ b)) := by
  refine ⟨ExtL.app _ _, by simp [emitO], by simp [emitO], ?_⟩
  have := holdsO_list O B p [⟨f, a, b⟩] (by intro i hi; simp at hi; subst hi; simp; omega)
  refine this.imp ?_
  intro σ h
  have := h 0 (by simp)
  simpa [emitO] using this

/-- Emit `f x b` for every `x` of the list. -/
def mapE (f : Bool → Bool → Bool) (X : List ℕ) (b : ℕ) : BldO K (List ℕ) :=
  fun p => ((List.range X.length).map (fun i => B + p.length + i),
    p ++ (X.map (fun x => (⟨f, x, b⟩ : Instr))).map OIns.bin)

theorem mapE_spec (f : Bool → Bool → Bool) (X : List ℕ) (b : ℕ) (p : List (OIns K))
    (hX : ∀ x ∈ X, x < B + p.length) (hb : b < B + p.length) :
    ExtL p (mapE B f X b p).2 ∧ (mapE B f X b p).2.length = p.length + X.length ∧
    (mapE B f X b p).1.length = X.length ∧
    (∀ v ∈ (mapE B f X b p).1, v < B + (mapE B f X b p).2.length) ∧
    HoldsO O B (mapE B f X b p).2
      (fun σ => (mapE B f X b p).1.map σ = X.map (fun x => f (σ x) (σ b))) := by
  refine ⟨ExtL.app _ _, by simp [mapE], by simp [mapE], ?_, ?_⟩
  · intro v hv
    simp only [mapE, List.mem_map, List.mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    simp only [mapE, List.length_append, List.length_map]; omega
  · have := holdsO_list O B p (X.map (fun x => (⟨f, x, b⟩ : Instr))) (by
      intro i hi
      simp only [List.getElem_map]
      simp only [List.length_map] at hi
      have := hX X[i] (List.getElem_mem hi)
      constructor <;> omega)
    refine this.imp ?_
    intro σ h
    apply List.ext_getElem
    · simp [mapE]
    · intro i h1 h2
      have := h i (by simpa [mapE] using h1)
      simpa [mapE] using this

/-- A block of `k` binary instructions with explicit indices. -/
def blockE {k : ℕ} (g : Fin k → Instr) : BldO K Unit :=
  fun p => ((), p ++ (List.ofFn g).map OIns.bin)

theorem blockE_spec {k : ℕ} (g : Fin k → Instr) (p : List (OIns K))
    (hg : ∀ j, (g j).a < B + p.length ∧ (g j).b < B + p.length) :
    ExtL p (blockE g p).2 ∧ (blockE g p).2.length = p.length + k ∧
    HoldsO O B (blockE g p).2 (fun σ => ∀ j : Fin k,
      σ (B + p.length + j) = (g j).f (σ (g j).a) (σ (g j).b)) := by
  refine ⟨ExtL.app _ _, by simp [blockE], ?_⟩
  have := holdsO_list O B p (List.ofFn g) (by
    intro i hi
    simp only [List.getElem_ofFn]
    simp only [List.length_ofFn] at hi
    have := hg ⟨i, hi⟩
    constructor <;> omega)
  refine this.imp ?_
  intro σ h j
  have := h j.val (by simp)
  simpa using this

def orcE (addr : Fin K → ℕ) : BldO K ℕ := fun p => (B + p.length, p ++ [.orc addr])

theorem orcE_spec (addr : Fin K → ℕ) (p : List (OIns K)) (ha : ∀ j, addr j < B + p.length)
    (hinj : Function.Injective addr) :
    ExtL p (orcE B addr p).2 ∧ (orcE B addr p).2.length = p.length + 1 ∧
    (orcE B addr p).1 < B + (orcE B addr p).2.length ∧
    HoldsO O B (orcE B addr p).2 (fun σ => σ (orcE B addr p).1 = O (fun j => σ (addr j))) :=
  ⟨ExtL.app _ _, by simp [orcE], by simp [orcE], holdsO_orc O B p addr ha hinj⟩

/-! Ripple-carry adder (LSB first). -/

def addcO : List ℕ → List ℕ → ℕ → BldO K (List ℕ)
  | x :: xs, y :: ys, c => fun p =>
      let n := B + p.length
      let r := addcO xs ys (n + 4) (p ++ ([⟨xor, x, y⟩, ⟨xor, n, c⟩, ⟨(· && ·), x, y⟩,
        ⟨(· && ·), c, n⟩, ⟨(· || ·), n + 2, n + 3⟩] : List Instr).map OIns.bin)
      ((n + 1) :: r.1, r.2)
  | _, _, c => fun p => ([c], p)

theorem addcO_spec : ∀ (xs ys : List ℕ) (c : ℕ) (p : List (OIns K)), xs.length = ys.length →
    (∀ v ∈ xs, v < B + p.length) → (∀ v ∈ ys, v < B + p.length) → c < B + p.length →
    ExtL p (addcO B xs ys c p).2 ∧ (addcO B xs ys c p).2.length = p.length + 5 * xs.length ∧
    (addcO B xs ys c p).1.length = xs.length + 1 ∧
    (∀ v ∈ (addcO B xs ys c p).1, v < B + (addcO B xs ys c p).2.length) ∧
    HoldsO O B (addcO B xs ys c p).2
      (fun σ => numVal σ (addcO B xs ys c p).1 = numVal σ xs + numVal σ ys + (σ c).toNat) := by
  intro xs
  induction xs with
  | nil =>
    intro ys c p hl _ _ hc
    have : ys = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
    subst this
    refine ⟨ExtL.refl _, by simp [addcO], by simp [addcO], ?_, ?_⟩
    · intro v hv; simp only [addcO, List.mem_singleton] at hv ⊢; omega
    · intro q inp; simp [addcO, numVal]
  | cons x xs ih =>
    intro ys c p hl hx hy hc
    obtain ⟨y, ys, rfl⟩ : ∃ y ys', ys = y :: ys' := by
      cases ys with
      | nil => simp at hl
      | cons y ys' => exact ⟨y, ys', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    set n := B + p.length with hn
    set blk : List Instr := [⟨xor, x, y⟩, ⟨xor, n, c⟩, ⟨(· && ·), x, y⟩,
        ⟨(· && ·), c, n⟩, ⟨(· || ·), n + 2, n + 3⟩] with hblk
    have hxv : x < n := hx x List.mem_cons_self
    have hyv : y < n := hy y List.mem_cons_self
    have hp1 : (p ++ blk.map OIns.bin).length = p.length + 5 := by simp [hblk]
    obtain ⟨e1, l1, o1, v1, h1⟩ := ih ys (n + 4) (p ++ blk.map OIns.bin) hl
      (fun v hv => by have := hx v (List.mem_cons_of_mem _ hv); rw [hp1]; omega)
      (fun v hv => by have := hy v (List.mem_cons_of_mem _ hv); rw [hp1]; omega)
      (by rw [hp1]; omega)
    have hb := holdsO_list O B p blk (by
      intro i hi
      simp only [hblk, List.length_cons, List.length_nil] at hi
      interval_cases i <;> simp [hblk] <;> omega)
    have hext : ExtL p (addcO B xs ys (n + 4) (p ++ blk.map OIns.bin)).2 :=
      (ExtL.app p _).trans e1
    change ExtL p (addcO B xs ys (n + 4) (p ++ blk.map OIns.bin)).2 ∧
      (addcO B xs ys (n + 4) (p ++ blk.map OIns.bin)).2.length = p.length + 5 * (xs.length + 1) ∧
      ((n + 1) :: (addcO B xs ys (n + 4) (p ++ blk.map OIns.bin)).1).length = xs.length + 1 + 1 ∧
      (∀ v ∈ (n + 1) :: (addcO B xs ys (n + 4) (p ++ blk.map OIns.bin)).1,
        v < B + (addcO B xs ys (n + 4) (p ++ blk.map OIns.bin)).2.length) ∧
      HoldsO O B (addcO B xs ys (n + 4) (p ++ blk.map OIns.bin)).2 (fun σ =>
        numVal σ ((n + 1) :: (addcO B xs ys (n + 4) (p ++ blk.map OIns.bin)).1) =
          numVal σ (x :: xs) + numVal σ (y :: ys) + (σ c).toNat)
    refine ⟨hext, by rw [l1, hp1]; ring, by simp [o1], ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.1 hv with h | h
      · rw [h, l1, hp1]; omega
      · exact v1 v h
    · refine ((hb.mono e1).and h1).imp ?_
      rintro σ ⟨hb, h1⟩
      have q0 := hb 0 (by simp [hblk])
      have q1 := hb 1 (by simp [hblk])
      have q2 := hb 2 (by simp [hblk])
      have q3 := hb 3 (by simp [hblk])
      have q4 := hb 4 (by simp [hblk])
      simp only [hblk, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at q0 q1 q2 q3 q4
      rw [← hn] at q0 q1 q2 q3 q4
      simp only [numVal]
      rw [h1]
      have fa := full_adder (σ x) (σ y) (σ c)
      rw [← q0] at fa
      rw [q1, q4, q2, q3]
      omega

/-! Modular addition / subtraction: `A ± X mod 2^L`. -/

def csub (A X : List ℕ) (neg : ℕ) : BldO K (List ℕ) := fun p =>
  let r1 := mapE B xor X neg p
  let r2 := addcO B A r1.1 neg r1.2
  (r2.1.take A.length, r2.2)

theorem csub_spec (A X : List ℕ) (neg : ℕ) (p : List (OIns K)) (hl : A.length = X.length)
    (hA : ∀ v ∈ A, v < B + p.length) (hX : ∀ v ∈ X, v < B + p.length)
    (hneg : neg < B + p.length) :
    ExtL p (csub B A X neg p).2 ∧ (csub B A X neg p).2.length = p.length + 6 * A.length ∧
    (csub B A X neg p).1.length = A.length ∧
    (∀ v ∈ (csub B A X neg p).1, v < B + (csub B A X neg p).2.length) ∧
    HoldsO O B (csub B A X neg p).2 (fun σ =>
      ((numVal σ (csub B A X neg p).1 : ℕ) : ℤ) ≡
        (numVal σ A : ℤ) + (if σ neg then -(numVal σ X : ℤ) else (numVal σ X : ℤ))
          [ZMOD 2 ^ A.length]) := by
  obtain ⟨e1, l1, o1, v1, h1⟩ := mapE_spec O B xor X neg p hX hneg
  set r1 := mapE B xor X neg p with hr1
  obtain ⟨e2, l2, o2, v2, h2⟩ := addcO_spec O B A r1.1 neg r1.2 (by rw [o1, hl])
    (fun v hv => by have := hA v hv; have := e1.length_le; omega) v1
    (by have := e1.length_le; omega)
  set r2 := addcO B A r1.1 neg r1.2 with hr2
  refine ⟨e1.trans e2, ?_, ?_, ?_, ?_⟩
  · show r2.2.length = _
    rw [l2, l1, hl]; ring
  · show (r2.1.take A.length).length = _
    simp [o2]
  · intro v hv
    exact v2 v (List.mem_of_mem_take hv)
  · refine ((h1.mono e2).and h2).imp ?_
    rintro σ ⟨h1, h2⟩
    show ((numVal σ (r2.1.take A.length) : ℕ) : ℤ) ≡ _ [ZMOD _]
    have ht : numVal σ (r2.1.take A.length) = numVal σ r2.1 % 2 ^ A.length := by
      rw [numVal_eq_bval, numVal_eq_bval, List.map_take, bval_take]
    rw [ht, h2]
    have hY : numVal σ r1.1 = if σ neg then 2 ^ A.length - 1 - numVal σ X else numVal σ X := by
      rw [numVal_eq_bval, h1, numVal_eq_bval]
      have hlen : (X.map σ).length = A.length := by simp [hl]
      split_ifs with hn
      · have := bval_not (X.map σ)
        simp only [List.map_map, hlen] at this
        have e : (X.map fun x => xor (σ x) (σ neg)) = ((X.map σ).map fun x => !x) := by
          simp [hn, Function.comp_def]
        rw [e]; simp only [List.map_map] at this ⊢; omega
      · have e : (X.map fun x => xor (σ x) (σ neg)) = X.map σ := by
          simp [hn]
        rw [e]
    have hXlt : numVal σ X < 2 ^ A.length := by
      rw [numVal_eq_bval]; have := bval_lt (X.map σ); simpa [hl] using this
    rw [hY]
    split_ifs with hn
    · simp only [hn, Bool.toNat_true]
      have e : (numVal σ A + (2 ^ A.length - 1 - numVal σ X) + 1) =
          numVal σ A + 2 ^ A.length - numVal σ X := by omega
      rw [e]
      refine (natmod_modEq _ _).trans ?_
      push_cast [Nat.cast_sub (show numVal σ X ≤ numVal σ A + 2 ^ A.length by omega)]
      unfold Int.ModEq
      rw [show (numVal σ A : ℤ) + 2 ^ A.length - numVal σ X =
        ((numVal σ A : ℤ) + -(numVal σ X : ℤ)) + 2 ^ A.length * 1 by ring,
        Int.add_mul_emod_self_left]
    · simp only [hn, Bool.false_eq_true, Bool.toNat_false, add_zero]
      refine (natmod_modEq _ _).trans ?_
      push_cast
      rfl

end BuildO

end LTFC

-- ===== module OffA =====

/-! Fixed-point address arithmetic for the coherent offset estimation. -/

open QAlgorithms

namespace LTFC

theorem msb_snoc (x : Bool) : ∀ (l : List Bool) (acc : ℕ),
    msb acc (l ++ [x]) = 2 * msb acc l + x.toNat := by
  intro l
  induction l with
  | nil => intro acc; simp [msb]
  | cons y ys ihy => intro acc; simp only [List.cons_append, msb]; exact ihy _

theorem msb_eq_bval_reverse (l : List Bool) : msb 0 l = bval l.reverse := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
    simp only [bval]
    rw [msb_snoc, ih]; ring

theorem bval_rev_bits {L : ℕ} (b : Fin L → Bool) :
    bval ((List.range L).map (fun i => if h : L - 1 - i < L then b ⟨L - 1 - i, h⟩ else false)) =
      bitsToNat b := by
  rw [← msb_ofFn, msb_eq_bval_reverse]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.getElem_ofFn,
      List.length_ofFn]
    rw [dif_pos (by omega)]

section Off

variable (n ℓ₁ ℓ : ℕ)

/-- Variables of coordinate `k` of the `p` register, least significant first. -/
def NL (k : ℕ) : List ℕ := (List.range ℓ₁).map (fun i => (ℓ₁ - 1 - i) + ℓ₁ * k)

theorem NL_length (k : ℕ) : (NL ℓ₁ k).length = ℓ₁ := by simp [NL]

theorem NL_lt (k : ℕ) (hk : k < n) : ∀ v ∈ NL ℓ₁ k, v < n * ℓ₁ := by
  intro v hv
  simp only [NL, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have : (k + 1) * ℓ₁ ≤ n * ℓ₁ := Nat.mul_le_mul_right ℓ₁ hk
  rw [Nat.add_mul, one_mul] at this
  rw [mul_comm ℓ₁ k]; omega

/-- The register value `p` as a bit string of the inputs. -/
def pBits (σ : ℕ → Bool) : Qubits (n * ℓ₁) := fun idx => σ idx.val

theorem numVal_NL (σ : ℕ → Bool) (k : Fin n) :
    numVal σ (NL ℓ₁ k) = bitsToNat (QuantumLTF.Membership.splitReg n ℓ₁ (pBits n ℓ₁ σ) k) := by
  rw [numVal_eq_bval, ← bval_rev_bits]
  congr 1
  simp only [NL, List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp_apply, dif_pos (show ℓ₁ - 1 - i < ℓ₁ by omega),
    QuantumLTF.Membership.splitReg, pBits, finProdFinEquiv_apply_val]

/-- Shifted copy of `N_k`: value `2^e N_k mod 2^ℓ`. -/
def shl (zw k e : ℕ) : List ℕ :=
  ((List.replicate e zw) ++ NL ℓ₁ k ++ List.replicate ℓ zw).take ℓ

theorem shl_length (zw k e : ℕ) : (shl ℓ₁ ℓ zw k e).length = ℓ := by
  simp [shl]; omega

theorem shl_val (σ : ℕ → Bool) (zw k e : ℕ) (hz : σ zw = false) :
    numVal σ (shl ℓ₁ ℓ zw k e) = (2 ^ e * numVal σ (NL ℓ₁ k)) % 2 ^ ℓ := by
  rw [numVal_eq_bval, shl, List.map_take, bval_take, List.map_append, List.map_append,
    bval_append, bval_append]
  simp [List.map_replicate, hz, bval_replicate_false, numVal_eq_bval]

end Off

/-! ### Builders over the oracle program -/

section OffB

variable {K : ℕ} (O : (Fin K → Bool) → Bool) (B ℓ₁ ℓ : ℕ)

/-- `A ± 2^e P_k mod 2^ℓ`, where `P_k = 2 N_k - 2^ℓ₁`; sign `-` iff `negv`; `negb = ¬negv`. -/
def addScaled (zw ow : ℕ) (A : List ℕ) (k e negv negb : ℕ) : BldO K (List ℕ) := fun p =>
  let r1 := csub B A (shl ℓ₁ ℓ zw k (e + 1)) negv p
  csub B r1.1 (constL zw ow ℓ (2 ^ (e + ℓ₁))) negb r1.2

def Pk (σ : ℕ → Bool) (k : ℕ) : ℤ := 2 * (numVal σ (NL ℓ₁ k) : ℤ) - 2 ^ ℓ₁

def sgnB (b : Bool) : ℤ := if b then -1 else 1

theorem addScaled_spec (zw ow : ℕ) (A : List ℕ) (k e negv negb : ℕ) (p : List (OIns K))
    (hA : A.length = ℓ) (hAv : ∀ v ∈ A, v < B + p.length) (hNL : ∀ v ∈ NL ℓ₁ k, v < B + p.length)
    (hzw : zw < B + p.length) (how : ow < B + p.length) (hnv : negv < B + p.length)
    (hnb : negb < B + p.length) :
    ExtL p (addScaled B ℓ₁ ℓ zw ow A k e negv negb p).2 ∧
    (addScaled B ℓ₁ ℓ zw ow A k e negv negb p).2.length = p.length + 12 * ℓ ∧
    (addScaled B ℓ₁ ℓ zw ow A k e negv negb p).1.length = ℓ ∧
    (∀ v ∈ (addScaled B ℓ₁ ℓ zw ow A k e negv negb p).1,
      v < B + (addScaled B ℓ₁ ℓ zw ow A k e negv negb p).2.length) ∧
    HoldsO O B (addScaled B ℓ₁ ℓ zw ow A k e negv negb p).2 (fun σ =>
      σ zw = false → σ ow = true → σ negb = !σ negv →
      ((numVal σ (addScaled B ℓ₁ ℓ zw ow A k e negv negb p).1 : ℕ) : ℤ) ≡
        (numVal σ A : ℤ) + sgnB (σ negv) * 2 ^ e * Pk ℓ₁ σ k [ZMOD 2 ^ ℓ]) := by
  have hshv : ∀ v ∈ shl ℓ₁ ℓ zw k (e + 1), v < B + p.length := by
    intro v hv
    have := List.mem_of_mem_take hv
    simp only [List.mem_append, List.mem_replicate] at this
    rcases this with (⟨_, rfl⟩ | h) | ⟨_, rfl⟩
    · exact hzw
    · exact hNL v h
    · exact hzw
  obtain ⟨e1, l1, o1, v1, h1⟩ := csub_spec O B A (shl ℓ₁ ℓ zw k (e + 1)) negv p
    (by rw [hA, shl_length]) hAv hshv hnv
  set r1 := csub B A (shl ℓ₁ ℓ zw k (e + 1)) negv p with hr1
  have hle := e1.length_le
  obtain ⟨e2, l2, o2, v2, h2⟩ := csub_spec O B r1.1 (constL zw ow ℓ (2 ^ (e + ℓ₁))) negb r1.2
    (by rw [o1, hA, constL_length]) v1
    (fun v hv => by rcases constL_mem _ _ _ _ v hv with h | h <;> omega) (by omega)
  refine ⟨e1.trans e2, ?_, ?_, v2, ?_⟩
  · show (csub B r1.1 _ negb r1.2).2.length = _
    rw [l2, l1, o1, hA]; ring
  · show (csub B r1.1 _ negb r1.2).1.length = _
    rw [o2, o1, hA]
  · refine ((h1.mono e2).and h2).imp ?_
    rintro σ ⟨h1, h2⟩ hz ho hnb'
    show ((numVal σ (csub B r1.1 _ negb r1.2).1 : ℕ) : ℤ) ≡ _ [ZMOD _]
    rw [o1, hA] at h2
    rw [hA] at h1
    refine h2.trans ?_
    have hc : (numVal σ (constL zw ow ℓ (2 ^ (e + ℓ₁))) : ℤ) ≡ 2 ^ (e + ℓ₁) [ZMOD 2 ^ ℓ] := by
      rw [numVal_eq_bval, constL_val σ zw ow hz ho]
      have := natmod_modEq (2 ^ (e + ℓ₁)) ℓ
      simpa using this
    have hs : (numVal σ (shl ℓ₁ ℓ zw k (e + 1)) : ℤ) ≡ 2 ^ (e + 1) * numVal σ (NL ℓ₁ k)
        [ZMOD 2 ^ ℓ] := by
      rw [shl_val ℓ₁ ℓ σ zw k (e + 1) hz]
      have := natmod_modEq (2 ^ (e + 1) * numVal σ (NL ℓ₁ k)) ℓ
      simpa using this
    have key : (numVal σ A : ℤ) + sgnB (σ negv) * 2 ^ e * Pk ℓ₁ σ k =
        ((numVal σ A : ℤ) + sgnB (σ negv) * (2 ^ (e + 1) * numVal σ (NL ℓ₁ k))) +
          (-sgnB (σ negv)) * 2 ^ (e + ℓ₁) := by
      simp only [Pk, pow_add]; ring
    rw [key, hnb']
    cases hnv' : σ negv
    · simp only [hnv', sgnB, Bool.not_false, if_true, Bool.false_eq_true, if_false] at h1 ⊢
      refine Int.ModEq.add ?_ ?_
      · refine h1.trans ?_
        exact Int.ModEq.add_left _ (by simpa using hs)
      · have := hc.neg; simpa using this
    · simp only [hnv', sgnB, Bool.not_true, if_true, Bool.false_eq_true, if_false] at h1 ⊢
      refine Int.ModEq.add ?_ ?_
      · refine h1.trans ?_
        have := hs.neg
        simpa using Int.ModEq.add_left _ this
      · simpa using hc

/-- Apply `addScaled` to every coordinate `k₀, k₀+1, …`. -/
def addAllL (zw ow : ℕ) (e negv negb : ℕ) : ℕ → List (List ℕ) → BldO K (List (List ℕ))
  | _, [] => fun p => ([], p)
  | k, A :: As => fun p =>
      let r1 := addScaled B ℓ₁ ℓ zw ow A k e negv negb p
      let r2 := addAllL zw ow e negv negb (k + 1) As r1.2
      (r1.1 :: r2.1, r2.2)

theorem addAllL_spec (n : ℕ) (zw ow e negv negb : ℕ) :
    ∀ (As : List (List ℕ)) (k : ℕ) (p : List (OIns K)), k + As.length ≤ n →
    n * ℓ₁ ≤ B →
    (∀ A ∈ As, A.length = ℓ ∧ ∀ v ∈ A, v < B + p.length) →
    zw < B + p.length → ow < B + p.length → negv < B + p.length → negb < B + p.length →
    ExtL p (addAllL B ℓ₁ ℓ zw ow e negv negb k As p).2 ∧
    (addAllL B ℓ₁ ℓ zw ow e negv negb k As p).2.length = p.length + As.length * (12 * ℓ) ∧
    (addAllL B ℓ₁ ℓ zw ow e negv negb k As p).1.length = As.length ∧
    (∀ A ∈ (addAllL B ℓ₁ ℓ zw ow e negv negb k As p).1, A.length = ℓ ∧
      ∀ v ∈ A, v < B + (addAllL B ℓ₁ ℓ zw ow e negv negb k As p).2.length) ∧
    HoldsO O B (addAllL B ℓ₁ ℓ zw ow e negv negb k As p).2 (fun σ =>
      σ zw = false → σ ow = true → σ negb = !σ negv →
      ∀ i < As.length,
        ((numVal σ ((addAllL B ℓ₁ ℓ zw ow e negv negb k As p).1.getD i []) : ℕ) : ℤ) ≡
          (numVal σ (As.getD i []) : ℤ) + sgnB (σ negv) * 2 ^ e * Pk ℓ₁ σ (k + i)
          [ZMOD 2 ^ ℓ]) := by
  intro As
  induction As with
  | nil =>
    intro k p _ _ _ _ _ _ _
    refine ⟨ExtL.refl _, by simp [addAllL], by simp [addAllL], by simp [addAllL], ?_⟩
    intro q inp _ _ _ i hi; simp at hi
  | cons A As ih =>
    intro k p hk hB hAs hzw how hnv hnb
    obtain ⟨hAl, hAv⟩ := hAs A List.mem_cons_self
    obtain ⟨e1, l1, o1, v1, h1⟩ := addScaled_spec O B ℓ₁ ℓ zw ow A k e negv negb p hAl hAv
      (fun v hv => by have := NL_lt n ℓ₁ k (by simp at hk; omega) v hv; omega)
      hzw how hnv hnb
    set r1 := addScaled B ℓ₁ ℓ zw ow A k e negv negb p with hr1
    have hle := e1.length_le
    obtain ⟨e2, l2, o2, v2, h2⟩ := ih (k + 1) r1.2 (by simp at hk; omega) hB
      (fun A' hA' => ⟨(hAs A' (List.mem_cons_of_mem _ hA')).1,
        fun v hv => by have := (hAs A' (List.mem_cons_of_mem _ hA')).2 v hv; omega⟩)
      (by omega) (by omega) (by omega) (by omega)
    set r2 := addAllL B ℓ₁ ℓ zw ow e negv negb (k + 1) As r1.2 with hr2
    have hle2 := e2.length_le
    change ExtL p r2.2 ∧ r2.2.length = p.length + (As.length + 1) * (12 * ℓ) ∧
      (r1.1 :: r2.1).length = As.length + 1 ∧
      (∀ A' ∈ r1.1 :: r2.1, A'.length = ℓ ∧ ∀ v ∈ A', v < B + r2.2.length) ∧
      HoldsO O B r2.2 (fun σ => σ zw = false → σ ow = true → σ negb = !σ negv →
        ∀ i < As.length + 1, ((numVal σ ((r1.1 :: r2.1).getD i []) : ℕ) : ℤ) ≡
          (numVal σ ((A :: As).getD i []) : ℤ) + sgnB (σ negv) * 2 ^ e * Pk ℓ₁ σ (k + i)
          [ZMOD 2 ^ ℓ])
    refine ⟨e1.trans e2, by rw [l2, l1]; ring, by simp [o2], ?_, ?_⟩
    · intro A' hA'
      rcases List.mem_cons.1 hA' with h | h
      · subst h; exact ⟨o1, fun v hv => by have := v1 v hv; omega⟩
      · exact v2 A' h
    · refine ((h1.mono e2).and h2).imp ?_
      rintro σ ⟨h1, h2⟩ hz ho hnb' i hi
      cases i with
      | zero => simpa using h1 hz ho hnb'
      | succ i =>
        have := h2 hz ho hnb' i (by omega)
        simpa [show k + 1 + i = k + (i + 1) by ring] using this

/-- Copy the address (in oracle order) into a fresh block and query it. -/
def addrSrc (ℓ : ℕ) (As : List (List ℕ)) (idx : ℕ) : ℕ :=
  (As.getD (idx / ℓ) []).getD (ℓ - 1 - idx % ℓ) 0

def queryB (n : ℕ) (As : List (List ℕ)) : BldO (n * ℓ) ℕ := fun p =>
  let r1 := blockE (K := n * ℓ) (fun idx : Fin (n * ℓ) =>
    (⟨fun a _ => a, addrSrc ℓ As idx, addrSrc ℓ As idx⟩ : Instr)) p
  orcE B (fun idx : Fin (n * ℓ) => B + p.length + idx.val) r1.2

theorem queryB_spec (n : ℕ) (O : (Fin (n * ℓ) → Bool) → Bool) (As : List (List ℕ))
    (p : List (OIns (n * ℓ))) (hAs : ∀ A ∈ As, ∀ v ∈ A, v < B + p.length)
    (h0 : 0 < B + p.length) :
    ExtL p (queryB B ℓ n As p).2 ∧ (queryB B ℓ n As p).2.length = p.length + n * ℓ + 1 ∧
    (queryB B ℓ n As p).1 < B + (queryB B ℓ n As p).2.length ∧
    HoldsO O B (queryB B ℓ n As p).2 (fun σ =>
      σ (queryB B ℓ n As p).1 = O (fun idx => σ (addrSrc ℓ As idx))) := by
  have hsrc : ∀ idx : ℕ, addrSrc ℓ As idx < B + p.length := by
    intro idx
    unfold addrSrc
    rw [List.getD_eq_getElem?_getD]
    cases h : (As.getD (idx / ℓ) [])[ℓ - 1 - idx % ℓ]? with
    | none => simpa using h0
    | some v =>
      simp only [Option.getD_some]
      have hmem : v ∈ As.getD (idx / ℓ) [] := List.mem_of_getElem? h
      rw [List.getD_eq_getElem?_getD] at hmem
      cases h2 : As[idx / ℓ]? with
      | none => rw [h2] at hmem; simp at hmem
      | some A => rw [h2] at hmem; exact hAs A (List.mem_of_getElem? h2) v hmem
  obtain ⟨e1, l1, h1⟩ := blockE_spec O B (K := n * ℓ) (fun idx : Fin (n * ℓ) =>
    (⟨fun a _ => a, addrSrc ℓ As idx, addrSrc ℓ As idx⟩ : Instr)) p
    (fun idx => ⟨hsrc _, hsrc _⟩)
  set r1 := blockE (K := n * ℓ) (fun idx : Fin (n * ℓ) =>
    (⟨fun a _ => a, addrSrc ℓ As idx, addrSrc ℓ As idx⟩ : Instr)) p with hr1
  obtain ⟨e2, l2, v2, h2⟩ := orcE_spec O B (fun idx : Fin (n * ℓ) => B + p.length + idx.val) r1.2
    (fun j => by rw [l1]; omega) (fun i j h => Fin.ext (by simpa using h))
  refine ⟨e1.trans e2, by rw [queryB, l2, l1], v2, ?_⟩
  refine ((h1.mono e2).and h2).imp ?_
  rintro σ ⟨h1, h2⟩
  show σ (orcE B _ r1.2).1 = _
  rw [h2]
  congr 1
  funext idx
  exact h1 idx

end OffB

end LTFC

-- ===== module OffB =====

/-! The address of a query equals `t • p` exactly. -/

open QAlgorithms

namespace LTFC

theorem int_eq_of_modEq {a b N : ℤ} (h : a ≡ b [ZMOD N]) (ha0 : 0 ≤ a) (ha : a < N)
    (hb0 : 0 ≤ b) (hb : b < N) : a = b := by
  unfold Int.ModEq at h
  rwa [Int.emod_eq_of_lt ha0 ha, Int.emod_eq_of_lt hb0 hb] at h

theorem numVal_lt (σ : ℕ → Bool) (l : List ℕ) : numVal σ l < 2 ^ l.length := by
  rw [numVal_eq_bval]; simpa using bval_lt (l.map σ)

/-- If a register holds `X + 2^(L-1) (mod 2^L)` with `|X| < 2^(L-1)`, it holds it exactly. -/
theorem exact_of_modEq (σ : ℕ → Bool) (A : List ℕ) (L : ℕ) (hL : A.length = L) (hL1 : 1 ≤ L)
    (X : ℤ) (hX : |X| < 2 ^ (L - 1))
    (h : ((numVal σ A : ℕ) : ℤ) ≡ X + 2 ^ (L - 1) [ZMOD 2 ^ L]) :
    ((numVal σ A : ℕ) : ℤ) = X + 2 ^ (L - 1) := by
  have h2 : (2 : ℤ) ^ L = 2 * 2 ^ (L - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hlt := numVal_lt σ A
  rw [hL] at hlt
  rw [abs_lt] at hX
  apply int_eq_of_modEq h (by positivity) (by exact_mod_cast hlt) (by linarith) (by linarith)

section Addr

variable (n ℓ₁ f₁ ℓ f E q m : ℕ)

theorem bitsToNat_addr (σ : ℕ → Bool) (As : List (List ℕ)) (k : Fin n) (hlen : As.length = n)
    (hA : (As.getD k []).length = ℓ) :
    bitsToNat (QuantumLTF.Membership.splitReg n ℓ
      (fun idx : Fin (n * ℓ) => σ (addrSrc ℓ As idx)) k) = numVal σ (As.getD k []) := by
  rw [numVal_eq_bval, ← bval_rev_bits]
  congr 1
  apply List.ext_getElem
  · rw [List.length_map, List.length_map, List.length_range, hA]
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [dif_pos (by omega)]
    simp only [QuantumLTF.Membership.splitReg, addrSrc, finProdFinEquiv_apply_val]
    have hℓ : 0 < ℓ := by omega
    have e1 : (k * ℓ + (ℓ - 1 - i)) / ℓ = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt (by omega), zero_add]
    have e2 : (k * ℓ + (ℓ - 1 - i)) % ℓ = ℓ - 1 - i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have e1' : (ℓ - 1 - i + ℓ * k) / ℓ = k := by rw [Nat.add_comm, Nat.mul_comm]; exact e1
    have e2' : (ℓ - 1 - i + ℓ * k) % ℓ = ℓ - 1 - i := by rw [Nat.add_comm, Nat.mul_comm]; exact e2
    simp only [e1, e2, e1', e2']
    rw [ show ℓ - 1 - (ℓ - 1 - i) = i by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hA]; omega), Option.getD_some]

/-- **Address correctness.** -/
theorem addr_eq (hf : f = E + q + f₁ + 1) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)
    (σ : ℕ → Bool) (As : List (List ℕ)) (T : ℤ) (hT : |T| ≤ (2 ^ m + 1) * 2 ^ q)
    (hlen : As.length = n) (hAl : ∀ k < n, (As.getD k []).length = ℓ)
    (hA : ∀ k < n, ((numVal σ (As.getD k []) : ℕ) : ℤ) ≡ T * Pk ℓ₁ σ k * 2 ^ E + 2 ^ (ℓ - 1)
      [ZMOD 2 ^ ℓ]) :
    QuantumLTF.Membership.addrOf n ℓ f (fun idx : Fin (n * ℓ) => σ (addrSrc ℓ As idx)) =
      ((T : ℝ) / 2 ^ q) • QuantumLTF.Membership.addrOf n ℓ₁ f₁ (pBits n ℓ₁ σ) := by
  ext k
  simp only [QuantumLTF.Membership.addrOf, PiLp.smul_apply, smul_eq_mul]
  simp only [QuantumLTF.Membership.fpVal]
  rw [bitsToNat_addr n ℓ σ As k hlen (hAl k k.isLt), ← numVal_NL]
  have hN := numVal_lt σ (NL ℓ₁ k)
  rw [NL_length] at hN
  have hP : |Pk ℓ₁ σ k| ≤ 2 ^ ℓ₁ := by
    have hN' : ((numVal σ (NL ℓ₁ k) : ℕ) : ℤ) < 2 ^ ℓ₁ := by exact_mod_cast hN
    have hN0 : (0 : ℤ) ≤ ((numVal σ (NL ℓ₁ k) : ℕ) : ℤ) := by positivity
    unfold Pk; rw [abs_le]; constructor <;> linarith
  have hbound : |T * Pk ℓ₁ σ k * 2 ^ E| < 2 ^ (ℓ - 1) := by
    rw [abs_mul, abs_mul, abs_pow, abs_two]
    have h1 : (2 ^ m + 1 : ℤ) ≤ 2 ^ (m + 1) := by rw [pow_succ]; have := one_le_pow₀ (M₀ := ℤ) (n := m) (a := 2) (by norm_num); linarith
    calc |T| * |Pk ℓ₁ σ k| * 2 ^ E ≤ ((2 ^ m + 1) * 2 ^ q) * 2 ^ ℓ₁ * 2 ^ E := by gcongr
      _ ≤ (2 ^ (m + 1) * 2 ^ q) * 2 ^ ℓ₁ * 2 ^ E := by gcongr
      _ = 2 ^ (m + 1 + q + ℓ₁ + E) := by simp only [pow_add]
      _ < 2 ^ (ℓ - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hex := exact_of_modEq σ (As.getD k []) ℓ (hAl k k.isLt) (by omega) _ hbound (hA k k.isLt)
  have hR : ((numVal σ (As.getD k []) : ℕ) : ℝ) = ((T * Pk ℓ₁ σ k * 2 ^ E : ℤ) : ℝ) + 2 ^ (ℓ - 1) := by
    exact_mod_cast hex
  rw [hR]
  simp only [Pk]
  push_cast
  have h2l : (2 : ℝ) ^ ℓ / 2 = 2 ^ (ℓ - 1) := by
    rw [show ℓ = (ℓ - 1) + 1 by omega, pow_succ]; simp
  have h2l1 : (2 : ℝ) ^ ℓ₁ / 2 * 2 = 2 ^ ℓ₁ := by ring
  rw [h2l, hf]
  field_simp
  rw [pow_add, pow_add, pow_add]
  ring

end Addr

end LTFC

-- ===== module OffC =====

/-! The coherent offset program (Theorem 3.1) and its semantics. -/

open QAlgorithms

namespace LTFC

theorem queryTree_run_map {n : ℕ} {α β : Type} (g : α → β)
    (T : QuantumLTF.Membership.QueryTree n α) (f : EuclideanSpace ℝ (Fin n) → ℤ) :
    (T.map g).run f = g (T.run f) := by
  induction T with
  | leaf a => rfl
  | query x next ih =>
      simp only [QuantumLTF.Membership.QueryTree.map, QuantumLTF.Membership.QueryTree.run]
      exact ih (f x)

theorem ltf_cases {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    QuantumLTF.Membership.ltf w θ x = 1 ∨ QuantumLTF.Membership.ltf w θ x = -1 := by
  unfold QuantumLTF.Membership.ltf QuantumLTF.Membership.sgn
  split_ifs <;> simp

section OffC

variable (n ℓ₁ f₁ m q ℓ f : ℕ)

/-- The oracle function of `memOracle n ℓ f w θ`. -/
noncomputable def Owt (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) : (Fin (n * ℓ) → Bool) → Bool :=
  fun y => decide (QuantumLTF.Membership.ltf w θ (QuantumLTF.Membership.addrOf n ℓ f y) = -1)

abbrev Ex : ℕ := f - f₁ - 1 - q
abbrev Bh : ℕ := m + q + 2

def p0 : List (OIns (n * ℓ)) :=
  [.bin ⟨fun _ _ => false, 0, 0⟩, .bin ⟨fun _ _ => true, n * ℓ₁, n * ℓ₁⟩]

def As0 : List (List ℕ) := List.replicate n (constL (n * ℓ₁) (n * ℓ₁ + 1) ℓ (2 ^ (ℓ - 1)))

def H0 : List ℕ := constL (n * ℓ₁) (n * ℓ₁ + 1) (Bh m q) (2 ^ (Bh m q - 1))

def bisLoop : ℕ → ℕ → List (List ℕ) → List ℕ → ℕ → BldO (n * ℓ) (List ℕ)
  | _, 0, _, H, _ => fun p => (H, p)
  | j, k + 1, As, H, sb => fun p =>
    let r1 := queryB (n * ℓ₁) ℓ n As p
    let r2 := emitO (n * ℓ₁) xor sb r1.1 r1.2
    let r3 := emitO (n * ℓ₁) (fun x _ => !x) r2.1 r2.1 r2.2
    let r4 := addAllL (n * ℓ₁) ℓ₁ ℓ (n * ℓ₁) (n * ℓ₁ + 1) (m + q + Ex f₁ q f - (j + 1))
      r2.1 r3.1 0 As r3.2
    let r5 := csub (n * ℓ₁) H (constL (n * ℓ₁) (n * ℓ₁ + 1) (Bh m q) (2 ^ (m + q - j))) r2.1 r4.2
    bisLoop (j + 1) k r4.1 r5.1 sb r5.2

def loopCost : ℕ := (n * ℓ + 1) + 2 + n * (12 * ℓ) + 6 * Bh m q

def AddrInv (σ : ℕ → Bool) (As : List (List ℕ)) (T : ℤ) : Prop :=
  ∀ k < n, ((numVal σ (As.getD k []) : ℕ) : ℤ) ≡ T * Pk ℓ₁ σ k * 2 ^ Ex f₁ q f + 2 ^ (ℓ - 1)
    [ZMOD 2 ^ ℓ]

def HInv (σ : ℕ → Bool) (H : List ℕ) (T : ℤ) : Prop :=
  ((numVal σ H : ℕ) : ℤ) ≡ 2 * T + 2 ^ (Bh m q - 1) [ZMOD 2 ^ Bh m q]

def AsOK (B : ℕ) (As : List (List ℕ)) (len : ℕ) : Prop :=
  As.length = n ∧ ∀ A ∈ As, A.length = ℓ ∧ ∀ v ∈ A, v < B + len

theorem AsOK.getD_length {B : ℕ} {As : List (List ℕ)} {len : ℕ} (h : AsOK n ℓ B As len)
    (k : ℕ) (hk : k < n) : (As.getD k []).length = ℓ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [h.1]; exact hk),
    Option.getD_some]
  exact (h.2 _ (List.getElem_mem _)).1

variable (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)

include hf hℓ in
theorem bisLoop_spec (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    ∀ (k j : ℕ) (As : List (List ℕ)) (H : List ℕ) (sb : ℕ) (p : List (OIns (n * ℓ))),
    j + k ≤ q → AsOK n ℓ (n * ℓ₁) As p.length → H.length = Bh m q →
    (∀ v ∈ H, v < n * ℓ₁ + p.length) → sb < n * ℓ₁ + p.length → n * ℓ₁ + 1 < n * ℓ₁ + p.length →
    ExtL p (bisLoop n ℓ₁ f₁ m q ℓ f j k As H sb p).2 ∧
    (bisLoop n ℓ₁ f₁ m q ℓ f j k As H sb p).2.length = p.length + k * loopCost n m q ℓ ∧
    (bisLoop n ℓ₁ f₁ m q ℓ f j k As H sb p).1.length = Bh m q ∧
    (∀ v ∈ (bisLoop n ℓ₁ f₁ m q ℓ f j k As H sb p).1,
      v < n * ℓ₁ + (bisLoop n ℓ₁ f₁ m q ℓ f j k As H sb p).2.length) ∧
    HoldsO (Owt n ℓ f w θ) (n * ℓ₁) (bisLoop n ℓ₁ f₁ m q ℓ f j k As H sb p).2 (fun σ =>
      σ (n * ℓ₁) = false → σ (n * ℓ₁ + 1) = true →
      ∀ T : ℤ, AddrInv n ℓ₁ f₁ q ℓ f σ As T → HInv m q σ H T →
        |T| + 2 ^ (m + q - j) ≤ 2 ^ (m + q) →
        ∃ T' : ℤ, HInv m q σ (bisLoop n ℓ₁ f₁ m q ℓ f j k As H sb p).1 T' ∧
          |T'| < 2 ^ (m + q) ∧
          (T' : ℝ) / 2 ^ q =
            (QuantumLTF.Membership.boundaryBisect
              (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (pBits n ℓ₁ σ))
              (if σ sb then 1 else -1) k
              (((T : ℝ) - 2 ^ (m + q - j)) / 2 ^ q) (((T : ℝ) + 2 ^ (m + q - j)) / 2 ^ q)).run
              (QuantumLTF.Membership.ltf w θ)) := by
  intro k
  induction k with
  | zero =>
    intro j As H sb p _ _ hH hHv _ _
    refine ⟨ExtL.refl _, by simp [bisLoop], by simpa [bisLoop] using hH,
      by simpa [bisLoop] using hHv, ?_⟩
    intro q' inp _ _ T _ hHi hT
    refine ⟨T, by simpa [bisLoop] using hHi, ?_, ?_⟩
    · have : (0 : ℤ) < 2 ^ (m + q - j) := by positivity
      linarith [abs_nonneg T]
    · simp only [QuantumLTF.Membership.boundaryBisect, QuantumLTF.Membership.QueryTree.run]
      field_simp
      ring
  | succ k ih =>
    intro j As H sb p hjk hAs hH hHv hsb hp2
    set B := n * ℓ₁ with hB
    set O := Owt n ℓ f w θ with hO
    obtain ⟨e1, l1, v1, h1⟩ := queryB_spec B ℓ n O As p (fun A hA => (hAs.2 A hA).2) (by omega)
    set r1 := queryB B ℓ n As p with hr1
    have le1 := e1.length_le
    obtain ⟨e2, l2, v2, h2⟩ := emitO_spec O B xor sb r1.1 r1.2 (by omega) v1
    set r2 := emitO B xor sb r1.1 r1.2 with hr2
    have le2 := e2.length_le
    obtain ⟨e3, l3, v3, h3⟩ := emitO_spec O B (fun x _ => !x) r2.1 r2.1 r2.2 v2 v2
    set r3 := emitO B (fun x _ => !x) r2.1 r2.1 r2.2 with hr3
    have le3 := e3.length_le
    obtain ⟨e4, l4, o4, v4, h4⟩ := addAllL_spec O B ℓ₁ ℓ n B (B + 1)
      (m + q + Ex f₁ q f - (j + 1)) r2.1 r3.1 As 0 r3.2 (by rw [hAs.1]; omega) le_rfl
      (fun A hA => ⟨(hAs.2 A hA).1, fun v hv => by have := (hAs.2 A hA).2 v hv; omega⟩)
      (by omega) (by omega) (by omega) v3
    set r4 := addAllL B ℓ₁ ℓ B (B + 1) (m + q + Ex f₁ q f - (j + 1)) r2.1 r3.1 0 As r3.2 with hr4
    have le4 := e4.length_le
    obtain ⟨e5, l5, o5, v5, h5⟩ := csub_spec O B H (constL B (B + 1) (Bh m q) (2 ^ (m + q - j)))
      r2.1 r4.2 (by rw [hH, constL_length])
      (fun v hv => by have := hHv v hv; omega)
      (fun v hv => by rcases constL_mem _ _ _ _ v hv with h | h <;> omega) (by omega)
    set r5 := csub B H (constL B (B + 1) (Bh m q) (2 ^ (m + q - j))) r2.1 r4.2 with hr5
    have le5 := e5.length_le
    have hAs' : AsOK n ℓ B r4.1 r5.2.length :=
      ⟨by rw [o4, hAs.1], fun A hA => ⟨(v4 A hA).1, fun v hv => by
        have := (v4 A hA).2 v hv; omega⟩⟩
    obtain ⟨e6, l6, o6, v6, h6⟩ := ih (j + 1) r4.1 r5.1 sb r5.2 (by omega) hAs'
      (by rw [o5, hH]) v5 (by omega) (by omega)
    set r6 := bisLoop n ℓ₁ f₁ m q ℓ f (j + 1) k r4.1 r5.1 sb r5.2 with hr6
    change ExtL p r6.2 ∧ r6.2.length = p.length + (k + 1) * loopCost n m q ℓ ∧
      r6.1.length = Bh m q ∧ (∀ v ∈ r6.1, v < B + r6.2.length) ∧
      HoldsO O B r6.2 (fun σ => σ B = false → σ (B + 1) = true →
        ∀ T : ℤ, AddrInv n ℓ₁ f₁ q ℓ f σ As T → HInv m q σ H T →
          |T| + 2 ^ (m + q - j) ≤ 2 ^ (m + q) →
          ∃ T' : ℤ, HInv m q σ r6.1 T' ∧ |T'| < 2 ^ (m + q) ∧
            (T' : ℝ) / 2 ^ q =
              (QuantumLTF.Membership.boundaryBisect
                (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (pBits n ℓ₁ σ))
                (if σ sb then 1 else -1) (k + 1)
                (((T : ℝ) - 2 ^ (m + q - j)) / 2 ^ q) (((T : ℝ) + 2 ^ (m + q - j)) / 2 ^ q)).run
                (QuantumLTF.Membership.ltf w θ))
    refine ⟨e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6)))), ?_, o6, v6, ?_⟩
    · rw [l6, l5, l4, l3, l2, l1, hAs.1, hH, loopCost]; ring
    · have e26 := e2.trans (e3.trans (e4.trans (e5.trans e6)))
      refine (((h1.mono e26).and (h2.mono (e3.trans (e4.trans (e5.trans e6))))).and
        (((h3.mono (e4.trans (e5.trans e6))).and (h4.mono (e5.trans e6))).and
        ((h5.mono e6).and h6))).imp ?_
      rintro σ ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩ hz ho T hAI hHI hT
      -- the query point
      set pv := QuantumLTF.Membership.addrOf n ℓ₁ f₁ (pBits n ℓ₁ σ) with hpv
      set F := QuantumLTF.Membership.ltf w θ with hF
      have hTq : |T| ≤ (2 ^ m + 1) * 2 ^ q := by
        have h1 : (2 : ℤ) ^ (m + q) ≤ (2 ^ m + 1) * 2 ^ q := by
          rw [pow_add]
          exact mul_le_mul_of_nonneg_right (by linarith only) (by positivity)
        have h2 : (0 : ℤ) < 2 ^ (m + q - j) := by positivity
        linarith only [h1, h2, hT]
      have haddr := addr_eq n ℓ₁ f₁ ℓ f (Ex f₁ q f) q m (by simp only [Ex]; omega) hℓ σ As T hTq
        hAs.1 (fun k hk => hAs.getD_length n ℓ k hk) hAI
      have hans : σ r1.1 = decide (F (((T : ℝ) / 2 ^ q) • pv) = -1) := by
        rw [h1, hO, Owt, haddr]
      set neg := σ r2.1 with hneg
      have hneg' : neg = xor (σ sb) (decide (F (((T : ℝ) / 2 ^ q) • pv) = -1)) := by
        rw [h2, hans]
      have hnb : σ r3.1 = !σ r2.1 := h3
      -- new center
      set Wn : ℤ := 2 ^ (m + q - (j + 1)) with hWn
      set T' : ℤ := T + sgnB neg * Wn with hT'
      have hW2 : (2 : ℤ) ^ (m + q - j) = 2 * Wn := by
        rw [hWn, ← pow_succ']; congr 1; omega
      have hAI' : AddrInv n ℓ₁ f₁ q ℓ f σ r4.1 T' := by
        intro k' hk'
        have := h4 hz ho hnb k' (by rw [hAs.1]; exact hk')
        refine this.trans ?_
        have h' := hAI k' hk'
        simp only [Nat.zero_add] at h' ⊢
        have hexp : (2 : ℤ) ^ (m + q + Ex f₁ q f - (j + 1)) = Wn * 2 ^ Ex f₁ q f := by
          rw [hWn, ← pow_add]; congr 1; omega
        rw [hexp]
        have := Int.ModEq.add_right (sgnB neg * (Wn * 2 ^ Ex f₁ q f) * Pk ℓ₁ σ k') h'
        refine this.trans ?_
        rw [hT']
        apply Int.ModEq.refl _ |>.trans
        ring_nf
        exact Int.ModEq.refl _
      have hHI' : HInv m q σ r5.1 T' := by
        unfold HInv at hHI ⊢
        rw [hH] at h5
        refine h5.trans ?_
        have hc : ((numVal σ (constL B (B + 1) (Bh m q) (2 ^ (m + q - j))) : ℕ) : ℤ) ≡
            2 ^ (m + q - j) [ZMOD 2 ^ Bh m q] := by
          rw [numVal_eq_bval, constL_val σ B (B + 1) hz ho]
          have := natmod_modEq (2 ^ (m + q - j)) (Bh m q)
          simpa using this
        have : (if neg then -((numVal σ (constL B (B + 1) (Bh m q) (2 ^ (m + q - j))) : ℕ) : ℤ)
            else ((numVal σ (constL B (B + 1) (Bh m q) (2 ^ (m + q - j))) : ℕ) : ℤ)) ≡
            sgnB neg * 2 ^ (m + q - j) [ZMOD 2 ^ Bh m q] := by
          cases neg
          · simpa [sgnB] using hc
          · simpa [sgnB] using hc.neg
        refine (Int.ModEq.add hHI this).trans ?_
        rw [hT', hW2]
        ring_nf
        exact Int.ModEq.refl _
      have hsg : sgnB neg = 1 ∨ sgnB neg = -1 := by cases neg <;> simp [sgnB]
      have hWpos : (0 : ℤ) < Wn := by positivity
      have hTb : |T'| + 2 ^ (m + q - (j + 1)) ≤ 2 ^ (m + q) := by
        rw [← hWn, hT']
        have : |T + sgnB neg * Wn| ≤ |T| + Wn := by
          rcases hsg with h | h <;> rw [h] <;> [skip; skip] <;>
            [exact (abs_add_le _ _).trans (by simp [abs_of_pos hWpos]);
             exact (abs_add_le _ _).trans (by simp [abs_neg, abs_of_pos hWpos])]
        linarith
      obtain ⟨T'', hH'', hb'', hrun⟩ := h6 hz ho T' hAI' hHI' hTb
      refine ⟨T'', hH'', hb'', ?_⟩
      rw [hrun]
      -- one tree step
      have hmid : ((((T : ℝ) - 2 ^ (m + q - j)) / 2 ^ q) +
          (((T : ℝ) + 2 ^ (m + q - j)) / 2 ^ q)) / 2 = (T : ℝ) / 2 ^ q := by ring
      simp only [QuantumLTF.Membership.boundaryBisect, QuantumLTF.Membership.QueryTree.run]
      rw [hmid]
      have hWR : ((2 : ℝ) ^ (m + q - j)) = 2 * ((Wn : ℤ) : ℝ) := by
        rw [hWn]; push_cast; rw [← pow_succ']; congr 1; omega
      have hWR' : ((2 : ℝ) ^ (m + q - (j + 1))) = ((Wn : ℤ) : ℝ) := by rw [hWn]; push_cast; rfl
      rw [hWR, hWR']
      rcases ltf_cases w θ (((T : ℝ) / 2 ^ q) • pv) with ha | ha
      · rw [← hF] at ha
        rw [ha]
        cases hs : σ sb
        · -- s = -1, ans = 1: go right
          have : neg = false := by rw [hneg', ha, hs]; decide
          simp only [this, hT', sgnB, if_false, Bool.false_eq_true]
          simp only [show ((-1 : ℤ) = 1) ↔ False by decide, if_false, if_true]
          congr 1 <;> push_cast <;> ring
        · have : neg = true := by rw [hneg', ha, hs]; decide
          simp only [this, hT', sgnB, if_true]
          congr 1 <;> push_cast <;> ring
      · rw [← hF] at ha
        rw [ha]
        cases hs : σ sb
        · have : neg = true := by rw [hneg', ha, hs]; decide
          simp only [this, hT', sgnB, if_true, Bool.false_eq_true, if_false]
          simp only [show ((-1 : ℤ) = 1) ↔ False by decide, if_false]
          congr 1 <;> push_cast <;> ring
        · have : neg = false := by rw [hneg', ha, hs]; decide
          simp only [this, hT', sgnB, if_true, Bool.false_eq_true, if_false]
          simp only [show ((-1 : ℤ) = 1) ↔ False by decide, if_false, if_true]
          congr 1 <;> push_cast <;> ring

end OffC

end LTFC

-- ===== module OffD =====

/-! The whole offset program: endpoint queries, orientation, bisection; its semantics. -/

open QAlgorithms

namespace LTFC

/-! ### Counting oracle instructions -/

theorem orcCount_append {K : ℕ} (l₁ l₂ : List (OIns K)) :
    orcCount (l₁ ++ l₂) = orcCount l₁ + orcCount l₂ := by
  induction l₁ with
  | nil => simp [orcCount]
  | cons g gs ih => simp only [List.cons_append, orcCount, ih]; ring

theorem orcCount_bin {K : ℕ} (l : List Instr) : orcCount (l.map (OIns.bin (K := K))) = 0 := by
  induction l with
  | nil => rfl
  | cons g gs ih => simp [orcCount, isOrc, ih]

/-- `p'` extends `p` by binary instructions only. -/
def BinExt {K : ℕ} (p p' : List (OIns K)) : Prop := ∃ r : List Instr, p' = p ++ r.map OIns.bin

theorem BinExt.refl {K : ℕ} (p : List (OIns K)) : BinExt p p := ⟨[], by simp⟩

theorem BinExt.trans {K : ℕ} {p p' p'' : List (OIns K)} (h₁ : BinExt p p') (h₂ : BinExt p' p'') :
    BinExt p p'' := by
  obtain ⟨r, rfl⟩ := h₁; obtain ⟨r', rfl⟩ := h₂; exact ⟨r ++ r', by simp⟩

theorem BinExt.orc {K : ℕ} {p p' : List (OIns K)} (h : BinExt p p') :
    orcCount p' = orcCount p := by
  obtain ⟨r, rfl⟩ := h; rw [orcCount_append, orcCount_bin]; rfl

section Bins

variable {K : ℕ} (B ℓ₁ ℓ : ℕ)

theorem emitO_bin (f : Bool → Bool → Bool) (a b : ℕ) (p : List (OIns K)) :
    BinExt p (emitO B f a b p).2 := ⟨[⟨f, a, b⟩], rfl⟩

theorem mapE_bin (f : Bool → Bool → Bool) (X : List ℕ) (b : ℕ) (p : List (OIns K)) :
    BinExt p (mapE B f X b p).2 := ⟨_, rfl⟩

theorem addcO_bin : ∀ (xs ys : List ℕ) (c : ℕ) (p : List (OIns K)),
    BinExt p (addcO B xs ys c p).2 := by
  intro xs
  induction xs with
  | nil => intro ys c p; exact BinExt.refl _
  | cons x xs ih =>
    intro ys c p
    cases ys with
    | nil => exact BinExt.refl _
    | cons y ys => exact (BinExt.refl _ |>.trans ⟨_, rfl⟩).trans (ih ys _ _)

theorem csub_bin (A X : List ℕ) (neg : ℕ) (p : List (OIns K)) : BinExt p (csub B A X neg p).2 :=
  (mapE_bin B xor X neg p).trans (addcO_bin B _ _ _ _)

theorem addScaled_bin (zw ow : ℕ) (A : List ℕ) (k e negv negb : ℕ) (p : List (OIns K)) :
    BinExt p (addScaled B ℓ₁ ℓ zw ow A k e negv negb p).2 :=
  (csub_bin B _ _ _ p).trans (csub_bin B _ _ _ _)

theorem addAllL_bin (zw ow e negv negb : ℕ) :
    ∀ (As : List (List ℕ)) (k : ℕ) (p : List (OIns K)),
    BinExt p (addAllL B ℓ₁ ℓ zw ow e negv negb k As p).2 := by
  intro As
  induction As with
  | nil => intro k p; exact BinExt.refl _
  | cons A As ih => intro k p; exact (addScaled_bin B ℓ₁ ℓ _ _ _ _ _ _ _ p).trans (ih _ _)

theorem queryB_orc (n : ℕ) (As : List (List ℕ)) (p : List (OIns (n * ℓ))) :
    orcCount (queryB B ℓ n As p).2 = orcCount p + 1 := by
  simp only [queryB, orcE, blockE, orcCount_append, orcCount_bin]
  simp [orcCount, isOrc]

end Bins

section OffD

variable (n ℓ₁ f₁ m q ℓ f : ℕ)

theorem bisLoop_orc : ∀ (k j : ℕ) (As : List (List ℕ)) (H : List ℕ) (sb : ℕ)
    (p : List (OIns (n * ℓ))),
    orcCount (bisLoop n ℓ₁ f₁ m q ℓ f j k As H sb p).2 = orcCount p + k := by
  intro k
  induction k with
  | zero => intro j As H sb p; rfl
  | succ k ih =>
    intro j As H sb p
    simp only [bisLoop]
    rw [ih, (csub_bin _ _ _ _ _).orc, (addAllL_bin _ _ _ _ _ _ _ _ _ _ _).orc,
      (emitO_bin _ _ _ _ _).orc, (emitO_bin _ _ _ _ _).orc, queryB_orc]
    ring

def endpointB (negv negb : ℕ) : BldO (n * ℓ) (List (List ℕ)) := fun p =>
  let r1 := addAllL (n * ℓ₁) ℓ₁ ℓ (n * ℓ₁) (n * ℓ₁ + 1) (m + q + Ex f₁ q f) negv negb 0
    (As0 n ℓ₁ ℓ) p
  addAllL (n * ℓ₁) ℓ₁ ℓ (n * ℓ₁) (n * ℓ₁ + 1) (q + Ex f₁ q f) negv negb 0 r1.1 r1.2

/-- The offset program: `(s variable, htil register (LSB first), program)`. -/
def offProg : ℕ × List ℕ × List (OIns (n * ℓ)) :=
  let B := n * ℓ₁
  let rR := endpointB n ℓ₁ f₁ m q ℓ f B (B + 1) (p0 n ℓ₁ ℓ)
  let aR := queryB B ℓ n rR.1 rR.2
  let rL := endpointB n ℓ₁ f₁ m q ℓ f (B + 1) B aR.2
  let aL := queryB B ℓ n rL.1 rL.2
  let sb := emitO B (fun r l => !r && l) aR.1 aL.1 aL.2
  let res := bisLoop n ℓ₁ f₁ m q ℓ f 0 q (As0 n ℓ₁ ℓ) (H0 n ℓ₁ m q) sb.1 sb.2
  (sb.1, res.1, res.2)

theorem offProg_orc : orcCount (offProg n ℓ₁ f₁ m q ℓ f).2.2 = q + 2 := by
  simp only [offProg, endpointB]
  rw [bisLoop_orc, (emitO_bin _ _ _ _ _).orc, queryB_orc, (addAllL_bin _ _ _ _ _ _ _ _ _ _ _).orc,
    (addAllL_bin _ _ _ _ _ _ _ _ _ _ _).orc, queryB_orc, (addAllL_bin _ _ _ _ _ _ _ _ _ _ _).orc,
    (addAllL_bin _ _ _ _ _ _ _ _ _ _ _).orc]
  simp [p0, orcCount, isOrc]; ring

def offLen : ℕ := 2 + 2 * (2 * (n * (12 * ℓ))) + 2 * (n * ℓ + 1) + 1 + q * loopCost n m q ℓ

theorem p0_holds (O : (Fin (n * ℓ) → Bool) → Bool) :
    HoldsO O (n * ℓ₁) (p0 n ℓ₁ ℓ) (fun σ => σ (n * ℓ₁) = false ∧ σ (n * ℓ₁ + 1) = true) := by
  intro q' inp
  constructor
  · have h := svalO_at O (n * ℓ₁) (p0 n ℓ₁ ℓ ++ q') inp 0 (by simp [p0])
    rw [Nat.add_zero] at h
    rw [h]
    simp only [p0, List.cons_append, List.getElem_cons_zero, evalIns]
    split_ifs <;> rfl
  · have h := svalO_at_bin O (n * ℓ₁) (p0 n ℓ₁ ℓ ++ q') inp 1 (by simp [p0])
      ⟨fun _ _ => true, n * ℓ₁, n * ℓ₁⟩ (by simp [p0]) (by show n * ℓ₁ < n * ℓ₁ + 1; omega)
      (by show n * ℓ₁ < n * ℓ₁ + 1; omega)
    exact h

theorem As0_ok (len : ℕ) (hB : 2 ≤ len) : AsOK n ℓ (n * ℓ₁) (As0 n ℓ₁ ℓ) len := by
  refine ⟨by simp [As0], fun A hA => ?_⟩
  simp only [As0, List.mem_replicate] at hA
  obtain ⟨_, rfl⟩ := hA
  refine ⟨constL_length _ _ _ _, fun v hv => ?_⟩
  rcases constL_mem _ _ _ _ v hv with h | h <;> omega

theorem As0_getD (k : ℕ) (hk : k < n) :
    (As0 n ℓ₁ ℓ).getD k [] = constL (n * ℓ₁) (n * ℓ₁ + 1) ℓ (2 ^ (ℓ - 1)) := by
  simp [As0, List.getD_eq_getElem?_getD, hk]

theorem constL_top (σ : ℕ → Bool) (zw ow L : ℕ) (hz : σ zw = false) (ho : σ ow = true)
    (hL : 1 ≤ L) : ((numVal σ (constL zw ow L (2 ^ (L - 1))) : ℕ) : ℤ) = 2 ^ (L - 1) := by
  rw [numVal_eq_bval, constL_val σ zw ow hz ho, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right
    (by norm_num) (by omega))]
  push_cast; rfl

variable (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)

include hℓ in
theorem endpointB_spec (O : (Fin (n * ℓ) → Bool) → Bool) (negv negb : ℕ)
    (p : List (OIns (n * ℓ))) (hp : 2 ≤ p.length) (hnv : negv < n * ℓ₁ + p.length)
    (hnb : negb < n * ℓ₁ + p.length) :
    ExtL p (endpointB n ℓ₁ f₁ m q ℓ f negv negb p).2 ∧
    (endpointB n ℓ₁ f₁ m q ℓ f negv negb p).2.length = p.length + 2 * (n * (12 * ℓ)) ∧
    AsOK n ℓ (n * ℓ₁) (endpointB n ℓ₁ f₁ m q ℓ f negv negb p).1
      (endpointB n ℓ₁ f₁ m q ℓ f negv negb p).2.length ∧
    HoldsO O (n * ℓ₁) (endpointB n ℓ₁ f₁ m q ℓ f negv negb p).2 (fun σ =>
      σ (n * ℓ₁) = false → σ (n * ℓ₁ + 1) = true → σ negb = !σ negv →
      AddrInv n ℓ₁ f₁ q ℓ f σ (endpointB n ℓ₁ f₁ m q ℓ f negv negb p).1
        (sgnB (σ negv) * (2 ^ (m + q) + 2 ^ q))) := by
  set B := n * ℓ₁ with hB
  have hA0 := As0_ok n ℓ₁ ℓ p.length hp
  obtain ⟨e1, l1, o1, v1, h1⟩ := addAllL_spec O B ℓ₁ ℓ n B (B + 1) (m + q + Ex f₁ q f) negv negb
    (As0 n ℓ₁ ℓ) 0 p (by rw [hA0.1]; omega) le_rfl hA0.2 (by omega) (by omega) hnv hnb
  set r1 := addAllL B ℓ₁ ℓ B (B + 1) (m + q + Ex f₁ q f) negv negb 0 (As0 n ℓ₁ ℓ) p with hr1
  have le1 := e1.length_le
  obtain ⟨e2, l2, o2, v2, h2⟩ := addAllL_spec O B ℓ₁ ℓ n B (B + 1) (q + Ex f₁ q f) negv negb
    r1.1 0 r1.2 (by rw [o1, hA0.1]; omega) le_rfl v1 (by omega) (by omega) (by omega) (by omega)
  set r2 := addAllL B ℓ₁ ℓ B (B + 1) (q + Ex f₁ q f) negv negb 0 r1.1 r1.2 with hr2
  refine ⟨e1.trans e2, ?_, ⟨by show r2.1.length = n; rw [o2, o1, hA0.1], v2⟩, ?_⟩
  · show r2.2.length = _
    rw [l2, l1, o1, hA0.1]; ring
  · refine ((h1.mono e2).and h2).imp ?_
    rintro σ ⟨h1, h2⟩ hz ho hnb' k hk
    have q2 := h2 hz ho hnb' k (by rw [o1, hA0.1]; exact hk)
    have q1 := h1 hz ho hnb' k (by rw [hA0.1]; exact hk)
    rw [As0_getD n ℓ₁ ℓ k hk, constL_top σ _ _ ℓ hz ho (by omega)] at q1
    refine q2.trans ?_
    simp only [Nat.zero_add] at q1 q2 ⊢
    refine (Int.ModEq.add_right _ q1).trans ?_
    unfold Int.ModEq; congr 1; simp only [pow_add]; ring

theorem ite_sgn_aux (c : Prop) [Decidable c] :
    (if decide ((if c then (1 : ℤ) else -1) = 1) = true then (1 : ℤ) else -1) = if c then 1 else -1 := by
  split_ifs <;> simp_all

include hf hℓ in
theorem offProg_spec (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    (offProg n ℓ₁ f₁ m q ℓ f).2.2.length = offLen n m q ℓ ∧
    (offProg n ℓ₁ f₁ m q ℓ f).1 < n * ℓ₁ + (offProg n ℓ₁ f₁ m q ℓ f).2.2.length ∧
    (offProg n ℓ₁ f₁ m q ℓ f).2.1.length = Bh m q ∧
    (∀ v ∈ (offProg n ℓ₁ f₁ m q ℓ f).2.1, v < n * ℓ₁ + (offProg n ℓ₁ f₁ m q ℓ f).2.2.length) ∧
    HoldsO (Owt n ℓ f w θ) (n * ℓ₁) (offProg n ℓ₁ f₁ m q ℓ f).2.2 (fun σ =>
      σ (offProg n ℓ₁ f₁ m q ℓ f).1 = decide
        (((QuantumLTF.Membership.boundarySearchTreeStrict
          (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (pBits n ℓ₁ σ)) ((2 : ℝ) ^ m) q).run
          (QuantumLTF.Membership.ltf w θ)).1 = 1) ∧
      ∃ T' : ℤ, HInv m q σ (offProg n ℓ₁ f₁ m q ℓ f).2.1 T' ∧ |T'| < 2 ^ (m + q) ∧
        (T' : ℝ) / 2 ^ q = ((QuantumLTF.Membership.boundarySearchTreeStrict
          (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (pBits n ℓ₁ σ)) ((2 : ℝ) ^ m) q).run
          (QuantumLTF.Membership.ltf w θ)).2) := by
  set B := n * ℓ₁ with hB
  set O := Owt n ℓ f w θ with hO
  have hp0 : (p0 n ℓ₁ ℓ).length = 2 := rfl
  obtain ⟨e1, l1, a1, h1⟩ := endpointB_spec n ℓ₁ f₁ m q ℓ f hℓ O B (B + 1) (p0 n ℓ₁ ℓ)
    (by rw [hp0]) (by rw [hp0]; omega) (by rw [hp0]; omega)
  set rR := endpointB n ℓ₁ f₁ m q ℓ f B (B + 1) (p0 n ℓ₁ ℓ) with hrR
  have le1 := e1.length_le
  obtain ⟨e2, l2, v2, h2⟩ := queryB_spec B ℓ n O rR.1 rR.2 (fun A hA => (a1.2 A hA).2) (by omega)
  set aR := queryB B ℓ n rR.1 rR.2 with haR
  have le2 := e2.length_le
  obtain ⟨e3, l3, a3, h3⟩ := endpointB_spec n ℓ₁ f₁ m q ℓ f hℓ O (B + 1) B aR.2
    (by rw [hp0] at le1; omega) (by omega) (by omega)
  set rL := endpointB n ℓ₁ f₁ m q ℓ f (B + 1) B aR.2 with hrL
  have le3 := e3.length_le
  obtain ⟨e4, l4, v4, h4⟩ := queryB_spec B ℓ n O rL.1 rL.2 (fun A hA => (a3.2 A hA).2) (by omega)
  set aL := queryB B ℓ n rL.1 rL.2 with haL
  have le4 := e4.length_le
  obtain ⟨e5, l5, v5, h5⟩ := emitO_spec O B (fun r l => !r && l) aR.1 aL.1 aL.2 (by omega) v4
  set sb := emitO B (fun r l => !r && l) aR.1 aL.1 aL.2 with hsb
  have le5 := e5.length_le
  have hH0l : (H0 n ℓ₁ m q).length = Bh m q := constL_length _ _ _ _
  obtain ⟨e6, l6, o6, v6, h6⟩ := bisLoop_spec n ℓ₁ f₁ m q ℓ f hf hℓ w θ q 0 (As0 n ℓ₁ ℓ)
    (H0 n ℓ₁ m q) sb.1 sb.2 (by omega) (As0_ok n ℓ₁ ℓ _ (by rw [hp0] at le1; omega)) hH0l
    (fun v hv => by rcases constL_mem _ _ _ _ v hv with h | h <;> rw [hp0] at le1 <;> omega)
    v5 (by rw [hp0] at le1; omega)
  set res := bisLoop n ℓ₁ f₁ m q ℓ f 0 q (As0 n ℓ₁ ℓ) (H0 n ℓ₁ m q) sb.1 sb.2 with hres
  have le6 := e6.length_le
  change res.2.length = _ ∧ sb.1 < B + res.2.length ∧ res.1.length = _ ∧
    (∀ v ∈ res.1, v < B + res.2.length) ∧ HoldsO O B res.2 (fun σ => σ sb.1 = _ ∧ _)
  refine ⟨?_, by omega, o6, v6, ?_⟩
  · rw [l6, l5, l4, l3, l2, l1, hp0, offLen]; ring
  · have e06 := e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))
    have hp0h := (p0_holds n ℓ₁ ℓ O).mono e06
    have H1 := h1.mono (e2.trans (e3.trans (e4.trans (e5.trans e6))))
    have H2 := h2.mono (e3.trans (e4.trans (e5.trans e6)))
    have H3 := h3.mono (e4.trans (e5.trans e6))
    have H4 := h4.mono (e5.trans e6)
    have H5 := h5.mono e6
    refine ((((H1.and H2).and (H3.and H4)).and (H5.and h6)).and hp0h).imp ?_
    rintro σ ⟨⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨h5, h6⟩⟩, hz, ho⟩
    set pv := QuantumLTF.Membership.addrOf n ℓ₁ f₁ (pBits n ℓ₁ σ) with hpv
    set F := QuantumLTF.Membership.ltf w θ with hF
    have hTb : |(2 : ℤ) ^ (m + q) + 2 ^ q| ≤ (2 ^ m + 1) * 2 ^ q := by
      rw [abs_of_pos (by positivity)]; rw [pow_add]; ring_nf; rfl
    have hTb' : |-((2 : ℤ) ^ (m + q) + 2 ^ q)| ≤ (2 ^ m + 1) * 2 ^ q := by rw [abs_neg]; exact hTb
    -- right endpoint
    have hAR := h1 hz ho (by rw [ho, hz]; rfl)
    rw [hz] at hAR
    simp only [sgnB, Bool.false_eq_true, if_false, one_mul] at hAR
    have haddrR := addr_eq n ℓ₁ f₁ ℓ f (Ex f₁ q f) q m (by simp only [Ex]; omega) hℓ σ rR.1 _ hTb
      a1.1 (fun k hk => a1.getD_length n ℓ k hk) hAR
    have hLR : (((2 : ℤ) ^ (m + q) + 2 ^ q : ℤ) : ℝ) / 2 ^ q = (2 : ℝ) ^ m + 1 := by
      push_cast; rw [pow_add]; field_simp
    rw [hLR] at haddrR
    have hR : σ aR.1 = decide (F (((2 : ℝ) ^ m + 1) • pv) = -1) := by rw [h2, hO, Owt, haddrR]
    -- left endpoint
    have hAL := h3 hz ho (by rw [ho, hz]; rfl)
    rw [ho] at hAL
    simp only [sgnB, if_true, neg_one_mul] at hAL
    have haddrL := addr_eq n ℓ₁ f₁ ℓ f (Ex f₁ q f) q m (by simp only [Ex]; omega) hℓ σ rL.1 _ hTb'
      a3.1 (fun k hk => a3.getD_length n ℓ k hk) hAL
    have hLL : ((-((2 : ℤ) ^ (m + q) + 2 ^ q) : ℤ) : ℝ) / 2 ^ q = -((2 : ℝ) ^ m + 1) := by
      push_cast; rw [pow_add]; field_simp
    rw [hLL] at haddrL
    have hL : σ aL.1 = decide (F ((-((2 : ℝ) ^ m + 1)) • pv) = -1) := by rw [h4, hO, Owt, haddrL]
    -- the tree
    have htree : (QuantumLTF.Membership.boundarySearchTreeStrict pv ((2 : ℝ) ^ m) q).run F =
        (if F (((2 : ℝ) ^ m + 1) • pv) = 1 ∧ F ((-((2 : ℝ) ^ m + 1)) • pv) = -1 then 1 else -1,
         (QuantumLTF.Membership.boundaryBisect pv
           (if F (((2 : ℝ) ^ m + 1) • pv) = 1 ∧ F ((-((2 : ℝ) ^ m + 1)) • pv) = -1 then 1 else -1)
           q (-(2 : ℝ) ^ m) ((2 : ℝ) ^ m)).run F) := by
      simp only [QuantumLTF.Membership.boundarySearchTreeStrict, QuantumLTF.Membership.QueryTree.run]
      rw [queryTree_run_map]
    have hsbv : σ sb.1 = decide ((if F (((2 : ℝ) ^ m + 1) • pv) = 1 ∧
        F ((-((2 : ℝ) ^ m + 1)) • pv) = -1 then (1 : ℤ) else -1) = 1) := by
      rw [h5, hR, hL]
      rcases ltf_cases w θ (((2 : ℝ) ^ m + 1) • pv) with ha | ha <;>
        rcases ltf_cases w θ ((-((2 : ℝ) ^ m + 1)) • pv) with hb | hb <;>
        · rw [← hF] at ha hb
          rw [ha, hb]
          decide
    have hs : (if σ sb.1 then (1 : ℤ) else -1) =
        (if F (((2 : ℝ) ^ m + 1) • pv) = 1 ∧ F ((-((2 : ℝ) ^ m + 1)) • pv) = -1 then 1 else -1) := by
      rw [hsbv]; exact ite_sgn_aux _
    refine ⟨by rw [htree]; exact hsbv, ?_⟩
    -- bisection
    have hAI0 : AddrInv n ℓ₁ f₁ q ℓ f σ (As0 n ℓ₁ ℓ) 0 := by
      intro k hk
      rw [As0_getD n ℓ₁ ℓ k hk, constL_top σ _ _ ℓ hz ho (by omega)]
      simp
    have hHI0 : HInv m q σ (H0 n ℓ₁ m q) 0 := by
      unfold HInv H0
      rw [constL_top σ _ _ _ hz ho (by simp [Bh])]
      simp
    obtain ⟨T', hH', hb', hrun⟩ := h6 hz ho 0 hAI0 hHI0 (by simp)
    refine ⟨T', hH', hb', ?_⟩
    rw [hrun, htree, hs]
    congr 2
    · push_cast; simp only [Nat.sub_zero, zero_sub, pow_add]; field_simp
    · push_cast; simp only [Nat.sub_zero, zero_add, pow_add]; field_simp

end OffD

end LTFC

-- ===== module PrepP =====

/-!
# Piece (1): preparing the random reference direction `p` by Hadamards

`hadCirc e` applies a Hadamard to every wire of the register `e`.  From `|0…0⟩` it prepares the
uniform superposition over the strings of the register (`hadCirc_zero`).  If the rest of the
algorithm `V` never changes the register `e` (block property), the final outcome distribution is
the uniform average over the register values of the outcome distributions of the runs started
from `|u⟩` (`prob_mix`), i.e. the register behaves exactly like a classical uniformly random
string, as in `uniform_dyadic_reference_direction`.
-/

open QAlgorithms

namespace LTFC

section Prep

variable {r : ℕ} {ar : Fin r → ℕ}

/-- `1/√2` as a complex number. -/
noncomputable abbrev cH : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

noncomputable def hadList {M : ℕ} (ws : List (Fin M)) : OracleCircuit G12 ar M :=
  ws.map stepH

theorem hadamard_col_false (x : Bool) : hadamard x false = cH := by
  cases x <;> simp [hadamard]

theorem hadList_state {M : ℕ} (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ) :
    ∀ (ws : List (Fin M)), ws.Nodup → ∀ z : Qubits M, (∀ v ∈ ws, z v = false) →
      ((hadList ws : OracleCircuit G12 ar M).unitary orc).mulVec (bv z) =
        fun y => if ∀ v, v ∉ ws → y v = z v then cH ^ ws.length else 0 := by
  intro ws
  induction ws with
  | nil =>
    intro _ z _
    funext y
    simp only [hadList, List.map_nil, unitary_nil, Matrix.one_mulVec, List.length_nil, pow_zero,
      List.not_mem_nil, not_false_eq_true, forall_const, bv, Pi.single_apply]
    by_cases h : y = z
    · subst h; simp
    · rw [if_neg h, if_neg]; intro h'; exact h (funext h')
  | cons t ws ih =>
    intro hnd z hz
    rw [List.nodup_cons] at hnd
    have hzt : z t = false := hz t List.mem_cons_self
    rw [hadList, List.map_cons]
    rw [unitary_cons, ← Matrix.mulVec_mulVec]
    simp only [stepH, OracleStep.mat]
    rw [mulVec_H, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    have hz' : ∀ b : Bool, ∀ v ∈ ws, Function.update z t b v = false := by
      intro b v hv
      have hvt : v ≠ t := fun e => hnd.1 (e ▸ hv)
      rw [Function.update_of_ne hvt]; exact hz v (List.mem_cons_of_mem _ hv)
    have e1 := ih hnd.2 _ (hz' false)
    have e2 := ih hnd.2 _ (hz' true)
    simp only [hadList] at e1 e2
    rw [Fintype.sum_bool, e1, e2]
    funext y
    simp only [ Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hzt, hadamard_col_false, List.length_cons]
    by_cases hy : ∀ v, v ∉ t :: ws → y v = z v
    · rw [if_pos hy]
      have hyo : ∀ v, v ∉ ws → v ≠ t → y v = z v := fun v h1 h2 => hy v (by simp [h1, h2])
      cases hyt : y t
      · rw [if_neg, if_pos]
        · ring
        · intro v hv
          by_cases hvt : v = t
          · subst hvt; simp [hyt]
          · rw [Function.update_of_ne hvt]; exact hyo v hv hvt
        · intro h
          have := h t hnd.1
          simp [hyt] at this
      · rw [if_pos, if_neg]
        · ring
        · intro h
          have := h t hnd.1
          simp [hyt] at this
        · intro v hv
          by_cases hvt : v = t
          · subst hvt; simp [hyt]
          · rw [Function.update_of_ne hvt]; exact hyo v hv hvt
    · rw [if_neg hy]
      have h1 : ∀ b : Bool, ¬ ∀ v, v ∉ ws → y v = Function.update z t b v := by
        intro b h
        apply hy
        intro v hv
        have hvt : v ≠ t := fun e => hv (e ▸ List.mem_cons_self)
        have hvw : v ∉ ws := fun h' => hv (List.mem_cons_of_mem _ h')
        rw [h v hvw, Function.update_of_ne hvt]
      rw [if_neg (h1 true), if_neg (h1 false)]
      ring

/-- Hadamards on the register `e`. -/
noncomputable def hadCirc {N M : ℕ} (e : Fin N ↪ Fin M) : OracleCircuit G12 ar M :=
  hadList (List.ofFn e)

theorem hadCirc_counts {N M : ℕ} (e : Fin N ↪ Fin M) :
    QuantumLTF.Membership.Uncontrolled (hadCirc (ar := ar) e) ∧
    (hadCirc (ar := ar) e).gateCount = N ∧ ∀ k, (hadCirc (ar := ar) e).queryCount k = 0 := by
  have hall : AllGates (hadCirc (ar := ar) e) := by
    intro s hs
    simp only [hadCirc, hadList, List.mem_map] at hs
    obtain ⟨t, _, rfl⟩ := hs
    exact ⟨_, rfl⟩
  refine ⟨hall.uncontrolled, ?_, fun k => hall.queryCount k⟩
  rw [hall.gateCount]; simp [hadCirc, hadList]

theorem hadCirc_zero {N M : ℕ} (e : Fin N ↪ Fin M)
    (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ) :
    ((hadCirc (ar := ar) e).unitary orc).mulVec (bv (fun _ => false)) =
      fun y => if ∀ v, v ∉ Set.range e → y v = false then cH ^ N else 0 := by
  have hnd : (List.ofFn e).Nodup := List.nodup_ofFn.2 e.injective
  rw [hadCirc, hadList_state orc _ hnd _ (fun _ _ => rfl)]
  funext y
  simp only [List.length_ofFn, List.mem_ofFn]
  congr 1

theorem cH_normSq : ‖cH‖ ^ 2 = 1 / 2 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (by norm_num)]
  norm_num

/-- **Uniform mixing.** If `V` never changes the register `e`, the outcome distribution of
`V · H^{⊗e} |0⟩` is the uniform average over `u` of that of `V |u⟩`. -/
theorem prob_mix {N M : ℕ} (e : Fin N ↪ Fin M) (V : Matrix (Qubits M) (Qubits M) ℂ)
    (hV : ∀ (u : Qubits N) (y : Qubits M),
      (V.mulVec (bv (setPart (fun _ => false) e u))) y ≠ 0 → y ∘ e = u)
    (Hm : Matrix (Qubits M) (Qubits M) ℂ)
    (hH : Hm.mulVec (bv (fun _ => false)) =
      fun y => if ∀ v, v ∉ Set.range e → y v = false then cH ^ N else 0)
    (E : Qubits M → Prop) [DecidablePred E] :
    ∑ y ∈ Finset.univ.filter E, ‖((V * Hm).mulVec (bv (fun _ => false))) y‖ ^ 2 =
      (1 / 2) ^ N * ∑ u : Qubits N,
        ∑ y ∈ Finset.univ.filter E, ‖(V.mulVec (bv (setPart (fun _ => false) e u))) y‖ ^ 2 := by
  have hdec : Hm.mulVec (bv (fun _ => false)) =
      ∑ u : Qubits N, cH ^ N • bv (setPart (fun _ => false) e u) := by
    rw [hH]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bv, Pi.single_apply, mul_ite,
      mul_one, mul_zero]
    by_cases hy : ∀ v, v ∉ Set.range e → y v = false
    · rw [if_pos hy, Finset.sum_eq_single (y ∘ e)]
      · rw [if_pos]; exact eq_setPart_iff.2 ⟨rfl, fun a ha => hy a ha⟩
      · intro u _ hu; rw [if_neg]; intro h; exact hu (eq_setPart_iff.1 h).1.symm
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hy]
      symm
      apply Finset.sum_eq_zero
      intro u _
      rw [if_neg]
      intro h
      exact hy (eq_setPart_iff.1 h).2
  have hVy : ∀ y, ((V * Hm).mulVec (bv (fun _ => false))) y =
      cH ^ N * (V.mulVec (bv (setPart (fun _ => false) e (y ∘ e)))) y := by
    intro y
    rw [← Matrix.mulVec_mulVec, hdec, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (y ∘ e)]
    intro u _ hu
    by_contra hne
    have := hV u y (fun h0 => hne (by rw [h0, mul_zero]))
    exact hu this.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsq : ∀ y, ‖((V * Hm).mulVec (bv (fun _ => false))) y‖ ^ 2 =
      (1 / 2) ^ N * ∑ u : Qubits N, ‖(V.mulVec (bv (setPart (fun _ => false) e u))) y‖ ^ 2 := by
    intro y
    rw [hVy, norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm N 2, pow_mul, cH_normSq]
    congr 1
    rw [Finset.sum_eq_single (y ∘ e)]
    · intro u _ hu
      by_contra hne
      have h1 : (V.mulVec (bv (setPart (fun _ => false) e u))) y ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      exact hu (hV u y h1).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun y _ => hsq y), ← Finset.mul_sum, Finset.sum_comm]

end Prep

open Classical in
/-- The uniform law of `uniform_dyadic_reference_direction` as a normalized count. -/
theorem uniform_toReal {X : Type} [Fintype X] [Nonempty X] (S : Set X) :
    ((PMF.uniformOfFintype X).toOuterMeasure S).toReal =
      ((Finset.univ.filter (· ∈ S)).card : ℝ) / Fintype.card X := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [ENNReal.toReal_div]
  simp [Fintype.card_subtype]

end LTFC

-- ===== module OffE =====

/-!
# Piece (2): the coherent, uniform-in-`p` offset estimation circuit (Theorem 3.1)

`offset_circuit`: one uncontrolled `gates12` circuit, chosen before `w, θ` and independent of the
value of `p`, that maps `|p, 0…0⟩` to `|p, s, h̃, 0…0⟩` (all work wires restored), where
`(s, h̃) = (boundarySearchTreeStrict p (2^m) q).run (ltf w θ)` exactly, using `2(q+2)` queries.
-/

open QAlgorithms

namespace LTFC

section Locality

variable {K : ℕ}

def AgreeB {M : ℕ} (R : ℕ) (z z' : Qubits M) : Prop := ∀ v : Fin M, v.val < R → z v = z' v

theorem stepFO_other (M : ℕ) (O : (Fin K → Bool) → Bool) (g : OIns K) (pos : ℕ) (z : Qubits M)
    (v : Fin M) (hv : v.val ≠ pos) : stepFO M O g pos z v = z v := by
  cases g with
  | bin g =>
    simp only [stepFO]; unfold stepF
    split_ifs
    · rw [Function.update_of_ne]; intro e; exact hv (by rw [e])
    · rfl
  | orc addr =>
    simp only [stepFO]
    split_ifs
    · rw [Function.update_of_ne]; intro e; exact hv (by rw [e])
    · rfl

theorem stepFO_agree (M : ℕ) (O : (Fin K → Bool) → Bool) (g : OIns K) (pos R : ℕ) (hpos : pos < R)
    (z z' : Qubits M) (h : AgreeB R z z') : AgreeB R (stepFO M O g pos z) (stepFO M O g pos z') := by
  intro v hv
  by_cases hvp : v.val = pos
  · cases g with
    | bin g =>
      simp only [stepFO]; unfold stepF
      split_ifs with hc
      · have hv' : v = ⟨pos, hc.1⟩ := Fin.ext hvp
        subst hv'
        rw [Function.update_self, Function.update_self, h _ hv, h ⟨g.a, _⟩ (by simp; omega),
          h ⟨g.b, _⟩ (by simp; omega)]
      · exact h v hv
    | orc addr =>
      simp only [stepFO]
      split_ifs with hc
      · have hv' : v = ⟨pos, hc.1⟩ := Fin.ext hvp
        subst hv'
        rw [Function.update_self, Function.update_self, h _ hv]
        congr 2; funext j; exact h _ (by have := hc.2.1 j; simp; omega)
      · exact h v hv
  · rw [stepFO_other M O g pos z v hvp, stepFO_other M O g pos z' v hvp]; exact h v hv

theorem runRevO_agree (M : ℕ) (O : (Fin K → Bool) → Bool) (P : List (OIns K)) :
    ∀ (pos R : ℕ), pos + P.length ≤ R → ∀ z z' : Qubits M, AgreeB R z z' →
      AgreeB R (runRevO M O P pos z) (runRevO M O P pos z') := by
  induction P with
  | nil => intro pos R _ z z' h; exact h
  | cons g gs ih =>
    intro pos R hR z z' h
    simp only [runRevO, Function.comp_apply]
    exact stepFO_agree M O g pos R (by simp at hR; omega) _ _
      (ih (pos + 1) R (by simp at hR; omega) z z' h)

theorem runRevO_high (M : ℕ) (O : (Fin K → Bool) → Bool) (P : List (OIns K)) :
    ∀ (pos : ℕ) (z : Qubits M) (v : Fin M), pos + P.length ≤ v.val → runRevO M O P pos z v = z v := by
  induction P with
  | nil => intro pos z v _; rfl
  | cons g gs ih =>
    intro pos z v hv
    simp only [runRevO, Function.comp_apply]
    rw [stepFO_other M O g pos _ v (by simp at hv; omega), ih (pos + 1) z v (by simp at hv; omega)]

theorem svalO_beyond (O : (Fin K → Bool) → Bool) (B : ℕ) (P : List (OIns K)) (inp : ℕ → Bool)
    (v : ℕ) (hv : B + P.length ≤ v) : svalO O B P inp v = false := by
  rw [svalO, if_neg (by omega), dif_neg (by omega)]

end Locality

/-! ### Copy circuits -/

section Copy

variable {a : ℕ}

noncomputable def cnotStep {M : ℕ} (s t : Fin M) : OracleCircuit G12 (fun _ : Fin 1 => a) M :=
  if h : s ≠ t then [stepCNOT s t h] else []

noncomputable def copyList {M : ℕ} : List (Fin M × Fin M) → OracleCircuit G12 (fun _ : Fin 1 => a) M
  | [] => []
  | pr :: l => cnotStep pr.1 pr.2 ++ copyList l

def cpL {M : ℕ} : List (Fin M × Fin M) → Qubits M → Qubits M
  | [] => id
  | pr :: l => cpL l ∘ (fun z => Function.update z pr.2 (xor (z pr.2) (z pr.1)))

theorem impl_copyList {M : ℕ} (l : List (Fin M × Fin M)) (hl : ∀ pr ∈ l, pr.1 ≠ pr.2) :
    Implements (copyList (a := a) l) (cpL l) := by
  induction l with
  | nil => exact Implements.nil
  | cons pr l ih =>
    have h1 : Implements (cnotStep (a := a) pr.1 pr.2)
        (fun z => Function.update z pr.2 (xor (z pr.2) (z pr.1))) := by
      unfold cnotStep
      rw [dif_pos (hl pr List.mem_cons_self)]
      exact impl_CNOT _ _ _
    exact h1.append (ih (fun pr' h => hl pr' (List.mem_cons_of_mem _ h)))

theorem cpL_apply {M : ℕ} (l : List (Fin M × Fin M)) (hnd : (l.map Prod.snd).Nodup)
    (hsrc : ∀ pr ∈ l, ∀ pr' ∈ l, pr.1 ≠ pr'.2) (z : Qubits M) (v : Fin M) :
    cpL l z v = match l.find? (fun pr => pr.2 = v) with
      | some pr => xor (z v) (z pr.1)
      | none => z v := by
  induction l generalizing z with
  | nil => rfl
  | cons pr l ih =>
    simp only [cpL, Function.comp_apply]
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [ih hnd.2 (fun x hx y hy => hsrc x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))]
    simp only [List.find?_cons]
    by_cases hv : pr.2 = v
    · subst hv
      simp only [decide_true]
      have hnone : l.find? (fun pr' => decide (pr'.2 = pr.2)) = none := by
        rw [List.find?_eq_none]
        intro x hx hx'
        apply hnd.1
        simp only [decide_eq_true_eq] at hx'
        exact List.mem_map.2 ⟨x, hx, hx'⟩
      rw [hnone, Function.update_self]
    · simp only [hv, decide_false]
      cases hf : l.find? (fun pr' => decide (pr'.2 = v)) with
      | none => simp only; rw [Function.update_of_ne (Ne.symm hv)]
      | some pr' =>
        simp only
        have hmem := List.mem_of_find?_eq_some hf
        rw [Function.update_of_ne (Ne.symm hv), Function.update_of_ne]
        exact hsrc pr' (List.mem_cons_of_mem _ hmem) pr List.mem_cons_self

end Copy

/-! ### The circuit -/

section OffE

variable (n ℓ₁ f₁ m q ℓ f : ℕ)

abbrev offP : List (OIns (n * ℓ)) := (offProg n ℓ₁ f₁ m q ℓ f).2.2
abbrev offL : ℕ := (offP n ℓ₁ f₁ m q ℓ f).length
abbrev offM : ℕ := n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f + 1 + Bh m q

def offSw : Fin (offM n ℓ₁ f₁ m q ℓ f) := ⟨n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f, by simp [offM]; omega⟩

def offHw : Fin (Bh m q) ↪ Fin (offM n ℓ₁ f₁ m q ℓ f) :=
  ⟨fun t => ⟨n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f + 1 + t.val, by simp only [offM]; omega⟩, by
    intro t t' h; simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩

def offPin : Fin (n * ℓ₁) ↪ Fin (offM n ℓ₁ f₁ m q ℓ f) :=
  ⟨fun i => ⟨i.val, by simp only [offM]; omega⟩, by
    intro i i' h; simp only [Fin.mk.injEq] at h; exact Fin.ext h⟩

theorem offSrc_lt (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ) (t : ℕ) :
    ((offProg n ℓ₁ f₁ m q ℓ f).2.1.getD t 0) < n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f := by
  have hs := offProg_spec n ℓ₁ f₁ m q ℓ f hf hℓ 0 0
  rw [List.getD_eq_getElem?_getD]
  cases h : (offProg n ℓ₁ f₁ m q ℓ f).2.1[t]? with
  | none =>
    simp only [Option.getD_some, Option.getD_none]
    have h1 := hs.1
    have h2 : 0 < offLen n m q ℓ := by unfold offLen; omega
    show 0 < n * ℓ₁ + (offProg n ℓ₁ f₁ m q ℓ f).2.2.length
    omega
  | some v =>
    simp only [Option.getD_some]
    exact hs.2.2.2.1 v (List.mem_of_getElem? h)

def offPairs (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ) :
    List (Fin (offM n ℓ₁ f₁ m q ℓ f) × Fin (offM n ℓ₁ f₁ m q ℓ f)) :=
  (⟨(offProg n ℓ₁ f₁ m q ℓ f).1, by
      have := (offProg_spec n ℓ₁ f₁ m q ℓ f hf hℓ 0 0).2.1
      show _ < n * ℓ₁ + (offProg n ℓ₁ f₁ m q ℓ f).2.2.length + 1 + Bh m q
      omega⟩,
    offSw n ℓ₁ f₁ m q ℓ f) ::
  List.ofFn (fun t : Fin (Bh m q) =>
    ((⟨(offProg n ℓ₁ f₁ m q ℓ f).2.1.getD (Bh m q - 1 - t.val) 0, by
        have := offSrc_lt n ℓ₁ f₁ m q ℓ f hf hℓ (Bh m q - 1 - t.val)
        show _ < n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f + 1 + Bh m q
        omega⟩ :
        Fin (offM n ℓ₁ f₁ m q ℓ f)), offHw n ℓ₁ f₁ m q ℓ f t))

noncomputable def offCirc (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ) :
    OracleCircuit G12 (fun _ : Fin 1 => n * ℓ + 1) (offM n ℓ₁ f₁ m q ℓ f) :=
  compileO (offM n ℓ₁ f₁ m q ℓ f) (offP n ℓ₁ f₁ m q ℓ f) (n * ℓ₁) ++
    copyList (offPairs n ℓ₁ f₁ m q ℓ f hf hℓ) ++
    compileRevO (offM n ℓ₁ f₁ m q ℓ f) (offP n ℓ₁ f₁ m q ℓ f) (n * ℓ₁)

end OffE

end LTFC

namespace LTFC

section OffF

variable (n ℓ₁ f₁ m q ℓ f : ℕ)

theorem copyList_counts {a M : ℕ} (l : List (Fin M × Fin M)) :
    AllGates (copyList (a := a) l) ∧ (copyList (a := a) l).length ≤ l.length := by
  induction l with
  | nil => exact ⟨AllGates.nil, by simp [copyList]⟩
  | cons pr l ih =>
    have h1 : AllGates (cnotStep (a := a) pr.1 pr.2) ∧ (cnotStep (a := a) pr.1 pr.2).length ≤ 1 := by
      unfold cnotStep
      split_ifs
      · exact ⟨allGates_single _ ⟨_, rfl⟩, by simp⟩
      · exact ⟨AllGates.nil, by simp⟩
    refine ⟨h1.1.append ih.1, ?_⟩
    simp only [copyList, List.length_append, List.length_cons]
    have := ih.2; have := h1.2; omega

theorem offLen_le (q n ℓ m : ℕ) :
    20 * offLen n m q ℓ + (Bh m q + 1) ≤ 1200 * (n * ℓ + m + q + 2) * (q + 2) := by
  unfold offLen loopCost Bh
  set N := n * ℓ with hN
  have e1 : n * (12 * ℓ) = 12 * N := by rw [hN]; ring
  rw [e1]
  nlinarith [Nat.zero_le N, Nat.zero_le m, Nat.zero_le q, Nat.zero_le (q * N), Nat.zero_le (q * m),
    Nat.zero_le (q * q)]

variable (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)

@[simp] theorem offHw_val (t : Fin (Bh m q)) :
    (offHw n ℓ₁ f₁ m q ℓ f t).val = n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f + 1 + t.val := rfl
@[simp] theorem offSw_val : (offSw n ℓ₁ f₁ m q ℓ f).val = n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f := rfl
@[simp] theorem offPin_val (i : Fin (n * ℓ₁)) : (offPin n ℓ₁ f₁ m q ℓ f i).val = i.val := rfl

include hf hℓ in
/-- **Coherent offset estimation, uniform in `p`.** -/
theorem offset_circuit :
    QuantumLTF.Membership.Uncontrolled (offCirc n ℓ₁ f₁ m q ℓ f hf hℓ) ∧
    (offCirc n ℓ₁ f₁ m q ℓ f hf hℓ).queryCount 0 ≤ 2 * (q + 2) ∧
    (offCirc n ℓ₁ f₁ m q ℓ f hf hℓ).gateCount ≤ 1200 * (n * ℓ + m + q + 2) * (q + 2) ∧
    ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (z : Qubits (offM n ℓ₁ f₁ m q ℓ f)),
      (∀ v : Fin (offM n ℓ₁ f₁ m q ℓ f), n * ℓ₁ ≤ v.val → z v = false) →
      ∃ z' : Qubits (offM n ℓ₁ f₁ m q ℓ f),
        ((offCirc n ℓ₁ f₁ m q ℓ f hf hℓ).unitary
          fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ).mulVec (bv z) = bv z' ∧
        (∀ v, v ≠ offSw n ℓ₁ f₁ m q ℓ f → v ∉ Set.range (offHw n ℓ₁ f₁ m q ℓ f) → z' v = z v) ∧
        z' (offSw n ℓ₁ f₁ m q ℓ f) = decide
          (((QuantumLTF.Membership.boundarySearchTreeStrict
            (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (z ∘ offPin n ℓ₁ f₁ m q ℓ f)) ((2 : ℝ) ^ m) q).run
            (QuantumLTF.Membership.ltf w θ)).1 = 1) ∧
        QuantumLTF.Membership.fpVal (m + q + 2) (q + 1) (z' ∘ offHw n ℓ₁ f₁ m q ℓ f) =
          ((QuantumLTF.Membership.boundarySearchTreeStrict
            (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (z ∘ offPin n ℓ₁ f₁ m q ℓ f)) ((2 : ℝ) ^ m) q).run
            (QuantumLTF.Membership.ltf w θ)).2 := by
  have hspec := offProg_spec n ℓ₁ f₁ m q ℓ f hf hℓ
  have hL : offL n ℓ₁ f₁ m q ℓ f = offLen n m q ℓ := (hspec 0 0).1
  have hsbl : (offProg n ℓ₁ f₁ m q ℓ f).1 < n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f := (hspec 0 0).2.1
  obtain ⟨u1, g1, q1, u2, g2, q2⟩ := counts_compileO (K := n * ℓ) (offM n ℓ₁ f₁ m q ℓ f)
    (offP n ℓ₁ f₁ m q ℓ f) (n * ℓ₁)
  have hcp := copyList_counts (a := n * ℓ + 1) (offPairs n ℓ₁ f₁ m q ℓ f hf hℓ)
  have hpl : (offPairs n ℓ₁ f₁ m q ℓ f hf hℓ).length = Bh m q + 1 := by simp [offPairs]
  have horc : orcCount (offP n ℓ₁ f₁ m q ℓ f) = q + 2 := offProg_orc n ℓ₁ f₁ m q ℓ f
  have hPL : (offP n ℓ₁ f₁ m q ℓ f).length = offL n ℓ₁ f₁ m q ℓ f := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact uncontrolled_append (uncontrolled_append u1 hcp.1.uncontrolled) u2
  · unfold offCirc
    rw [queryCount_append, queryCount_append, hcp.1.queryCount]
    have := q1.trans horc.le; have := q2.trans horc.le; omega
  · unfold offCirc
    rw [gateCount_append, gateCount_append, hcp.1.gateCount]
    have := offLen_le q n ℓ m
    rw [hPL, hL] at g1 g2
    have := hcp.2
    omega
  · intro w θ z hz
    have hMo := memOracle_classical n ℓ f w θ
    have hpairs : ∀ pr ∈ offPairs n ℓ₁ f₁ m q ℓ f hf hℓ, pr.1.val < n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f ∧
        n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f ≤ pr.2.val := by
      intro pr hpr
      simp only [offPairs, List.mem_cons, List.mem_ofFn] at hpr
      rcases hpr with rfl | ⟨t, rfl⟩
      · exact ⟨hsbl, by simp⟩
      · exact ⟨offSrc_lt n ℓ₁ f₁ m q ℓ f hf hℓ _, by simp only [offHw_val]; omega⟩
    have hne : ∀ pr ∈ offPairs n ℓ₁ f₁ m q ℓ f hf hℓ, pr.1 ≠ pr.2 := by
      intro pr hpr e
      have := hpairs pr hpr; rw [e] at this; omega
    have himpl := ((impl_compileO (offM n ℓ₁ f₁ m q ℓ f) (Owt n ℓ f w θ) _ hMo
      (offP n ℓ₁ f₁ m q ℓ f) (n * ℓ₁)).append
      (ImplAt.of_impl (impl_copyList (a := n * ℓ + 1) (offPairs n ℓ₁ f₁ m q ℓ f hf hℓ) hne) _)).append
      (impl_compileRevO (offM n ℓ₁ f₁ m q ℓ f) (Owt n ℓ f w θ) _ hMo (offP n ℓ₁ f₁ m q ℓ f) (n * ℓ₁))
    let z1 := runPO (offM n ℓ₁ f₁ m q ℓ f) (Owt n ℓ f w θ) (offP n ℓ₁ f₁ m q ℓ f) (n * ℓ₁) z
    let z2 := cpL (offPairs n ℓ₁ f₁ m q ℓ f hf hℓ) z1
    let z' := runRevO (offM n ℓ₁ f₁ m q ℓ f) (Owt n ℓ f w θ) (offP n ℓ₁ f₁ m q ℓ f) (n * ℓ₁) z2
    refine ⟨z', ?_, ?_⟩
    · unfold offCirc
      rw [himpl z]
      rfl
    let σ := svalO (Owt n ℓ f w θ) (n * ℓ₁) (offP n ℓ₁ f₁ m q ℓ f) (toN z)
    have hz1v : ∀ v : Fin (offM n ℓ₁ f₁ m q ℓ f), z1 v = σ v.val := fun v =>
      compile_semO _ (n * ℓ₁) _ _ (by simp only [hPL, offM]; omega) z hz v
    have hnd : ((offPairs n ℓ₁ f₁ m q ℓ f hf hℓ).map Prod.snd).Nodup := by
      simp only [offPairs, List.map_cons, List.nodup_cons, List.map_ofFn]
      refine ⟨?_, ?_⟩
      · rw [List.mem_ofFn]
        rintro ⟨t, ht⟩
        simp only [Function.comp_apply] at ht
        have := congrArg Fin.val ht
        simp only [offHw_val, offSw_val] at this; omega
      · rw [List.nodup_ofFn]
        exact (offHw n ℓ₁ f₁ m q ℓ f).injective
    have hsrc : ∀ pr ∈ offPairs n ℓ₁ f₁ m q ℓ f hf hℓ, ∀ pr' ∈ offPairs n ℓ₁ f₁ m q ℓ f hf hℓ,
        pr.1 ≠ pr'.2 := by
      intro pr hpr pr' hpr' e
      have := (hpairs pr hpr).1; have := (hpairs pr' hpr').2; rw [e] at *; omega
    have hz2low : AgreeB (n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f) z2 z1 := by
      intro v hv
      show cpL _ z1 v = z1 v
      rw [cpL_apply _ hnd hsrc]
      have : (offPairs n ℓ₁ f₁ m q ℓ f hf hℓ).find? (fun pr => decide (pr.2 = v)) = none := by
        rw [List.find?_eq_none]
        intro pr hpr hpv
        simp only [decide_eq_true_eq] at hpv
        have := (hpairs pr hpr).2
        rw [hpv] at this; omega
      rw [this]
    have hz'low : ∀ v : Fin (offM n ℓ₁ f₁ m q ℓ f), v.val < n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f →
        z' v = z v := by
      intro v hv
      have := runRevO_agree (offM n ℓ₁ f₁ m q ℓ f) (Owt n ℓ f w θ) (offP n ℓ₁ f₁ m q ℓ f) (n * ℓ₁)
        (n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f) (by rw [hPL]) z2 z1 hz2low v hv
      show runRevO _ _ _ _ z2 v = z v
      rw [this, runRevO_runPO]
    have hz'high : ∀ v : Fin (offM n ℓ₁ f₁ m q ℓ f), n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f ≤ v.val →
        z' v = z2 v := fun v hv => runRevO_high _ _ _ (n * ℓ₁) z2 v (by rw [hPL]; exact hv)
    have hhigh0 : ∀ v : Fin (offM n ℓ₁ f₁ m q ℓ f), n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f ≤ v.val →
        z1 v = false := by
      intro v hv; rw [hz1v]; exact svalO_beyond _ _ _ _ _ (by rw [hPL]; exact hv)
    have hpbits : pBits n ℓ₁ σ = z ∘ offPin n ℓ₁ f₁ m q ℓ f := by
      funext idx
      simp only [pBits, Function.comp_apply]
      show svalO _ _ _ _ idx.val = _
      rw [svalO_lt _ _ _ _ idx.isLt]
      have hlt : idx.val < offM n ℓ₁ f₁ m q ℓ f := by simp only [offM]; omega
      simp only [toN, dif_pos hlt]
      rfl
    have hsp := (hspec w θ).2.2.2.2 [] (toN z)
    simp only [List.append_nil] at hsp
    obtain ⟨hsbv, T', hH', hb', hrun⟩ := hsp
    change σ _ = _ at hsbv
    rw [hpbits] at hsbv hrun
    refine ⟨?_, ?_, ?_⟩
    · intro v hv1 hv2
      by_cases hvl : v.val < n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f
      · exact hz'low v hvl
      · exfalso
        by_cases hvs : v.val = n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f
        · exact hv1 (Fin.ext (by simp [hvs]))
        · apply hv2
          have := v.isLt
          refine ⟨⟨v.val - (n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f + 1), by simp only [offM] at this; omega⟩, ?_⟩
          apply Fin.ext; simp; omega
    · rw [hz'high _ (by simp only [offHw_val, offSw_val]; omega)]
      show cpL _ z1 _ = _
      rw [cpL_apply _ hnd hsrc]
      simp only [offPairs, List.find?_cons, decide_true]
      rw [hhigh0 _ (by simp only [offHw_val, offSw_val]; omega), Bool.false_xor, hz1v]
      exact hsbv
    · have hbits : (z' ∘ offHw n ℓ₁ f₁ m q ℓ f) =
          fun t : Fin (Bh m q) => σ ((offProg n ℓ₁ f₁ m q ℓ f).2.1.getD (Bh m q - 1 - t.val) 0) := by
        funext t
        simp only [Function.comp_apply]
        rw [hz'high _ (by simp only [offHw_val, offSw_val]; omega)]
        show cpL _ z1 _ = _
        rw [cpL_apply _ hnd hsrc]
        have hfind : (offPairs n ℓ₁ f₁ m q ℓ f hf hℓ).find?
            (fun pr => decide (pr.2 = offHw n ℓ₁ f₁ m q ℓ f t)) =
            some (⟨(offProg n ℓ₁ f₁ m q ℓ f).2.1.getD (Bh m q - 1 - t.val) 0, by
              have := offSrc_lt n ℓ₁ f₁ m q ℓ f hf hℓ (Bh m q - 1 - t.val)
              show _ < n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f + 1 + Bh m q
              omega⟩, offHw n ℓ₁ f₁ m q ℓ f t) := by
          simp only [offPairs, List.find?_cons]
          have hne' : ¬ (offSw n ℓ₁ f₁ m q ℓ f = offHw n ℓ₁ f₁ m q ℓ f t) := by
            intro e; have := congrArg Fin.val e; simp only [offHw_val, offSw_val] at this; omega
          simp only [hne', decide_false]
          rw [List.find?_ofFn_eq_some]
          refine ⟨by simp, t, rfl, fun j hj => ?_⟩
          simp only [decide_eq_true_eq]
          intro e
          have := (offHw n ℓ₁ f₁ m q ℓ f).injective e
          rw [this] at hj; exact lt_irrefl _ hj
        rw [hfind]
        simp only
        rw [hhigh0 _ (by simp only [offHw_val, offSw_val]; omega), Bool.false_xor, hz1v]
      rw [hbits, ← hrun]
      have hHl := (hspec w θ).2.2.1
      have hnum : bitsToNat (fun t : Fin (Bh m q) =>
          σ ((offProg n ℓ₁ f₁ m q ℓ f).2.1.getD (Bh m q - 1 - t.val) 0)) =
          numVal σ (offProg n ℓ₁ f₁ m q ℓ f).2.1 := by
        rw [numVal_eq_bval, ← bval_rev_bits]
        congr 1
        apply List.ext_getElem
        · simp [hHl]
        · intro i h1 h2
          simp only [List.length_map, List.length_range] at h1
          simp only [List.getElem_map, List.getElem_range]
          rw [dif_pos (by omega), show Bh m q - 1 - (Bh m q - 1 - i) = i by omega,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hHl]; exact h1),
            Option.getD_some]
      have hX : |2 * T'| < 2 ^ (Bh m q - 1) := by
        rw [abs_mul, abs_two, show Bh m q - 1 = m + q + 1 by simp [Bh], pow_succ]
        linarith
      have hex := exact_of_modEq σ (offProg n ℓ₁ f₁ m q ℓ f).2.1 (Bh m q) hHl (by simp [Bh]) _ hX hH'
      unfold QuantumLTF.Membership.fpVal
      rw [hnum]
      have hR : ((numVal σ (offProg n ℓ₁ f₁ m q ℓ f).2.1 : ℕ) : ℝ) =
          ((2 * T' : ℤ) : ℝ) + 2 ^ (Bh m q - 1) := by exact_mod_cast hex
      rw [hR]
      have h2 : (2 : ℝ) ^ (m + q + 2) / 2 = 2 ^ (Bh m q - 1) := by
        rw [show Bh m q - 1 = m + q + 1 by simp [Bh], pow_succ]; ring
      rw [h2]
      push_cast
      rw [pow_succ]
      field_simp
      ring

end OffF

end LTFC

-- ===== module Bennett =====

/-! General compute–copy–uncompute wrapper for oracle programs. -/

open QAlgorithms

namespace LTFC

section Bennett

variable {K : ℕ} (B : ℕ) (P : List (OIns K)) (outs : List ℕ)

abbrev bM : ℕ := B + P.length + outs.length

def bOut (t : Fin outs.length) : Fin (bM B P outs) := ⟨B + P.length + t.val, by simp [bM]⟩

def bPairs (hout : ∀ v ∈ outs, v < B + P.length) : List (Fin (bM B P outs) × Fin (bM B P outs)) :=
  List.ofFn (fun t : Fin outs.length =>
    ((⟨outs[t.val], by have := hout _ (List.getElem_mem t.isLt); simp only [bM]; omega⟩ :
      Fin (bM B P outs)), bOut B P outs t))

noncomputable def bCirc (hout : ∀ v ∈ outs, v < B + P.length) :
    OracleCircuit G12 (fun _ : Fin 1 => K + 1) (bM B P outs) :=
  compileO (bM B P outs) P B ++ copyList (bPairs B P outs hout) ++ compileRevO (bM B P outs) P B

theorem bennett (hout : ∀ v ∈ outs, v < B + P.length) :
    QuantumLTF.Membership.Uncontrolled (bCirc B P outs hout) ∧
    (bCirc B P outs hout).queryCount 0 ≤ 2 * orcCount P ∧
    (bCirc B P outs hout).gateCount ≤ 20 * P.length + outs.length ∧
    ∀ (O : (Fin K → Bool) → Bool) (Mo : Matrix (Qubits (K + 1)) (Qubits (K + 1)) ℂ),
      IsClassicalOracle O Mo → ∀ z : Qubits (bM B P outs), (∀ v : Fin (bM B P outs), B ≤ v.val → z v = false) →
      ∃ z' : Qubits (bM B P outs), ((bCirc B P outs hout).unitary fun _ => Mo).mulVec (bv z) = bv z' ∧
        (∀ v : Fin (bM B P outs), v.val < B + P.length → z' v = z v) ∧
        ∀ t : Fin outs.length, z' (bOut B P outs t) = svalO O B P (toN z) outs[t.val] := by
  obtain ⟨u1, g1, q1, u2, g2, q2⟩ := counts_compileO (K := K) (bM B P outs) P B
  have hcp := copyList_counts (a := K + 1) (bPairs B P outs hout)
  have hpl : (bPairs B P outs hout).length = outs.length := by simp [bPairs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact uncontrolled_append (uncontrolled_append u1 hcp.1.uncontrolled) u2
  · unfold bCirc
    rw [queryCount_append, queryCount_append, hcp.1.queryCount]; omega
  · unfold bCirc
    rw [gateCount_append, gateCount_append, hcp.1.gateCount]
    have := hcp.2; omega
  · intro O Mo hMo z hz
    have hpairs : ∀ pr ∈ bPairs B P outs hout, pr.1.val < B + P.length ∧ B + P.length ≤ pr.2.val := by
      intro pr hpr
      simp only [bPairs, List.mem_ofFn] at hpr
      obtain ⟨t, rfl⟩ := hpr
      exact ⟨hout _ (List.getElem_mem t.isLt), by simp [bOut]⟩
    have hne : ∀ pr ∈ bPairs B P outs hout, pr.1 ≠ pr.2 := by
      intro pr hpr e
      have := hpairs pr hpr; rw [e] at this; omega
    have himpl := ((impl_compileO (bM B P outs) O _ hMo P B).append
      (ImplAt.of_impl (impl_copyList (a := K + 1) (bPairs B P outs hout) hne) _)).append
      (impl_compileRevO (bM B P outs) O _ hMo P B)
    let z1 := runPO (bM B P outs) O P B z
    let z2 := cpL (bPairs B P outs hout) z1
    let z' := runRevO (bM B P outs) O P B z2
    refine ⟨z', ?_, ?_⟩
    · unfold bCirc; rw [himpl z]; rfl
    let σ := svalO O B P (toN z)
    have hz1v : ∀ v : Fin (bM B P outs), z1 v = σ v.val := fun v =>
      compile_semO _ B _ _ (by simp only [bM]; omega) z hz v
    have hnd : ((bPairs B P outs hout).map Prod.snd).Nodup := by
      simp only [bPairs, List.map_ofFn]
      rw [List.nodup_ofFn]
      intro t t' h
      simp only [Function.comp_apply, bOut, Fin.mk.injEq] at h
      exact Fin.ext (by omega)
    have hsrc : ∀ pr ∈ bPairs B P outs hout, ∀ pr' ∈ bPairs B P outs hout, pr.1 ≠ pr'.2 := by
      intro pr hpr pr' hpr' e
      have := (hpairs pr hpr).1; have := (hpairs pr' hpr').2; rw [e] at *; omega
    have hz2low : AgreeB (B + P.length) z2 z1 := by
      intro v hv
      show cpL _ z1 v = z1 v
      rw [cpL_apply _ hnd hsrc]
      have : (bPairs B P outs hout).find? (fun pr => decide (pr.2 = v)) = none := by
        rw [List.find?_eq_none]
        intro pr hpr hpv
        simp only [decide_eq_true_eq] at hpv
        have := (hpairs pr hpr).2
        rw [hpv] at this; omega
      rw [this]
    refine ⟨?_, ?_⟩
    · intro v hv
      have := runRevO_agree (bM B P outs) O P B (B + P.length) le_rfl z2 z1 hz2low v hv
      show runRevO _ _ _ _ z2 v = z v
      rw [this, runRevO_runPO]
    · intro t
      show runRevO _ _ _ _ z2 _ = _
      rw [runRevO_high _ _ _ B z2 _ (by simp [bOut])]
      show cpL _ z1 _ = _
      rw [cpL_apply _ hnd hsrc]
      have hfind : (bPairs B P outs hout).find? (fun pr => decide (pr.2 = bOut B P outs t)) =
          some ((⟨outs[t.val], by have := hout _ (List.getElem_mem t.isLt); simp only [bM]; omega⟩ :
            Fin (bM B P outs)), bOut B P outs t) := by
        simp only [bPairs]
        rw [List.find?_ofFn_eq_some]
        refine ⟨by simp, t, rfl, fun j hj => ?_⟩
        simp only [decide_eq_true_eq, bOut, Fin.mk.injEq]
        omega
      rw [hfind]
      simp only
      rw [hz1v, hz1v]
      have h0 : σ (bOut B P outs t).val = false :=
        svalO_beyond O B P (toN z) (bOut B P outs t).val (by simp [bOut])
      rw [h0, Bool.false_xor]

end Bennett

end LTFC

-- ===== module Test =====

/-! The endpoint test: queries at `±2^m • p`. -/

open QAlgorithms

namespace LTFC

section Test

variable (n ℓ₁ f₁ m q ℓ f : ℕ)

def testProg : List ℕ × List (OIns (n * ℓ)) :=
  let B := n * ℓ₁
  let r1 := addAllL B ℓ₁ ℓ B (B + 1) (m + q + Ex f₁ q f) B (B + 1) 0 (As0 n ℓ₁ ℓ) (p0 n ℓ₁ ℓ)
  let a1 := queryB B ℓ n r1.1 r1.2
  let r2 := addAllL B ℓ₁ ℓ B (B + 1) (m + q + Ex f₁ q f) (B + 1) B 0 (As0 n ℓ₁ ℓ) a1.2
  let a2 := queryB B ℓ n r2.1 r2.2
  let eqv := emitO B (fun x y => x == y) a1.1 a2.1 a2.2
  ([eqv.1, a1.1], eqv.2)

variable (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)

include hf hℓ in
theorem testProg_spec (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    (testProg n ℓ₁ f₁ m q ℓ f).1.length = 2 ∧
    (∀ v ∈ (testProg n ℓ₁ f₁ m q ℓ f).1, v < n * ℓ₁ + (testProg n ℓ₁ f₁ m q ℓ f).2.length) ∧
    orcCount (testProg n ℓ₁ f₁ m q ℓ f).2 = 2 ∧
    (testProg n ℓ₁ f₁ m q ℓ f).2.length = 2 + 2 * (n * (12 * ℓ)) + 2 * (n * ℓ + 1) + 1 ∧
    HoldsO (Owt n ℓ f w θ) (n * ℓ₁) (testProg n ℓ₁ f₁ m q ℓ f).2 (fun σ =>
      σ ((testProg n ℓ₁ f₁ m q ℓ f).1.getD 1 0) = decide (QuantumLTF.Membership.ltf w θ
        (((2 : ℝ) ^ m) • QuantumLTF.Membership.addrOf n ℓ₁ f₁ (pBits n ℓ₁ σ)) = -1) ∧
      σ ((testProg n ℓ₁ f₁ m q ℓ f).1.getD 0 0) = (σ ((testProg n ℓ₁ f₁ m q ℓ f).1.getD 1 0) ==
        decide (QuantumLTF.Membership.ltf w θ
        ((-((2 : ℝ) ^ m)) • QuantumLTF.Membership.addrOf n ℓ₁ f₁ (pBits n ℓ₁ σ)) = -1))) := by
  set B := n * ℓ₁ with hB
  set O := Owt n ℓ f w θ with hO
  have hp0 : (p0 n ℓ₁ ℓ).length = 2 := rfl
  have hA0 := As0_ok n ℓ₁ ℓ 2 le_rfl
  obtain ⟨e1, l1, o1, v1, h1⟩ := addAllL_spec O B ℓ₁ ℓ n B (B + 1) (m + q + Ex f₁ q f) B (B + 1)
    (As0 n ℓ₁ ℓ) 0 (p0 n ℓ₁ ℓ) (by rw [hA0.1]; omega) le_rfl (by rw [hp0]; exact hA0.2)
    (by rw [hp0]; omega) (by rw [hp0]; omega) (by rw [hp0]; omega) (by rw [hp0]; omega)
  set r1 := addAllL B ℓ₁ ℓ B (B + 1) (m + q + Ex f₁ q f) B (B + 1) 0 (As0 n ℓ₁ ℓ) (p0 n ℓ₁ ℓ)
    with hr1
  have le1 := e1.length_le
  obtain ⟨e2, l2, v2, h2⟩ := queryB_spec B ℓ n O r1.1 r1.2 (fun A hA => (v1 A hA).2) (by omega)
  set a1 := queryB B ℓ n r1.1 r1.2 with ha1
  have le2 := e2.length_le
  have hA0' := As0_ok n ℓ₁ ℓ a1.2.length (by rw [hp0] at le1; omega)
  obtain ⟨e3, l3, o3, v3, h3⟩ := addAllL_spec O B ℓ₁ ℓ n B (B + 1) (m + q + Ex f₁ q f) (B + 1) B
    (As0 n ℓ₁ ℓ) 0 a1.2 (by rw [hA0.1]; omega) le_rfl hA0'.2 (by omega) (by omega) (by omega)
    (by omega)
  set r2 := addAllL B ℓ₁ ℓ B (B + 1) (m + q + Ex f₁ q f) (B + 1) B 0 (As0 n ℓ₁ ℓ) a1.2 with hr2
  have le3 := e3.length_le
  obtain ⟨e4, l4, v4, h4⟩ := queryB_spec B ℓ n O r2.1 r2.2 (fun A hA => (v3 A hA).2) (by omega)
  set a2 := queryB B ℓ n r2.1 r2.2 with ha2
  have le4 := e4.length_le
  obtain ⟨e5, l5, v5, h5⟩ := emitO_spec O B (fun x y => x == y) a1.1 a2.1 a2.2 (by omega) v4
  set eqv := emitO B (fun x y => x == y) a1.1 a2.1 a2.2 with heqv
  have le5 := e5.length_le
  change [eqv.1, a1.1].length = 2 ∧ (∀ v ∈ [eqv.1, a1.1], v < B + eqv.2.length) ∧
    orcCount eqv.2 = 2 ∧ eqv.2.length = _ ∧ HoldsO O B eqv.2 (fun σ => σ ([eqv.1, a1.1].getD 1 0) = _ ∧
      σ ([eqv.1, a1.1].getD 0 0) = _)
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> omega
  · rw [(emitO_bin _ _ _ _ _).orc, queryB_orc, (addAllL_bin _ _ _ _ _ _ _ _ _ _ _).orc, queryB_orc,
      (addAllL_bin _ _ _ _ _ _ _ _ _ _ _).orc]
    simp [p0, orcCount, isOrc]
  · rw [l5, l4, l3, l2, l1, hp0, hA0.1]; ring
  · have H1 := h1.mono (e2.trans (e3.trans (e4.trans e5)))
    have H2 := h2.mono (e3.trans (e4.trans e5))
    have H3 := h3.mono (e4.trans e5)
    have H4 := h4.mono e5
    have hp0h := (p0_holds n ℓ₁ ℓ O).mono (e1.trans (e2.trans (e3.trans (e4.trans e5))))
    refine (((((H1.and H2).and H3).and H4).and h5).and hp0h).imp ?_
    rintro σ ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hz, ho⟩
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    set pv := QuantumLTF.Membership.addrOf n ℓ₁ f₁ (pBits n ℓ₁ σ) with hpv
    have hTb : |(2 : ℤ) ^ (m + q)| ≤ (2 ^ m + 1) * 2 ^ q := by
      rw [abs_of_pos (by positivity), pow_add]
      exact mul_le_mul_of_nonneg_right (by linarith only) (by positivity)
    have hTb' : |-(2 : ℤ) ^ (m + q)| ≤ (2 ^ m + 1) * 2 ^ q := by rw [abs_neg]; exact hTb
    have hR := h1 hz ho (by rw [ho, hz]; rfl)
    have hAR : AddrInv n ℓ₁ f₁ q ℓ f σ r1.1 (2 ^ (m + q)) := by
      intro k hk
      have := hR k (by rw [hA0.1]; exact hk)
      rw [As0_getD n ℓ₁ ℓ k hk, constL_top σ _ _ ℓ hz ho (by omega), hz] at this
      refine this.trans ?_
      unfold Int.ModEq; congr 1; simp only [sgnB, Bool.false_eq_true, if_false, pow_add]; ring
    have haddrR := addr_eq n ℓ₁ f₁ ℓ f (Ex f₁ q f) q m (by simp only [Ex]; omega) hℓ σ r1.1 _ hTb
      (by rw [o1, hA0.1]) (fun k hk => by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [o1, hA0.1]; exact hk),
          Option.getD_some]; exact (v1 _ (List.getElem_mem _)).1) hAR
    have hq1 : (((2 : ℤ) ^ (m + q) : ℤ) : ℝ) / 2 ^ q = (2 : ℝ) ^ m := by
      push_cast; rw [pow_add]; field_simp
    rw [hq1] at haddrR
    have hL := h3 hz ho (by rw [ho, hz]; rfl)
    have hAL : AddrInv n ℓ₁ f₁ q ℓ f σ r2.1 (-2 ^ (m + q)) := by
      intro k hk
      have := hL k (by rw [hA0.1]; exact hk)
      rw [As0_getD n ℓ₁ ℓ k hk, constL_top σ _ _ ℓ hz ho (by omega), ho] at this
      refine this.trans ?_
      unfold Int.ModEq; congr 1; simp only [sgnB, if_true, pow_add]; ring
    have haddrL := addr_eq n ℓ₁ f₁ ℓ f (Ex f₁ q f) q m (by simp only [Ex]; omega) hℓ σ r2.1 _ hTb'
      (by rw [o3, hA0.1]) (fun k hk => by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [o3, hA0.1]; exact hk),
          Option.getD_some]; exact (v3 _ (List.getElem_mem _)).1) hAL
    have hq2 : ((-(2 : ℤ) ^ (m + q) : ℤ) : ℝ) / 2 ^ q = -(2 : ℝ) ^ m := by
      push_cast; rw [pow_add]; field_simp
    rw [hq2] at haddrL
    have e1' : σ a1.1 = decide (QuantumLTF.Membership.ltf w θ (((2 : ℝ) ^ m) • pv) = -1) := by
      rw [h2, hO, Owt, haddrR]
    refine ⟨e1', ?_⟩
    show σ eqv.1 = (σ a1.1 == _)
    rw [h5, e1', h4, hO, Owt, haddrL]

end Test

end LTFC

-- ===== module OutProg =====

/-! Output formatting: exact fixed-point conversion with sign, multiplexing, copy block. -/

open QAlgorithms

namespace LTFC

section OutB

variable {K : ℕ} (O : (Fin K → Bool) → Bool) (B ℓo : ℕ)

def shlX (zw : ℕ) (X : List ℕ) (e : ℕ) : List ℕ :=
  ((List.replicate e zw) ++ X ++ List.replicate ℓo zw).take ℓo

theorem shlX_length (zw : ℕ) (X : List ℕ) (e : ℕ) : (shlX ℓo zw X e).length = ℓo := by
  simp [shlX]; omega

theorem shlX_val (σ : ℕ → Bool) (zw : ℕ) (X : List ℕ) (e : ℕ) (hz : σ zw = false) :
    numVal σ (shlX ℓo zw X e) = (2 ^ e * numVal σ X) % 2 ^ ℓo := by
  rw [numVal_eq_bval, shlX, List.map_take, bval_take, List.map_append, List.map_append,
    bval_append, bval_append]
  simp [List.map_replicate, hz, bval_replicate_false, numVal_eq_bval]

/-- `A ± 2^e (2 X - 2^L') mod 2^ℓo`. -/
def addScaledX (zw ow : ℕ) (A X : List ℕ) (L' e negv negb : ℕ) : BldO K (List ℕ) := fun p =>
  let r1 := csub B A (shlX ℓo zw X (e + 1)) negv p
  csub B r1.1 (constL zw ow ℓo (2 ^ (e + L'))) negb r1.2

def PX (σ : ℕ → Bool) (X : List ℕ) (L' : ℕ) : ℤ := 2 * (numVal σ X : ℤ) - 2 ^ L'

theorem addScaledX_spec (zw ow : ℕ) (A X : List ℕ) (L' e negv negb : ℕ) (p : List (OIns K))
    (hA : A.length = ℓo) (hAv : ∀ v ∈ A, v < B + p.length) (hX : ∀ v ∈ X, v < B + p.length)
    (hzw : zw < B + p.length) (how : ow < B + p.length) (hnv : negv < B + p.length)
    (hnb : negb < B + p.length) :
    ExtL p (addScaledX B ℓo zw ow A X L' e negv negb p).2 ∧
    (addScaledX B ℓo zw ow A X L' e negv negb p).2.length = p.length + 12 * ℓo ∧
    (addScaledX B ℓo zw ow A X L' e negv negb p).1.length = ℓo ∧
    (∀ v ∈ (addScaledX B ℓo zw ow A X L' e negv negb p).1,
      v < B + (addScaledX B ℓo zw ow A X L' e negv negb p).2.length) ∧
    HoldsO O B (addScaledX B ℓo zw ow A X L' e negv negb p).2 (fun σ =>
      σ zw = false → σ ow = true → σ negb = !σ negv →
      ((numVal σ (addScaledX B ℓo zw ow A X L' e negv negb p).1 : ℕ) : ℤ) ≡
        (numVal σ A : ℤ) + sgnB (σ negv) * 2 ^ e * PX σ X L' [ZMOD 2 ^ ℓo]) := by
  have hshv : ∀ v ∈ shlX ℓo zw X (e + 1), v < B + p.length := by
    intro v hv
    have := List.mem_of_mem_take hv
    simp only [List.mem_append, List.mem_replicate] at this
    rcases this with (⟨_, rfl⟩ | h) | ⟨_, rfl⟩
    · exact hzw
    · exact hX v h
    · exact hzw
  obtain ⟨e1, l1, o1, v1, h1⟩ := csub_spec O B A (shlX ℓo zw X (e + 1)) negv p
    (by rw [hA, shlX_length]) hAv hshv hnv
  set r1 := csub B A (shlX ℓo zw X (e + 1)) negv p with hr1
  have hle := e1.length_le
  obtain ⟨e2, l2, o2, v2, h2⟩ := csub_spec O B r1.1 (constL zw ow ℓo (2 ^ (e + L'))) negb r1.2
    (by rw [o1, hA, constL_length]) v1
    (fun v hv => by rcases constL_mem _ _ _ _ v hv with h | h <;> omega) (by omega)
  refine ⟨e1.trans e2, ?_, ?_, v2, ?_⟩
  · show (csub B r1.1 _ negb r1.2).2.length = _
    rw [l2, l1, o1, hA]; ring
  · show (csub B r1.1 _ negb r1.2).1.length = _
    rw [o2, o1, hA]
  · refine ((h1.mono e2).and h2).imp ?_
    rintro σ ⟨h1, h2⟩ hz ho hnb'
    show ((numVal σ (csub B r1.1 _ negb r1.2).1 : ℕ) : ℤ) ≡ _ [ZMOD _]
    rw [o1, hA] at h2
    rw [hA] at h1
    refine h2.trans ?_
    have hc : (numVal σ (constL zw ow ℓo (2 ^ (e + L'))) : ℤ) ≡ 2 ^ (e + L') [ZMOD 2 ^ ℓo] := by
      rw [numVal_eq_bval, constL_val σ zw ow hz ho]
      have := natmod_modEq (2 ^ (e + L')) ℓo
      simpa using this
    have hs : (numVal σ (shlX ℓo zw X (e + 1)) : ℤ) ≡ 2 ^ (e + 1) * numVal σ X [ZMOD 2 ^ ℓo] := by
      rw [shlX_val ℓo σ zw X (e + 1) hz]
      have := natmod_modEq (2 ^ (e + 1) * numVal σ X) ℓo
      simpa using this
    have key : (numVal σ A : ℤ) + sgnB (σ negv) * 2 ^ e * PX σ X L' =
        ((numVal σ A : ℤ) + sgnB (σ negv) * (2 ^ (e + 1) * numVal σ X)) +
          (-sgnB (σ negv)) * 2 ^ (e + L') := by
      simp only [PX, pow_add]; ring
    rw [key, hnb']
    cases hnv' : σ negv
    · simp only [hnv', sgnB, Bool.not_false, if_true, Bool.false_eq_true, if_false] at h1 ⊢
      refine Int.ModEq.add ?_ ?_
      · refine h1.trans ?_
        exact Int.ModEq.add_left _ (by simpa using hs)
      · have := hc.neg; simpa using this
    · simp only [hnv', sgnB, Bool.not_true, if_true, Bool.false_eq_true, if_false] at h1 ⊢
      refine Int.ModEq.add ?_ ?_
      · refine h1.trans ?_
        have := hs.neg
        simpa using Int.ModEq.add_left _ this
      · simpa using hc

/-- Zip two lists with a binary instruction. -/
def zipE2 (f : Bool → Bool → Bool) (X Y : List ℕ) : BldO K (List ℕ) :=
  fun p => ((List.range (List.zipWith (fun x y => (⟨f, x, y⟩ : Instr)) X Y).length).map
      (fun i => B + p.length + i),
    p ++ (List.zipWith (fun x y => (⟨f, x, y⟩ : Instr)) X Y).map OIns.bin)

theorem zipE2_spec (f : Bool → Bool → Bool) (X Y : List ℕ) (p : List (OIns K))
    (hl : X.length = Y.length)
    (hX : ∀ x ∈ X, x < B + p.length) (hY : ∀ y ∈ Y, y < B + p.length) :
    ExtL p (zipE2 B f X Y p).2 ∧ (zipE2 B f X Y p).2.length = p.length + X.length ∧
    (zipE2 B f X Y p).1.length = X.length ∧
    (∀ v ∈ (zipE2 B f X Y p).1, v < B + (zipE2 B f X Y p).2.length) ∧
    HoldsO O B (zipE2 B f X Y p).2
      (fun σ => (zipE2 B f X Y p).1.map σ = List.zipWith (fun x y => f (σ x) (σ y)) X Y) := by
  refine ⟨ExtL.app _ _, by simp [zipE2, hl], by simp [zipE2, hl], ?_, ?_⟩
  · intro v hv
    simp only [zipE2, List.mem_map, List.mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    simp only [zipE2, List.length_append, List.length_map]; omega
  · have := holdsO_list O B p (List.zipWith (fun x y => (⟨f, x, y⟩ : Instr)) X Y) (by
      intro i hi
      simp only [List.getElem_zipWith]
      simp only [List.length_zipWith] at hi
      have h1 := hX X[i] (List.getElem_mem (by omega))
      have h2 := hY Y[i] (List.getElem_mem (by omega))
      constructor <;> omega)
    refine this.imp ?_
    intro σ h
    apply List.ext_getElem
    · simp [zipE2]
    · intro i h1 h2
      have := h i (by simpa [zipE2] using h1)
      simpa [zipE2] using this

/-- `out_j = if e then X_j else Y_j`. -/
def muxL (e : ℕ) (X Y : List ℕ) : BldO K (List ℕ) := fun p =>
  let r1 := mapE B (fun x e => x && e) X e p
  let r2 := mapE B (fun y e => !e && y) Y e r1.2
  zipE2 B (· || ·) r1.1 r2.1 r2.2

theorem muxL_spec (e : ℕ) (X Y : List ℕ) (p : List (OIns K)) (hl : X.length = Y.length)
    (he : e < B + p.length) (hX : ∀ x ∈ X, x < B + p.length) (hY : ∀ y ∈ Y, y < B + p.length) :
    ExtL p (muxL B e X Y p).2 ∧ (muxL B e X Y p).2.length = p.length + 3 * X.length ∧
    (muxL B e X Y p).1.length = X.length ∧
    (∀ v ∈ (muxL B e X Y p).1, v < B + (muxL B e X Y p).2.length) ∧
    HoldsO O B (muxL B e X Y p).2
      (fun σ => (muxL B e X Y p).1.map σ = if σ e then X.map σ else Y.map σ) := by
  obtain ⟨e1, l1, o1, v1, h1⟩ := mapE_spec O B (fun x e => x && e) X e p hX he
  set r1 := mapE B (fun x e => x && e) X e p with hr1
  have le1 := e1.length_le
  obtain ⟨e2, l2, o2, v2, h2⟩ := mapE_spec O B (fun y e => !e && y) Y e r1.2
    (fun y hy => by have := hY y hy; omega) (by omega)
  set r2 := mapE B (fun y e => !e && y) Y e r1.2 with hr2
  have le2 := e2.length_le
  obtain ⟨e3, l3, o3, v3, h3⟩ := zipE2_spec O B (· || ·) r1.1 r2.1 r2.2 (by rw [o1, o2, hl])
    (fun v hv => by have := v1 v hv; omega) v2
  refine ⟨e1.trans (e2.trans e3), ?_, ?_, v3, ?_⟩
  · show (zipE2 B _ r1.1 r2.1 r2.2).2.length = _
    rw [l3, l2, l1, o1, hl]; ring
  · show (zipE2 B _ r1.1 r2.1 r2.2).1.length = _
    rw [o3, o1]
  · refine (((h1.mono (e2.trans e3)).and (h2.mono e3)).and h3).imp ?_
    rintro σ ⟨⟨h1, h2⟩, h3⟩
    show (zipE2 B _ r1.1 r2.1 r2.2).1.map σ = _
    rw [h3]
    apply List.ext_getElem
    · simp only [List.length_zipWith, o1, o2, hl, min_self]; split_ifs <;> simp [hl]
    · intro i hi1 hi2
      simp only [List.length_zipWith] at hi1
      have hi1' : i < r1.1.length := by omega
      have hi2' : i < r2.1.length := by omega
      simp only [List.getElem_zipWith]
      have g1 := congrArg (fun l => l[i]?) h1
      have g2 := congrArg (fun l => l[i]?) h2
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi1', List.getElem?_eq_getElem hi2',
        Option.map_some] at g1 g2
      have hiX : i < X.length := by rw [← o1]; exact hi1'
      have hiY : i < Y.length := by rw [← o2]; exact hi2'
      rw [List.getElem?_eq_getElem hiX] at g1
      rw [List.getElem?_eq_getElem hiY] at g2
      simp only [Option.map_some, Option.some.injEq] at g1 g2
      rw [g1, g2]
      split_ifs with h
      · simp [h]
      · simp [h]

end OutB

end LTFC

namespace LTFC

/-- MSB-first bits of an LSB-first variable list. -/
def msbBits (σ : ℕ → Bool) (L : ℕ) (X : List ℕ) : Qubits L := fun t => σ (X.getD (L - 1 - t.val) 0)

theorem bitsToNat_msbBits (σ : ℕ → Bool) (X : List ℕ) (L : ℕ) (hX : X.length = L) :
    bitsToNat (msbBits σ L X) = numVal σ X := by
  rw [numVal_eq_bval, ← bval_rev_bits]
  congr 1
  apply List.ext_getElem
  · simp [hX]
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, msbBits]
    rw [dif_pos (by omega), show L - 1 - (L - 1 - i) = i by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hX]; exact h1), Option.getD_some]

theorem fpVal_msbBits (σ : ℕ → Bool) (X : List ℕ) (L f : ℕ) (hX : X.length = L) :
    QuantumLTF.Membership.fpVal L f (msbBits σ L X) = (PX σ X L : ℝ) / 2 ^ (f + 1) := by
  unfold QuantumLTF.Membership.fpVal
  rw [bitsToNat_msbBits σ X L hX, PX]
  push_cast
  rw [pow_succ]
  field_simp

theorem fpVal_out (σ : ℕ → Bool) (A : List ℕ) (ℓo fo : ℕ) (hA : A.length = ℓo) (h1 : 1 ≤ ℓo)
    (X : ℤ) (hX : |X| < 2 ^ (ℓo - 1))
    (h : ((numVal σ A : ℕ) : ℤ) ≡ 2 ^ (ℓo - 1) + X [ZMOD 2 ^ ℓo]) :
    QuantumLTF.Membership.fpVal ℓo fo (msbBits σ ℓo A) = (X : ℝ) / 2 ^ fo := by
  have hex := exact_of_modEq σ A ℓo hA h1 X hX (by rw [add_comm] at h; exact h)
  unfold QuantumLTF.Membership.fpVal
  rw [bitsToNat_msbBits σ A ℓo hA]
  have hR : ((numVal σ A : ℕ) : ℝ) = (X : ℝ) + 2 ^ (ℓo - 1) := by exact_mod_cast hex
  rw [hR]
  have h2 : (2 : ℝ) ^ ℓo / 2 = 2 ^ (ℓo - 1) := by
    rw [show ℓo = (ℓo - 1) + 1 by omega, pow_succ]; simp
  rw [h2]; ring

theorem msbBits_congr (σ : ℕ → Bool) (L : ℕ) (X Y : List ℕ) (h : X.map σ = Y.map σ) :
    msbBits σ L X = msbBits σ L Y := by
  funext t
  simp only [msbBits, List.getD_eq_getElem?_getD]
  have := congrArg (fun l => l[L - 1 - t.val]?) h
  simp only [List.getElem?_map] at this
  cases hx : X[L - 1 - t.val]? <;> cases hy : Y[L - 1 - t.val]? <;> simp_all

end LTFC

namespace LTFC

section OutP

variable {K : ℕ} (O : (Fin K → Bool) → Bool) (B ℓo fo ℓo₃ fo₃ : ℕ)

def outCoords (zw ow sbv nsb eqv : ℕ) (A0 : List ℕ) : List (List ℕ) → BldO K (List (List ℕ))
  | [] => fun p => ([], p)
  | X :: Xs => fun p =>
    let r1 := addScaledX B ℓo zw ow A0 X ℓo₃ (fo - fo₃ - 1) sbv nsb p
    let r2 := muxL B eqv A0 r1.1 r1.2
    let r3 := outCoords zw ow sbv nsb eqv A0 Xs r2.2
    (r2.1 :: r3.1, r3.2)

def sgnS (b : Bool) : ℝ := if b then 1 else -1

theorem outCoords_spec (zw ow sbv nsb eqv : ℕ) (A0 : List ℕ) (hA0 : A0.length = ℓo)
    (hfo : fo₃ + 1 ≤ fo) (hℓo : fo + ℓo₃ + 2 ≤ ℓo) :
    ∀ (Xs : List (List ℕ)) (p : List (OIns K)),
    (∀ X ∈ Xs, X.length = ℓo₃ ∧ ∀ v ∈ X, v < B + p.length) → (∀ v ∈ A0, v < B + p.length) →
    zw < B + p.length → ow < B + p.length → sbv < B + p.length → nsb < B + p.length →
    eqv < B + p.length →
    ExtL p (outCoords B ℓo fo ℓo₃ fo₃ zw ow sbv nsb eqv A0 Xs p).2 ∧
    (outCoords B ℓo fo ℓo₃ fo₃ zw ow sbv nsb eqv A0 Xs p).2.length = p.length + Xs.length * (15 * ℓo) ∧
    (outCoords B ℓo fo ℓo₃ fo₃ zw ow sbv nsb eqv A0 Xs p).1.length = Xs.length ∧
    (∀ A ∈ (outCoords B ℓo fo ℓo₃ fo₃ zw ow sbv nsb eqv A0 Xs p).1, A.length = ℓo ∧
      ∀ v ∈ A, v < B + (outCoords B ℓo fo ℓo₃ fo₃ zw ow sbv nsb eqv A0 Xs p).2.length) ∧
    HoldsO O B (outCoords B ℓo fo ℓo₃ fo₃ zw ow sbv nsb eqv A0 Xs p).2 (fun σ =>
      σ zw = false → σ ow = true → σ nsb = !σ sbv →
      ((numVal σ A0 : ℕ) : ℤ) = 2 ^ (ℓo - 1) →
      ∀ i < Xs.length,
        QuantumLTF.Membership.fpVal ℓo fo (msbBits σ ℓo
          ((outCoords B ℓo fo ℓo₃ fo₃ zw ow sbv nsb eqv A0 Xs p).1.getD i [])) =
        if σ eqv then 0 else
          -(sgnS (σ sbv)) * QuantumLTF.Membership.fpVal ℓo₃ fo₃ (msbBits σ ℓo₃ (Xs.getD i []))) := by
  intro Xs
  induction Xs with
  | nil =>
    intro p _ _ _ _ _ _ _
    refine ⟨ExtL.refl _, by simp [outCoords], by simp [outCoords], by simp [outCoords], ?_⟩
    intro q inp _ _ _ _ i hi; simp at hi
  | cons X Xs ih =>
    intro p hXs hA0v hzw how hsb hnsb heq
    obtain ⟨hXl, hXv⟩ := hXs X List.mem_cons_self
    obtain ⟨e1, l1, o1, v1, h1⟩ := addScaledX_spec O B ℓo zw ow A0 X ℓo₃ (fo - fo₃ - 1) sbv nsb p
      hA0 hA0v hXv hzw how hsb hnsb
    set r1 := addScaledX B ℓo zw ow A0 X ℓo₃ (fo - fo₃ - 1) sbv nsb p with hr1
    have le1 := e1.length_le
    obtain ⟨e2, l2, o2, v2, h2⟩ := muxL_spec O B eqv A0 r1.1 r1.2 (by rw [hA0, o1]) (by omega)
      (fun v hv => by have := hA0v v hv; omega) v1
    set r2 := muxL B eqv A0 r1.1 r1.2 with hr2
    have le2 := e2.length_le
    obtain ⟨e3, l3, o3, v3, h3⟩ := ih r2.2
      (fun X' hX' => ⟨(hXs X' (List.mem_cons_of_mem _ hX')).1, fun v hv => by
        have := (hXs X' (List.mem_cons_of_mem _ hX')).2 v hv; omega⟩)
      (fun v hv => by have := hA0v v hv; omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    set r3 := outCoords B ℓo fo ℓo₃ fo₃ zw ow sbv nsb eqv A0 Xs r2.2 with hr3
    have le3 := e3.length_le
    change ExtL p r3.2 ∧ r3.2.length = p.length + (Xs.length + 1) * (15 * ℓo) ∧
      (r2.1 :: r3.1).length = Xs.length + 1 ∧
      (∀ A ∈ r2.1 :: r3.1, A.length = ℓo ∧ ∀ v ∈ A, v < B + r3.2.length) ∧
      HoldsO O B r3.2 (fun σ => σ zw = false → σ ow = true → σ nsb = !σ sbv →
        ((numVal σ A0 : ℕ) : ℤ) = 2 ^ (ℓo - 1) → ∀ i < Xs.length + 1,
          QuantumLTF.Membership.fpVal ℓo fo (msbBits σ ℓo ((r2.1 :: r3.1).getD i [])) =
          if σ eqv then 0 else
            -(sgnS (σ sbv)) * QuantumLTF.Membership.fpVal ℓo₃ fo₃ (msbBits σ ℓo₃ ((X :: Xs).getD i [])))
    refine ⟨e1.trans (e2.trans e3), by rw [l3, l2, l1, hA0]; ring, by simp [o3], ?_, ?_⟩
    · intro A hA
      rcases List.mem_cons.1 hA with h | h
      · subst h; exact ⟨by rw [o2, hA0], fun v hv => by have := v2 v hv; omega⟩
      · exact v3 A h
    · refine (((h1.mono (e2.trans e3)).and (h2.mono e3)).and h3).imp ?_
      rintro σ ⟨⟨h1, h2⟩, h3⟩ hz ho hnb hA0n i hi
      cases i with
      | succ i => simpa using h3 hz ho hnb hA0n i (by omega)
      | zero =>
        simp only [List.getD_cons_zero]
        by_cases he : σ eqv
        · rw [if_pos he] at h2
          rw [msbBits_congr σ ℓo _ _ h2, if_pos he]
          rw [fpVal_out σ A0 ℓo fo hA0 (by omega) 0 (by simp) (by rw [hA0n]; simp)]
          simp
        · rw [if_neg he] at h2
          rw [msbBits_congr σ ℓo _ _ h2, if_neg he]
          have hP : |PX σ X ℓo₃| ≤ 2 ^ ℓo₃ := by
            have hN := numVal_lt σ X
            rw [hXl] at hN
            have hN' : ((numVal σ X : ℕ) : ℤ) < 2 ^ ℓo₃ := by exact_mod_cast hN
            have hN0 : (0 : ℤ) ≤ ((numVal σ X : ℕ) : ℤ) := by positivity
            unfold PX; rw [abs_le]; constructor <;> linarith
          have hb : |sgnB (σ sbv) * 2 ^ (fo - fo₃ - 1) * PX σ X ℓo₃| < 2 ^ (ℓo - 1) := by
            rw [abs_mul, abs_mul, abs_pow, abs_two]
            have hs : |sgnB (σ sbv)| = 1 := by cases σ sbv <;> simp [sgnB]
            rw [hs, one_mul]
            calc (2 : ℤ) ^ (fo - fo₃ - 1) * |PX σ X ℓo₃| ≤ 2 ^ (fo - fo₃ - 1) * 2 ^ ℓo₃ := by gcongr
              _ = 2 ^ (fo - fo₃ - 1 + ℓo₃) := by rw [pow_add]
              _ < 2 ^ (ℓo - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
          have hm := h1 hz ho hnb
          rw [hA0n] at hm
          rw [fpVal_out σ r1.1 ℓo fo o1 (by omega) _ hb hm, fpVal_msbBits σ X ℓo₃ fo₃ hXl]
          have he2 : (2 : ℝ) ^ fo = 2 ^ (fo - fo₃ - 1) * 2 ^ (fo₃ + 1) := by
            rw [← pow_add]; congr 1; omega
          rw [he2]
          cases σ sbv <;> simp [sgnB, sgnS] <;> field_simp <;> ring

end OutP

end LTFC

namespace LTFC

section OutAll

variable {K : ℕ} (O : (Fin K → Bool) → Bool) (B ℓo fo ℓo₃ fo₃ Bh fhh n : ℕ)

def p0g : List (OIns K) := [.bin ⟨fun _ _ => false, 0, 0⟩, .bin ⟨fun _ _ => true, B, B⟩]

theorem p0g_holds :
    HoldsO O B (p0g (K := K) B) (fun σ => σ B = false ∧ σ (B + 1) = true) := by
  intro q' inp
  constructor
  · have h := svalO_at O B (p0g B ++ q') inp 0 (by simp [p0g])
    rw [Nat.add_zero] at h
    rw [h]
    simp only [p0g, List.cons_append, List.getElem_cons_zero, evalIns]
    split_ifs <;> rfl
  · exact svalO_at_bin O B (p0g B ++ q') inp 1 (by simp [p0g])
      ⟨fun _ _ => true, B, B⟩ (by simp [p0g]) (by show B < B + 1; omega) (by show B < B + 1; omega)

def outSrc (outs : List (List ℕ)) (idx : ℕ) : ℕ :=
  (outs.getD (idx / ℓo) []).getD (ℓo - 1 - idx % ℓo) 0

def outProgR (sbv eqv cv : ℕ) (gtL : List (List ℕ)) (hL : List ℕ) :
    List (List ℕ) × List (OIns K) :=
  let r0 := emitO B (fun x _ => !x) sbv sbv (p0g B)
  let A0 := constL B (B + 1) ℓo (2 ^ (ℓo - 1))
  let K1 := constL B (B + 1) ℓo (2 ^ (ℓo - 1) + 2 ^ fo)
  let ra := outCoords B ℓo fo ℓo₃ fo₃ B (B + 1) sbv r0.1 eqv A0 gtL r0.2
  let rb1 := addScaledX B ℓo B (B + 1) A0 hL Bh (fo - fhh - 1) r0.1 sbv ra.2
  let rb2 := muxL B cv K1 A0 rb1.2
  let rb3 := muxL B eqv rb2.1 rb1.1 rb2.2
  (ra.1 ++ [rb3.1], rb3.2)

def outProg (sbv eqv cv : ℕ) (gtL : List (List ℕ)) (hL : List ℕ) : List (OIns K) :=
  (blockE (K := K) (fun idx : Fin ((n + 1) * ℓo) =>
    (⟨fun a _ => a, outSrc ℓo (outProgR (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh sbv eqv cv gtL hL).1 idx,
      outSrc ℓo (outProgR (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh sbv eqv cv gtL hL).1 idx⟩ : Instr))
    (outProgR (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh sbv eqv cv gtL hL).2).2

def outBc (sbv eqv cv : ℕ) (gtL : List (List ℕ)) (hL : List ℕ) : ℕ :=
  B + (outProgR (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh sbv eqv cv gtL hL).2.length

theorem outProg_spec (sbv eqv cv : ℕ) (gtL : List (List ℕ)) (hL : List ℕ)
    (hsbv : sbv < B) (heqv : eqv < B) (hcv : cv < B) (hgl : gtL.length = n)
    (hgt : ∀ X ∈ gtL, X.length = ℓo₃ ∧ ∀ v ∈ X, v < B) (hhl : hL.length = Bh) (hh : ∀ v ∈ hL, v < B)
    (hfo : fo₃ + 1 ≤ fo) (hfo' : fhh + 1 ≤ fo) (hℓo : fo + ℓo₃ + 2 ≤ ℓo) (hℓo' : fo + Bh + 2 ≤ ℓo) :
    outBc (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh sbv eqv cv gtL hL + (n + 1) * ℓo =
      B + (outProg (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh n sbv eqv cv gtL hL).length ∧
    (outProg (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh n sbv eqv cv gtL hL).length =
      3 + n * (15 * ℓo) + 18 * ℓo + (n + 1) * ℓo ∧
    HoldsO O B (outProg (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh n sbv eqv cv gtL hL) (fun σ =>
      (∀ i < n, QuantumLTF.Membership.fpVal ℓo fo
          (fun t => σ (outBc (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh sbv eqv cv gtL hL + i * ℓo + t.val)) =
        if σ eqv then 0 else
          -(sgnS (σ sbv)) * QuantumLTF.Membership.fpVal ℓo₃ fo₃ (msbBits σ ℓo₃ (gtL.getD i []))) ∧
      QuantumLTF.Membership.fpVal ℓo fo
          (fun t => σ (outBc (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh sbv eqv cv gtL hL + n * ℓo + t.val)) =
        if σ eqv then (if σ cv then 1 else 0) else
          sgnS (σ sbv) * QuantumLTF.Membership.fpVal Bh fhh (msbBits σ Bh hL)) := by
  have hp0 : (p0g (K := K) B).length = 2 := rfl
  obtain ⟨e0, l0, v0, h0⟩ := emitO_spec O B (fun x _ => !x) sbv sbv (p0g B) (by omega) (by omega)
  set r0 := emitO B (fun x _ => !x) sbv sbv (p0g (K := K) B) with hr0
  have le0 := e0.length_le
  set A0 := constL B (B + 1) ℓo (2 ^ (ℓo - 1)) with hA0
  set K1 := constL B (B + 1) ℓo (2 ^ (ℓo - 1) + 2 ^ fo) with hK1
  have hA0l : A0.length = ℓo := constL_length _ _ _ _
  have hK1l : K1.length = ℓo := constL_length _ _ _ _
  have hcv' : ∀ (L c : ℕ) (len : ℕ), 2 ≤ len → ∀ v ∈ constL B (B + 1) L c, v < B + len := by
    intro L c len hl v hv; rcases constL_mem _ _ _ _ v hv with h | h <;> omega
  obtain ⟨ea, la, oa, va, ha⟩ := outCoords_spec O B ℓo fo ℓo₃ fo₃ B (B + 1) sbv r0.1 eqv A0 hA0l
    hfo hℓo gtL r0.2 (fun X hX => ⟨(hgt X hX).1, fun v hv => by have := (hgt X hX).2 v hv; omega⟩)
    (hcv' _ _ _ (by rw [hp0] at le0; omega)) (by omega) (by omega) (by omega) v0 (by omega)
  set ra := outCoords B ℓo fo ℓo₃ fo₃ B (B + 1) sbv r0.1 eqv A0 gtL r0.2 with hra
  have lea := ea.length_le
  obtain ⟨eb1, lb1, ob1, vb1, hb1⟩ := addScaledX_spec O B ℓo B (B + 1) A0 hL Bh (fo - fhh - 1)
    r0.1 sbv ra.2 hA0l (hcv' _ _ _ (by rw [hp0] at le0; omega))
    (fun v hv => by have := hh v hv; omega) (by omega) (by omega) (by omega) (by omega)
  set rb1 := addScaledX B ℓo B (B + 1) A0 hL Bh (fo - fhh - 1) r0.1 sbv ra.2 with hrb1
  have leb1 := eb1.length_le
  obtain ⟨eb2, lb2, ob2, vb2, hb2⟩ := muxL_spec O B cv K1 A0 rb1.2 (by rw [hK1l, hA0l]) (by omega)
    (hcv' _ _ _ (by rw [hp0] at le0; omega)) (hcv' _ _ _ (by rw [hp0] at le0; omega))
  set rb2 := muxL B cv K1 A0 rb1.2 with hrb2
  have leb2 := eb2.length_le
  obtain ⟨eb3, lb3, ob3, vb3, hb3⟩ := muxL_spec O B eqv rb2.1 rb1.1 rb2.2 (by rw [ob2, ob1, hK1l])
    (by omega) vb2 (fun v hv => by have := vb1 v hv; omega)
  set rb3 := muxL B eqv rb2.1 rb1.1 rb2.2 with hrb3
  have leb3 := eb3.length_le
  have hR : outProgR (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh sbv eqv cv gtL hL = (ra.1 ++ [rb3.1], rb3.2) := rfl
  set outs := ra.1 ++ [rb3.1] with houts
  have houtsv : ∀ idx, outSrc ℓo outs idx < B + rb3.2.length := by
    intro idx
    unfold outSrc
    rw [List.getD_eq_getElem?_getD]
    cases h : (outs.getD (idx / ℓo) [])[ℓo - 1 - idx % ℓo]? with
    | none => simp only [Option.getD_none]; omega
    | some v =>
      simp only [Option.getD_some]
      have hmem : v ∈ outs.getD (idx / ℓo) [] := List.mem_of_getElem? h
      rw [List.getD_eq_getElem?_getD] at hmem
      cases h2 : outs[idx / ℓo]? with
      | none => rw [h2] at hmem; simp at hmem
      | some A =>
        rw [h2] at hmem
        simp only [Option.getD_some] at hmem
        have hA := List.mem_of_getElem? h2
        rw [houts, List.mem_append, List.mem_singleton] at hA
        rcases hA with hA | rfl
        · have := (va A hA).2 v hmem; omega
        · exact vb3 v hmem
  obtain ⟨ec, lc, hc⟩ := blockE_spec O B (K := K) (fun idx : Fin ((n + 1) * ℓo) =>
    (⟨fun a _ => a, outSrc ℓo outs idx, outSrc ℓo outs idx⟩ : Instr)) rb3.2
    (fun idx => ⟨houtsv _, houtsv _⟩)
  have hP : outProg (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh n sbv eqv cv gtL hL = (blockE (K := K)
      (fun idx : Fin ((n + 1) * ℓo) =>
        (⟨fun a _ => a, outSrc ℓo outs idx, outSrc ℓo outs idx⟩ : Instr)) rb3.2).2 := by
    simp only [outProg, hR]
  have hBc : outBc (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh sbv eqv cv gtL hL = B + rb3.2.length := by
    simp only [outBc, hR]
  rw [hP, hBc]
  refine ⟨by rw [lc]; ring, ?_, ?_⟩
  · rw [lc, lb3, lb2, lb1, la, l0, hp0, ob2, hK1l, hgl]; ring
  · have e06 := (e0.trans (ea.trans (eb1.trans (eb2.trans (eb3.trans ec)))))
    have H0 := h0.mono (ea.trans (eb1.trans (eb2.trans (eb3.trans ec))))
    have Ha := ha.mono (eb1.trans (eb2.trans (eb3.trans ec)))
    have Hb1 := hb1.mono (eb2.trans (eb3.trans ec))
    have Hb2 := hb2.mono (eb3.trans ec)
    have Hb3 := hb3.mono ec
    have Hp := (p0g_holds O B (K := K)).mono e06
    refine ((((((H0.and Ha).and Hb1).and Hb2).and Hb3).and hc).and Hp).imp ?_
    rintro σ ⟨⟨⟨⟨⟨⟨h0, ha⟩, hb1⟩, hb2⟩, hb3⟩, hc⟩, hz, ho⟩
    have hnb : σ r0.1 = !σ sbv := h0
    have hA0n : ((numVal σ A0 : ℕ) : ℤ) = 2 ^ (ℓo - 1) := by
      rw [hA0, constL_top σ _ _ ℓo hz ho (by omega)]
    -- the copy block in terms of msbBits
    have hcopy : ∀ i < n + 1, (fun t : Fin ℓo => σ (B + rb3.2.length + i * ℓo + t.val)) =
        msbBits σ ℓo (outs.getD i []) := by
      intro i hi
      funext t
      have hq : i * ℓo + t.val < (n + 1) * ℓo := by
        have : (i + 1) * ℓo ≤ (n + 1) * ℓo := Nat.mul_le_mul_right ℓo hi
        rw [Nat.add_mul, one_mul] at this; have := t.isLt; omega
      have := hc ⟨i * ℓo + t.val, hq⟩
      simp only at this
      rw [Nat.add_assoc, this]
      simp only [msbBits, outSrc]
      have ht := t.isLt
      have e1 : (i * ℓo + t.val) / ℓo = i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, zero_add]
      have e2 : (i * ℓo + t.val) % ℓo = t.val := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
      rw [e1, e2]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [hcopy i (by omega)]
      have hgi : outs.getD i [] = ra.1.getD i [] := by
        rw [houts, List.getD_append _ _ _ _ (by rw [oa, hgl]; exact hi)]
      rw [hgi]
      exact ha hz ho hnb hA0n i (by rw [hgl]; exact hi)
    · rw [hcopy n (by omega)]
      have hgi : outs.getD n [] = rb3.1 := by
        rw [houts, List.getD_append_right _ _ _ _ (by rw [oa, hgl])]
        simp [oa, hgl]
      rw [hgi]
      by_cases he : σ eqv
      · rw [if_pos he] at hb3
        rw [msbBits_congr σ ℓo _ _ hb3, if_pos he]
        by_cases hcc : σ cv
        · rw [if_pos hcc] at hb2
          rw [msbBits_congr σ ℓo _ _ hb2, if_pos hcc]
          have hK1n : ((numVal σ K1 : ℕ) : ℤ) ≡ 2 ^ (ℓo - 1) + 2 ^ fo [ZMOD 2 ^ ℓo] := by
            rw [hK1, numVal_eq_bval, constL_val σ _ _ hz ho]
            have := natmod_modEq (2 ^ (ℓo - 1) + 2 ^ fo) ℓo
            simpa using this
          rw [fpVal_out σ K1 ℓo fo hK1l (by omega) _ (by
            rw [abs_of_pos (pow_pos two_pos _)]
            exact pow_lt_pow_right₀ (by norm_num) (by omega)) hK1n]
          push_cast; field_simp
        · rw [if_neg hcc] at hb2
          rw [msbBits_congr σ ℓo _ _ hb2, if_neg hcc]
          rw [fpVal_out σ A0 ℓo fo hA0l (by omega) 0 (by simp) (by rw [hA0n]; simp)]
          simp
      · rw [if_neg he] at hb3
        rw [msbBits_congr σ ℓo _ _ hb3, if_neg he]
        have hP' : |PX σ hL Bh| ≤ 2 ^ Bh := by
          have hN := numVal_lt σ hL
          rw [hhl] at hN
          have hN' : ((numVal σ hL : ℕ) : ℤ) < 2 ^ Bh := by exact_mod_cast hN
          have hN0 : (0 : ℤ) ≤ ((numVal σ hL : ℕ) : ℤ) := Int.natCast_nonneg _
          unfold PX; rw [abs_le]; constructor <;> linarith
        have hb : |sgnB (σ r0.1) * 2 ^ (fo - fhh - 1) * PX σ hL Bh| < 2 ^ (ℓo - 1) := by
          rw [abs_mul, abs_mul, abs_pow, abs_two]
          have hs : |sgnB (σ r0.1)| = 1 := by cases σ r0.1 <;> simp [sgnB]
          rw [hs, one_mul]
          calc (2 : ℤ) ^ (fo - fhh - 1) * |PX σ hL Bh| ≤ 2 ^ (fo - fhh - 1) * 2 ^ Bh := by gcongr
            _ = 2 ^ (fo - fhh - 1 + Bh) := by rw [pow_add]
            _ < 2 ^ (ℓo - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
        have hm := hb1 hz ho (by rw [hnb]; simp)
        rw [hA0n] at hm
        rw [fpVal_out σ rb1.1 ℓo fo ob1 (by omega) _ hb hm, fpVal_msbBits σ hL Bh fhh hhl, hnb]
        have he2 : (2 : ℝ) ^ fo = 2 ^ (fo - fhh - 1) * 2 ^ (fhh + 1) := by
          rw [← pow_add, show fo - fhh - 1 + (fhh + 1) = fo by omega]
        rw [he2]
        cases σ sbv <;> simp [sgnB, sgnS] <;> field_simp <;> ring

end OutAll

end LTFC

-- ===== module Trunc =====

/-! Truncation: a bounded window of the two's-complement bits of an offset-binary register. -/

open QAlgorithms

namespace LTFC

/-- `Σ_{i<M} e_i 2^i` as an integer. -/
def sumBits (e : ℕ → Bool) (M : ℕ) : ℤ := ∑ i ∈ Finset.range M, ((e i).toNat : ℤ) * 2 ^ i

theorem sumBits_add (e : ℕ → Bool) (a k : ℕ) :
    sumBits e (a + k) = sumBits e a + 2 ^ a * sumBits (fun i => e (a + i)) k := by
  unfold sumBits
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro i _; rw [pow_add]; ring

theorem sumBits_nonneg (e : ℕ → Bool) (M : ℕ) : 0 ≤ sumBits e M :=
  Finset.sum_nonneg (fun i _ => by positivity)

theorem sumBits_lt (e : ℕ → Bool) (M : ℕ) : sumBits e M < 2 ^ M := by
  induction M with
  | zero => simp [sumBits]
  | succ M ih =>
    unfold sumBits at *
    rw [Finset.sum_range_succ, pow_succ]
    have : ((e M).toNat : ℤ) ≤ 1 := by cases e M <;> simp
    nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) M]

theorem sumBits_congr (e e' : ℕ → Bool) (M : ℕ) (h : ∀ i < M, e i = e' i) :
    sumBits e M = sumBits e' M := by
  unfold sumBits
  apply Finset.sum_congr rfl
  intro i hi; rw [h i (Finset.mem_range.1 hi)]

/-- Sign-extended bits of the offset-binary register `e_0 … e_{L-1}` (value `X = N - 2^{L-1}`). -/
def sext (e : ℕ → Bool) (L : ℕ) (i : ℕ) : Bool := if i < L - 1 then e i else !e (L - 1)

theorem sext_modEq (e : ℕ → Bool) (L : ℕ) (hL : 1 ≤ L) (M : ℕ) :
    sumBits e L - 2 ^ (L - 1) ≡ sumBits (sext e L) M [ZMOD 2 ^ M] := by
  have hX : sumBits e L - 2 ^ (L - 1) =
      sumBits e (L - 1) - ((!e (L - 1)).toNat : ℤ) * 2 ^ (L - 1) := by
    have := sumBits_add e (L - 1) 1
    rw [show L - 1 + 1 = L by omega] at this
    rw [this]
    simp only [sumBits, Finset.sum_range_one, Nat.add_zero, pow_zero, mul_one]
    cases e (L - 1) <;> simp <;> ring
  rw [hX]
  by_cases hM : M ≤ L - 1
  · obtain ⟨k, hk⟩ : ∃ k, L - 1 = M + k := ⟨L - 1 - M, by omega⟩
    rw [hk, sumBits_add, pow_add]
    have hs : sumBits (sext e L) M = sumBits e M :=
      sumBits_congr _ _ M (fun i hi => by simp only [sext]; rw [if_pos (by omega)])
    rw [hs]
    unfold Int.ModEq
    rw [show sumBits e M + 2 ^ M * sumBits (fun i => e (M + i)) k -
        ((!e (M + k)).toNat : ℤ) * (2 ^ M * 2 ^ k) =
        sumBits e M + 2 ^ M * (sumBits (fun i => e (M + i)) k - ((!e (M + k)).toNat : ℤ) * 2 ^ k)
        by ring, Int.add_mul_emod_self_left]
  · obtain ⟨k, hk⟩ : ∃ k, M = L - 1 + k := ⟨M - (L - 1), by omega⟩
    rw [hk, sumBits_add]
    have hs : sumBits (sext e L) (L - 1) = sumBits e (L - 1) :=
      sumBits_congr _ _ _ (fun i hi => by simp only [sext]; rw [if_pos hi])
    have hs2 : sumBits (fun i => sext e L (L - 1 + i)) k =
        ((!e (L - 1)).toNat : ℤ) * (2 ^ k - 1) := by
      have : ∀ i, sext e L (L - 1 + i) = !e (L - 1) := fun i => by
        simp only [sext]; rw [if_neg (by omega)]
      simp only [this, sumBits]
      rw [← Finset.mul_sum]
      congr 1
      have := geom_sum_mul (2 : ℤ) k
      norm_num at this; linarith
    rw [hs, hs2]
    unfold Int.ModEq
    rw [show sumBits e (L - 1) - ((!e (L - 1)).toNat : ℤ) * 2 ^ (L - 1) =
        (sumBits e (L - 1) + 2 ^ (L - 1) * (((!e (L - 1)).toNat : ℤ) * (2 ^ k - 1))) +
          2 ^ (L - 1 + k) * (-((!e (L - 1)).toNat : ℤ)) by rw [pow_add]; ring,
      Int.add_mul_emod_self_left]

/-- **Window lemma.** If `|X| < 2^{lo+K-1}`, the `K`-bit window at `lo` (top bit flipped) is the
offset-binary encoding of `⌊X / 2^lo⌋`. -/
theorem window_lemma (e : ℕ → Bool) (L lo K : ℕ) (hL : 1 ≤ L) (hK : 1 ≤ K)
    (hX : |sumBits e L - 2 ^ (L - 1)| < 2 ^ (lo + K - 1)) :
    ∃ Xlow : ℤ, 0 ≤ Xlow ∧ Xlow < 2 ^ lo ∧
      sumBits e L - 2 ^ (L - 1) = Xlow + 2 ^ lo *
        (sumBits (fun j => xor (sext e L (lo + j)) (decide (j = K - 1))) K - 2 ^ (K - 1)) := by
  set X := sumBits e L - 2 ^ (L - 1) with hXdef
  set M := lo + K with hM
  set S := sumBits (sext e L) M with hS
  have hmod := sext_modEq e L hL M
  have hS0 := sumBits_nonneg (sext e L) M
  have hS1 := sumBits_lt (sext e L) M
  set t := sext e L (M - 1) with ht
  -- split S at the top bit
  have hSsplit : S = sumBits (sext e L) (M - 1) + (t.toNat : ℤ) * 2 ^ (M - 1) := by
    have := sumBits_add (sext e L) (M - 1) 1
    rw [show M - 1 + 1 = M by omega] at this
    rw [hS, this]; simp [sumBits, ht]; ring
  have hlow := sumBits_lt (sext e L) (M - 1)
  have hlow0 := sumBits_nonneg (sext e L) (M - 1)
  have hpow : (2 : ℤ) ^ M = 2 * 2 ^ (M - 1) := by rw [← pow_succ']; congr 1; omega
  have hX2 : X = S - (t.toNat : ℤ) * 2 ^ M := by
    have hd : (2 : ℤ) ^ M ∣ X - (S - (t.toNat : ℤ) * 2 ^ M) := by
      have h1 : (2 : ℤ) ^ M ∣ S - X := hmod.dvd
      have h1' : (2 : ℤ) ^ M ∣ X - S := by
        have := dvd_neg.2 h1; rwa [neg_sub] at this
      have h2 : (2 : ℤ) ^ M ∣ (t.toNat : ℤ) * 2 ^ M := dvd_mul_left _ _
      rw [show X - (S - (t.toNat : ℤ) * 2 ^ M) = (X - S) + (t.toNat : ℤ) * 2 ^ M by ring]
      exact dvd_add h1' h2
    have habs : |X - (S - (t.toNat : ℤ) * 2 ^ M)| < 2 ^ M := by
      rw [abs_lt] at hX ⊢
      rw [show lo + K - 1 = M - 1 by omega] at hX
      cases ht' : t <;> simp only [ht', Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one,
        zero_mul, one_mul, sub_zero] at hSsplit ⊢ <;> constructor <;> linarith
    exact sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd hd habs)
  refine ⟨sumBits (sext e L) lo, sumBits_nonneg _ _, sumBits_lt _ _, ?_⟩
  -- the window
  have hSw : S = sumBits (sext e L) lo + 2 ^ lo * sumBits (fun j => sext e L (lo + j)) K :=
    sumBits_add _ _ _
  have hW : sumBits (fun j => xor (sext e L (lo + j)) (decide (j = K - 1))) K =
      sumBits (fun j => sext e L (lo + j)) K + 2 ^ (K - 1) - (t.toNat : ℤ) * 2 ^ K := by
    have h1 := sumBits_add (fun j => xor (sext e L (lo + j)) (decide (j = K - 1))) (K - 1) 1
    have h2 := sumBits_add (fun j => sext e L (lo + j)) (K - 1) 1
    rw [show K - 1 + 1 = K by omega] at h1 h2
    rw [h1, h2]
    have hc : sumBits (fun j => xor (sext e L (lo + j)) (decide (j = K - 1))) (K - 1) =
        sumBits (fun j => sext e L (lo + j)) (K - 1) :=
      sumBits_congr _ _ _ (fun i hi => by simp [show i ≠ K - 1 by omega])
    rw [hc]
    have htop : sext e L (lo + (K - 1)) = t := by rw [ht]; congr 1; omega
    simp only [sumBits, Finset.sum_range_one, Nat.add_zero, pow_zero, mul_one, decide_true,
      Nat.zero_add, htop]
    have hpK : (2 : ℤ) ^ K = 2 * 2 ^ (K - 1) := by rw [← pow_succ']; congr 1; omega
    rw [hpK]
    cases t <;> simp <;> ring
  rw [hX2, hW, hSw]
  have : (2 : ℤ) ^ M = 2 ^ lo * 2 ^ K := by rw [hM, pow_add]
  rw [this]; ring

end LTFC

namespace LTFC

section TruncB

variable {K' : ℕ} (O : (Fin K' → Bool) → Bool) (B : ℕ)

def winSrc (src : ℕ → ℕ) (L lo j : ℕ) : ℕ := if lo + j < L - 1 then src (lo + j) else src (L - 1)

def winFlip (L lo K j : ℕ) : Bool := xor (decide (L - 1 ≤ lo + j)) (decide (j = K - 1))

def truncE (src : ℕ → ℕ) (L lo K : ℕ) : BldO K' (List ℕ) := fun p =>
  ((List.range K).map (fun j => B + p.length + j),
    (blockE (K := K') (fun j : Fin K =>
      (⟨fun x _ => xor x (winFlip L lo K j), winSrc src L lo j, winSrc src L lo j⟩ : Instr)) p).2)

theorem numVal_range (σ : ℕ → Bool) (base K : ℕ) :
    ((numVal σ ((List.range K).map (fun j => base + j)) : ℕ) : ℤ) =
      sumBits (fun j => σ (base + j)) K := by
  induction K generalizing base with
  | zero => simp [numVal, sumBits]
  | succ K ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [numVal]
    have := ih (base + 1)
    have e1 : ((List.range K).map ((fun j => base + j) ∘ Nat.succ)) =
        (List.range K).map (fun j => base + 1 + j) := by
      apply List.map_congr_left; intro j _; simp; ring
    rw [e1]
    push_cast
    rw [this]
    have h2 := sumBits_add (fun j => σ (base + j)) 1 K
    rw [show 1 + K = K + 1 by ring] at h2
    rw [h2]
    simp only [sumBits, Finset.sum_range_one, pow_zero, mul_one, pow_one, Nat.add_zero]
    congr 1
    congr 1
    apply Finset.sum_congr rfl; intro i _; congr 3; ring

theorem truncE_spec (src : ℕ → ℕ) (L lo K : ℕ) (p : List (OIns K'))
    (hsrc : ∀ i, i < L → src i < B + p.length) (hL : 1 ≤ L) :
    ExtL p (truncE B src L lo K p).2 ∧ (truncE B src L lo K p).2.length = p.length + K ∧
    (truncE B src L lo K p).1.length = K ∧
    (∀ v ∈ (truncE B src L lo K p).1, v < B + (truncE B src L lo K p).2.length) ∧
    HoldsO O B (truncE B src L lo K p).2 (fun σ =>
      ((numVal σ (truncE B src L lo K p).1 : ℕ) : ℤ) =
        sumBits (fun j => xor (sext (fun i => σ (src i)) L (lo + j)) (decide (j = K - 1))) K) := by
  have hws : ∀ j, winSrc src L lo j < B + p.length := by
    intro j; unfold winSrc; split_ifs with h
    · exact hsrc _ (by omega)
    · exact hsrc _ (by omega)
  obtain ⟨e1, l1, h1⟩ := blockE_spec O B (K := K') (fun j : Fin K =>
    (⟨fun x _ => xor x (winFlip L lo K j), winSrc src L lo j, winSrc src L lo j⟩ : Instr)) p
    (fun j => ⟨hws j, hws j⟩)
  refine ⟨e1, l1, by simp [truncE], ?_, ?_⟩
  · intro v hv
    simp only [truncE, List.mem_map, List.mem_range] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    have h' : (truncE B src L lo K p).2.length = p.length + K := l1
    rw [h']; omega
  · refine h1.imp ?_
    intro σ h
    show ((numVal σ ((List.range K).map (fun j => B + p.length + j)) : ℕ) : ℤ) = _
    rw [numVal_range]
    apply sumBits_congr
    intro j hj
    have := h ⟨j, hj⟩
    simp only at this
    rw [this]
    simp only [winSrc, winFlip, sext]
    by_cases h1 : lo + j < L - 1
    · rw [if_pos h1, if_pos h1]; simp [show ¬ (L - 1 ≤ lo + j) by omega]
    · rw [if_neg h1, if_neg h1]; simp [show L - 1 ≤ lo + j by omega]

end TruncB

end LTFC

-- ===== module Conv =====

/-! `gatesRev → gates12` conversion and inverse circuits. -/

open QAlgorithms

namespace LTFC

noncomputable def toffMat : Matrix (Qubits 3) (Qubits 3) ℂ :=
  Matrix.of fun y z => if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) then 1 else 0

noncomputable def toffGate : Gate := ⟨3, toffMat⟩

theorem gatesRev_cases {g : Gate} (h : g ∈ QuantumLTF.Membership.gatesRev) :
    g = Gate.ofMatrix1 pauliX ∨ g = Gate.ofMatrix2 cnot ∨ g = toffGate := h

theorem toff_mulVec {M : ℕ} (w : Fin 3 ↪ Fin M) (z : Qubits M) :
    (embedOp toffMat w).mulVec (bv z) =
      bv (Function.update z (w 2) (xor (z (w 2)) (z (w 0) && z (w 1)))) := by
  rw [embedOp_mulVec_bv]
  set u0 : Qubits 3 := ![z (w 0), z (w 1), xor (z (w 2)) (z (w 0) && z (w 1))] with hu0
  rw [Finset.sum_eq_single u0]
  · have : toffMat u0 (z ∘ w) = 1 := by
      simp [toffMat, hu0]
    rw [this, one_smul]
    congr 1
    symm
    rw [eq_setPart_iff]
    constructor
    · funext j
      simp only [Function.comp_apply]
      have h01 : w 0 ≠ w 2 := fun e => by have := w.injective e; simp at this
      have h11 : w 1 ≠ w 2 := fun e => by have := w.injective e; simp at this
      fin_cases j
      · simp [Function.update_of_ne h01, hu0]
      · simp [Function.update_of_ne h11, hu0]
      · simp [hu0]
    · intro v hv
      rw [Function.update_of_ne]
      intro e; exact hv ⟨2, e.symm⟩
  · intro u _ hu
    have : toffMat u (z ∘ w) = 0 := by
      simp only [toffMat, Matrix.of_apply, Function.comp_apply]
      rw [if_neg]
      rintro ⟨h0, h1, h2⟩
      apply hu
      funext j; fin_cases j <;> simp [hu0, h0, h1, h2]
    rw [this, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

section ConvC

variable {r : ℕ} {ar : Fin r → ℕ}

theorem mem12_of_rev {g : Gate} (h : g ∈ QuantumLTF.Membership.gatesRev) (hne : g ≠ toffGate) :
    g ∈ G12 := by
  rcases gatesRev_cases h with rfl | rfl | rfl
  · exact ofMatrix1_mem pauliX_unitary
  · exact ofMatrix2_mem cnot_unitary
  · exact absurd rfl hne

def castW {M : ℕ} {gate : Gate} (h : gate.arity = 3) (wires : Fin gate.arity ↪ Fin M) :
    Fin 3 ↪ Fin M :=
  ⟨fun i => wires (Fin.cast h.symm i), fun i j e => by
    have := wires.injective e; simpa [Fin.ext_iff] using this⟩

theorem castW_ne {M : ℕ} {gate : Gate} (h : gate.arity = 3) (wires : Fin gate.arity ↪ Fin M)
    (i j : Fin 3) (hij : i ≠ j) : castW h wires i ≠ castW h wires j :=
  fun e => hij ((castW h wires).injective e)

open Classical in
noncomputable def convGate {M : ℕ} : GateApp QuantumLTF.Membership.gatesRev M → OracleCircuit G12 ar M
  | ⟨gate, mem, wires⟩ =>
    if h : gate = toffGate then
      toffoli12 (castW (by rw [h]; rfl) wires 0) (castW (by rw [h]; rfl) wires 1)
        (castW (by rw [h]; rfl) wires 2)
        (castW_ne _ _ 0 1 (by decide)) (castW_ne _ _ 0 2 (by decide)) (castW_ne _ _ 1 2 (by decide))
    else [.gate ⟨gate, mem12_of_rev mem h, wires⟩]

noncomputable def convStep {M : ℕ} :
    OracleStep QuantumLTF.Membership.gatesRev ar M → OracleCircuit G12 ar M
  | .gate g => convGate g
  | .query k adj ctl w h => [.query k adj ctl w h]

noncomputable def convC {M : ℕ} (c : OracleCircuit QuantumLTF.Membership.gatesRev ar M) :
    OracleCircuit G12 ar M := c.flatMap convStep

theorem convStep_unitary {M : ℕ} (s : OracleStep QuantumLTF.Membership.gatesRev ar M)
    (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ) :
    (convStep s).unitary orc = s.mat orc := by
  cases s with
  | query k adj ctl w h => simp only [convStep]; rw [single_unitary]; cases ctl <;> rfl
  | gate g =>
    obtain ⟨gate, mem, wires⟩ := g
    simp only [convStep, convGate]
    by_cases h : gate = toffGate
    · subst h
      rw [dif_pos rfl]
      apply mat_ext_bv
      intro z
      rw [impl_toffoli12 _ _ _ _ _ _ orc z]
      simp only [OracleStep.mat]
      show _ = (embedOp toffMat (castW rfl wires)).mulVec (bv z)
      rw [toff_mulVec]
    · rw [dif_neg h, single_unitary]; rfl

theorem convC_unitary {M : ℕ} (c : OracleCircuit QuantumLTF.Membership.gatesRev ar M)
    (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ) :
    (convC c).unitary orc = c.unitary orc := by
  induction c with
  | nil => rfl
  | cons s c ih =>
    simp only [convC, List.flatMap_cons] at ih ⊢
    rw [unitary_append, ih, convStep_unitary, unitary_cons]

theorem convStep_counts {M : ℕ} (s : OracleStep QuantumLTF.Membership.gatesRev ar M) (k : Fin r) :
    (QuantumLTF.Membership.Uncontrolled [s] → QuantumLTF.Membership.Uncontrolled (convStep s)) ∧
    (convStep s).queryCount k = OracleCircuit.queryCount [s] k ∧
    (convStep s).gateCount ≤ 7 * OracleCircuit.gateCount [s] := by
  cases s with
  | query k' adj ctl w h =>
    simp only [convStep]
    refine ⟨fun hu st hst => ?_, rfl, by simp [OracleCircuit.gateCount]⟩
    have := hu _ List.mem_cons_self
    simp at hst; subst hst; exact this
  | gate g =>
    obtain ⟨gate, mem, wires⟩ := g
    simp only [convStep, convGate]
    by_cases h : gate = toffGate
    · rw [dif_pos h]
      have hall := allGates_toffoli12 (ar := ar) (M := M) _ _ _
        (castW_ne (by rw [h]; rfl) wires 0 1 (by decide)) (castW_ne (by rw [h]; rfl) wires 0 2 (by decide))
        (castW_ne (by rw [h]; rfl) wires 1 2 (by decide))
      refine ⟨fun _ => hall.uncontrolled, ?_, ?_⟩
      · rw [hall.queryCount]; simp [OracleCircuit.queryCount, OracleStep.IsQueryTo]
      · rw [hall.gateCount]; simp [OracleCircuit.gateCount, toffoli12, toffMid]
    · rw [dif_neg h]
      refine ⟨fun _ st hst => by simp at hst; subst hst; trivial, rfl, ?_⟩
      simp [OracleCircuit.gateCount]

theorem convC_counts {M : ℕ} (c : OracleCircuit QuantumLTF.Membership.gatesRev ar M)
    (hc : QuantumLTF.Membership.Uncontrolled c) (k : Fin r) :
    QuantumLTF.Membership.Uncontrolled (convC c) ∧ (convC c).queryCount k = c.queryCount k ∧
    (convC c).gateCount ≤ 7 * c.gateCount := by
  induction c with
  | nil => exact ⟨fun st hst => by simp [convC] at hst, rfl, by simp [convC, OracleCircuit.gateCount]⟩
  | cons s c ih =>
    have hc' : QuantumLTF.Membership.Uncontrolled c := fun st hst => hc st (List.mem_cons_of_mem _ hst)
    have hs : QuantumLTF.Membership.Uncontrolled [s] := fun st hst => by
      simp at hst; subst hst; exact hc _ List.mem_cons_self
    obtain ⟨u1, q1, g1⟩ := ih hc'
    obtain ⟨u0, q0, g0⟩ := convStep_counts s k
    have hsplit : (s :: c) = [s] ++ c := rfl
    simp only [convC, List.flatMap_cons] at u1 q1 g1 ⊢
    refine ⟨uncontrolled_append (u0 hs) u1, ?_, ?_⟩
    · rw [queryCount_append, q0, q1, hsplit, queryCount_append]
    · rw [gateCount_append, hsplit, gateCount_append]; omega

end ConvC

/-! ### Inverse circuits -/

section Inv

variable {r : ℕ} {ar : Fin r → ℕ}

theorem star_gate_mem {g : Gate} (h : g ∈ G12) : (⟨g.arity, star g.mat⟩ : Gate) ∈ G12 :=
  ⟨Unitary.star_mem h.1, h.2.1, h.2.2⟩

def invStep {M : ℕ} : OracleStep G12 ar M → OracleStep G12 ar M
  | .gate g => .gate ⟨⟨g.gate.arity, star g.gate.mat⟩, star_gate_mem g.mem, g.wires⟩
  | .query k adj ctl w h => .query k (!adj) ctl w h

def invC {M : ℕ} (c : OracleCircuit G12 ar M) : OracleCircuit G12 ar M := (c.map invStep).reverse

theorem invC_unitary {M : ℕ} (c : OracleCircuit G12 ar M) (hc : QuantumLTF.Membership.Uncontrolled c)
    (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ) :
    (invC c).unitary orc = star (c.unitary orc) := by
  induction c with
  | nil => simp [invC, unitary_nil]
  | cons s c ih =>
    have hc' : QuantumLTF.Membership.Uncontrolled c := fun st hst => hc st (List.mem_cons_of_mem _ hst)
    have hs := hc s List.mem_cons_self
    have e : invC (s :: c) = invC c ++ [invStep s] := by simp [invC]
    rw [e, unitary_append, single_unitary, ih hc', unitary_cons, star_mul]
    congr 1
    cases s with
    | gate g => simp only [invStep, OracleStep.mat]; exact embedOp_star _ _
    | query k adj ctl w h =>
      simp only at hs; subst hs
      simp only [invStep, OracleStep.mat]
      rw [← embedOp_star]
      congr 1
      cases adj <;> simp

theorem invC_counts {M : ℕ} (c : OracleCircuit G12 ar M) (hc : QuantumLTF.Membership.Uncontrolled c)
    (k : Fin r) :
    QuantumLTF.Membership.Uncontrolled (invC c) ∧ (invC c).queryCount k = c.queryCount k ∧
    (invC c).gateCount = c.gateCount := by
  refine ⟨?_, ?_, ?_⟩
  · intro st hst
    simp only [invC, List.mem_reverse, List.mem_map] at hst
    obtain ⟨s, hs, rfl⟩ := hst
    have := hc s hs
    cases s with
    | gate g => trivial
    | query k adj ctl w h => simpa [invStep] using this
  · simp only [invC, OracleCircuit.queryCount, List.countP_reverse, List.countP_map]
    congr 1; funext s; cases s <;> rfl
  · simp only [invC, OracleCircuit.gateCount, List.countP_reverse, List.countP_map]
    congr 1; funext s; cases s <;> rfl

end Inv

end LTFC

-- ===== module Subst =====

/-!
# Substituting a block-diagonal circuit for the oracle of another circuit

`A` acts on `[params (Pn) | oracle register (a₃)]` and never changes the params. Replacing every
oracle call of `c₃` (on wires `e`) by `A` placed on `[π | ι ∘ e]` (inverse calls by `invC A`)
gives a circuit that, on states whose param wires hold `v`, acts as `c₃` run with the oracle
`blockOf UA v`.
-/

open QAlgorithms

namespace LTFC

section Block

variable {Pn a₃ : ℕ}

/-- The block of `N` at the parameter value `v`. -/
def blockOf (N : Matrix (Qubits (Pn + a₃)) (Qubits (Pn + a₃)) ℂ) (v : Qubits Pn) :
    Matrix (Qubits a₃) (Qubits a₃) ℂ :=
  fun y' y => N (Fin.append v y') (Fin.append v y)

def BlockDiag (N : Matrix (Qubits (Pn + a₃)) (Qubits (Pn + a₃)) ℂ) : Prop :=
  ∀ y y', N y' y ≠ 0 → ∀ i : Fin Pn, y' (Fin.castAdd a₃ i) = y (Fin.castAdd a₃ i)

theorem sum_append {β : Type} [AddCommMonoid β] (f : Qubits (Pn + a₃) → β) :
    ∑ u, f u = ∑ u₁ : Qubits Pn, ∑ u₂ : Qubits a₃, f (Fin.append u₁ u₂) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.appendEquiv Pn a₃) _ _ (fun p => rfl)).symm

theorem BlockDiag.zero {N : Matrix (Qubits (Pn + a₃)) (Qubits (Pn + a₃)) ℂ} (h : BlockDiag N)
    {u₁ v : Qubits Pn} (hne : u₁ ≠ v) (u₂ y : Qubits a₃) :
    N (Fin.append u₁ u₂) (Fin.append v y) = 0 := by
  by_contra h0
  apply hne
  funext i
  have := h _ _ h0 i
  simpa using this

theorem BlockDiag.zero' {N : Matrix (Qubits (Pn + a₃)) (Qubits (Pn + a₃)) ℂ} (h : BlockDiag N)
    {u₁ v : Qubits Pn} (hne : u₁ ≠ v) (u₂ y : Qubits a₃) :
    N (Fin.append v y) (Fin.append u₁ u₂) = 0 := by
  by_contra h0
  apply hne
  funext i
  have := h _ _ h0 i
  simpa using this.symm

theorem BlockDiag.star {N : Matrix (Qubits (Pn + a₃)) (Qubits (Pn + a₃)) ℂ} (h : BlockDiag N) :
    BlockDiag (star N) := by
  intro y y' h0 i
  rw [Matrix.star_apply] at h0
  have : N y y' ≠ 0 := fun e => h0 (by rw [e, star_zero])
  exact (h y' y this i).symm

theorem blockOf_star (N : Matrix (Qubits (Pn + a₃)) (Qubits (Pn + a₃)) ℂ) (v : Qubits Pn) :
    blockOf (star N) v = star (blockOf N v) := by
  ext y' y; simp [blockOf, Matrix.star_apply]

theorem blockOf_mul {N N' : Matrix (Qubits (Pn + a₃)) (Qubits (Pn + a₃)) ℂ} (h : BlockDiag N)
    (v : Qubits Pn) : blockOf (N * N') v = blockOf N v * blockOf N' v := by
  ext y' y
  simp only [blockOf, Matrix.mul_apply]
  rw [sum_append, Finset.sum_eq_single v]
  · intro u₁ _ hu₁
    apply Finset.sum_eq_zero; intro u₂ _
    rw [h.zero' hu₁, zero_mul]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem blockOf_one (v : Qubits Pn) : blockOf (1 : Matrix (Qubits (Pn + a₃)) _ ℂ) v = 1 := by
  ext y' y
  simp only [blockOf, Matrix.one_apply]
  by_cases h : y' = y
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro e; apply h
    funext j
    have := congrFun e (Fin.natAdd Pn j)
    simpa using this

theorem blockOf_unitary {N : Matrix (Qubits (Pn + a₃)) (Qubits (Pn + a₃)) ℂ} (h : BlockDiag N)
    (hN : N ∈ Matrix.unitaryGroup _ ℂ) (v : Qubits Pn) :
    blockOf N v ∈ Matrix.unitaryGroup (Qubits a₃) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hN ⊢
  rw [← blockOf_star, ← blockOf_mul h, hN, blockOf_one]

theorem blockOf_act (N : Matrix (Qubits (Pn + a₃)) (Qubits (Pn + a₃)) ℂ) (v : Qubits Pn)
    (y y'' : Qubits a₃)
    (hN : act N (ket (Fin.append v y)) = ket (Fin.append v y'')) :
    act (blockOf N v) (ket y) = ket y'' := by
  have h1 : ∀ x, act N (ket x) = WithLp.toLp 2 (N.mulVec (bv x)) := fun x => rfl
  have h2 : ∀ x, act (blockOf N v) (ket x) = WithLp.toLp 2 ((blockOf N v).mulVec (bv x)) :=
    fun x => rfl
  rw [h2]
  rw [h1] at hN
  have hc := congrArg (fun φ => WithLp.ofLp φ) hN
  simp only [Matrix.mulVec_single_one] at hc
  have : (blockOf N v).mulVec (bv y) = bv y'' := by
    rw [Matrix.mulVec_single_one]
    funext y'
    have := congrFun hc (Fin.append v y')
    simp only [Matrix.col_apply] at this
    simp only [Matrix.col_apply, blockOf, this, ket, bv]
    simp only [PiLp.ofLp_single, Pi.single_apply]
    by_cases hy : y' = y''
    · subst hy; simp
    · rw [if_neg hy, if_neg]
      intro e; apply hy
      funext j
      have := congrFun e (Fin.natAdd Pn j)
      simpa using this
  rw [this]; rfl

end Block

section AppendEmb

variable {Pn a₃ MT : ℕ}

def appendFun (π : Fin Pn ↪ Fin MT) (κ : Fin a₃ ↪ Fin MT) (i : Fin (Pn + a₃)) : Fin MT :=
  Fin.addCases (motive := fun _ => Fin MT) π κ i

@[simp] theorem appendFun_left (π : Fin Pn ↪ Fin MT) (κ : Fin a₃ ↪ Fin MT) (i : Fin Pn) :
    appendFun π κ (Fin.castAdd a₃ i) = π i := by simp [appendFun]

@[simp] theorem appendFun_right (π : Fin Pn ↪ Fin MT) (κ : Fin a₃ ↪ Fin MT) (i : Fin a₃) :
    appendFun π κ (Fin.natAdd Pn i) = κ i := by simp [appendFun]

def appendEmb (π : Fin Pn ↪ Fin MT) (κ : Fin a₃ ↪ Fin MT)
    (hd : ∀ i j, π i ≠ κ j) : Fin (Pn + a₃) ↪ Fin MT :=
  ⟨appendFun π κ, by
    intro i j hij
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j => simp only [appendFun_left] at hij; rw [π.injective hij]
      | right j => simp only [appendFun_left, appendFun_right] at hij; exact absurd hij (hd i j)
    | right i =>
      induction j using Fin.addCases with
      | left j => simp only [appendFun_left, appendFun_right] at hij; exact absurd hij.symm (hd j i)
      | right j => simp only [appendFun_right] at hij; rw [κ.injective hij]⟩

@[simp] theorem appendEmb_apply (π : Fin Pn ↪ Fin MT) (κ : Fin a₃ ↪ Fin MT) (hd : ∀ i j, π i ≠ κ j)
    (i : Fin (Pn + a₃)) : appendEmb π κ hd i = appendFun π κ i := rfl

theorem comp_appendEmb (π : Fin Pn ↪ Fin MT) (κ : Fin a₃ ↪ Fin MT) (hd : ∀ i j, π i ≠ κ j)
    (Y : Qubits MT) : Y ∘ appendEmb π κ hd = Fin.append (Y ∘ π) (Y ∘ κ) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp
  | right i => simp

theorem setPart_appendEmb (π : Fin Pn ↪ Fin MT) (κ : Fin a₃ ↪ Fin MT) (hd : ∀ i j, π i ≠ κ j)
    (Y : Qubits MT) (y : Qubits a₃) :
    setPart Y (appendEmb π κ hd) (Fin.append (Y ∘ π) y) = setPart Y κ y := by
  symm
  rw [eq_setPart_iff]
  constructor
  · rw [comp_appendEmb]
    congr 1
    · funext i
      simp only [Function.comp_apply]
      rw [setPart_off]
      rintro ⟨j, hj⟩; exact hd i j hj.symm
    · exact setPart_comp Y κ y
  · intro v hv
    rw [setPart_off]
    intro ⟨j, hj⟩; apply hv
    exact ⟨Fin.natAdd Pn j, by simp [hj]⟩

/-- **Key lemma**: on states whose param wires hold `v`, the embedded block-diagonal `N` acts as
its block on `κ`. -/
theorem embed_block (π : Fin Pn ↪ Fin MT) (κ : Fin a₃ ↪ Fin MT) (hd : ∀ i j, π i ≠ κ j)
    (N : Matrix (Qubits (Pn + a₃)) (Qubits (Pn + a₃)) ℂ) (hN : BlockDiag N)
    (Y : Qubits MT) :
    (embedOp N (appendEmb π κ hd)).mulVec (bv Y) = (embedOp (blockOf N (Y ∘ π)) κ).mulVec (bv Y) := by
  rw [embedOp_mulVec_bv, embedOp_mulVec_bv, sum_append, Finset.sum_eq_single (Y ∘ π)]
  · apply Finset.sum_congr rfl
    intro y _
    rw [setPart_appendEmb, comp_appendEmb]
    rfl
  · intro u₁ _ hu₁
    apply Finset.sum_eq_zero
    intro u₂ _
    rw [comp_appendEmb, hN.zero hu₁, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem embedOp_keeps {k MT : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (κ : Fin k ↪ Fin MT)
    (Y Y' : Qubits MT) (h : (embedOp M κ).mulVec (bv Y) Y' ≠ 0) :
    ∀ v, v ∉ Set.range κ → Y' v = Y v := by
  rw [embedOp_mulVec_bv] at h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bv, Pi.single_apply] at h
  obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have : Y' = setPart Y κ u := by by_contra hne; simp [hne] at hu
  intro v hv
  rw [this, setPart_off _ _ _ hv]

end AppendEmb

end LTFC

namespace LTFC

section SubstC

variable {Pn a₃ MT m₃ aO : ℕ}

noncomputable def substStep (ι : Fin m₃ ↪ Fin MT) (π : Fin Pn ↪ Fin MT)
    (hd : ∀ i j, π i ≠ ι j) (A : OracleCircuit G12 (fun _ : Fin 1 => aO) (Pn + a₃)) :
    OracleStep G12 (fun _ : Fin 1 => a₃) m₃ → OracleCircuit G12 (fun _ : Fin 1 => aO) MT
  | .gate g => [.gate ⟨g.gate, g.mem, g.wires.trans ι⟩]
  | .query _ adj _ e _ => relabel (if adj then invC A else A)
      (appendEmb π (e.trans ι) (fun i j => hd i (e j)))

noncomputable def substC (ι : Fin m₃ ↪ Fin MT) (π : Fin Pn ↪ Fin MT)
    (hd : ∀ i j, π i ≠ ι j) (A : OracleCircuit G12 (fun _ : Fin 1 => aO) (Pn + a₃))
    (c : OracleCircuit G12 (fun _ : Fin 1 => a₃) m₃) : OracleCircuit G12 (fun _ : Fin 1 => aO) MT :=
  c.flatMap (substStep ι π hd A)

def SuppP (π : Fin Pn ↪ Fin MT) (v : Qubits Pn) (φ : Qubits MT → ℂ) : Prop :=
  ∀ Y, φ Y ≠ 0 → Y ∘ π = v

theorem suppP_embedOp {k : ℕ} (π : Fin Pn ↪ Fin MT) (κ : Fin k ↪ Fin MT)
    (hd : ∀ i j, π i ≠ κ j) (M : Matrix (Qubits k) (Qubits k) ℂ) (v : Qubits Pn)
    (φ : Qubits MT → ℂ) (hφ : SuppP π v φ) : SuppP π v ((embedOp M κ).mulVec φ) := by
  intro Y' hY'
  have hφd : φ = ∑ Y, φ Y • bv Y := by funext y; simp [bv, Finset.sum_apply, Pi.single_apply]
  rw [hφd, Matrix.mulVec_sum] at hY'
  simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hY'
  obtain ⟨Y, _, hY⟩ := Finset.exists_ne_zero_of_sum_ne_zero hY'
  have h1 : φ Y ≠ 0 := fun e => hY (by rw [e, zero_mul])
  have h2 : (embedOp M κ).mulVec (bv Y) Y' ≠ 0 := fun e => hY (by rw [e, mul_zero])
  have hk := embedOp_keeps M κ Y Y' h2
  rw [← hφ Y h1]
  funext i
  exact hk (π i) (by rintro ⟨j, hj⟩; exact hd i j hj.symm)

theorem mulVec_of_bv {MT' : ℕ} (U V : Matrix (Qubits MT') (Qubits MT') ℂ) (P : Qubits MT' → Prop)
    (h : ∀ Y, P Y → U.mulVec (bv Y) = V.mulVec (bv Y)) (φ : Qubits MT' → ℂ)
    (hφ : ∀ Y, φ Y ≠ 0 → P Y) : U.mulVec φ = V.mulVec φ := by
  have hφd : φ = ∑ Y, φ Y • bv Y := by funext y; simp [bv, Finset.sum_apply, Pi.single_apply]
  rw [hφd, Matrix.mulVec_sum, Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro Y _
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
  by_cases hY : φ Y = 0
  · rw [hY, zero_smul, zero_smul]
  · rw [h Y (hφ Y hY)]

theorem substStep_spec (ι : Fin m₃ ↪ Fin MT) (π : Fin Pn ↪ Fin MT) (hd : ∀ i j, π i ≠ ι j)
    (A : OracleCircuit G12 (fun _ : Fin 1 => aO) (Pn + a₃)) (hA : QuantumLTF.Membership.Uncontrolled A)
    (O : Matrix (Qubits aO) (Qubits aO) ℂ) (hB : BlockDiag (A.unitary fun _ => O))
    (s : OracleStep G12 (fun _ : Fin 1 => a₃) m₃) (hs : QuantumLTF.Membership.Uncontrolled [s])
    (v : Qubits Pn) (φ : Qubits MT → ℂ) (hφ : SuppP π v φ) :
    ((substStep ι π hd A s).unitary fun _ => O).mulVec φ =
      (embedOp (s.mat fun _ => blockOf (A.unitary fun _ => O) v) ι).mulVec φ := by
  cases s with
  | gate g =>
    simp only [substStep]
    rw [single_unitary]
    simp only [OracleStep.mat]
    rw [embedOp_trans]
  | query k adj ctl e h =>
    have hctl : ctl = none := hs _ List.mem_cons_self
    subst hctl
    simp only [substStep]
    apply mulVec_of_bv _ _ (fun Y => Y ∘ π = v) _ φ hφ
    intro Y hY
    rw [relabel_unitary _ _ (by split_ifs; exacts [(invC_counts A hA 0).1, hA])]
    simp only [OracleStep.mat]
    rw [← embedOp_trans]
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    cases adj
    · simp only [Bool.false_eq_true, if_false]
      have := embed_block π (e.trans ι) (fun i j => hd i (e j)) _ hB Y
      rw [hY] at this; exact this
    · simp only [if_true]
      rw [invC_unitary A hA]
      have := embed_block π (e.trans ι) (fun i j => hd i (e j)) _ hB.star Y
      rw [hY, blockOf_star] at this; exact this

theorem substC_spec (ι : Fin m₃ ↪ Fin MT) (π : Fin Pn ↪ Fin MT) (hd : ∀ i j, π i ≠ ι j)
    (A : OracleCircuit G12 (fun _ : Fin 1 => aO) (Pn + a₃)) (hA : QuantumLTF.Membership.Uncontrolled A)
    (O : Matrix (Qubits aO) (Qubits aO) ℂ) (hB : BlockDiag (A.unitary fun _ => O))
    (c : OracleCircuit G12 (fun _ : Fin 1 => a₃) m₃) (hc : QuantumLTF.Membership.Uncontrolled c)
    (v : Qubits Pn) (φ : Qubits MT → ℂ) (hφ : SuppP π v φ) :
    ((substC ι π hd A c).unitary fun _ => O).mulVec φ =
      (embedOp (c.unitary fun _ => blockOf (A.unitary fun _ => O) v) ι).mulVec φ := by
  induction c generalizing φ with
  | nil => simp [substC, unitary_nil, embedOp_one]
  | cons s c ih =>
    have hc' : QuantumLTF.Membership.Uncontrolled c := fun st hst => hc st (List.mem_cons_of_mem _ hst)
    have hs : QuantumLTF.Membership.Uncontrolled [s] := fun st hst => by
      simp at hst; subst hst; exact hc _ List.mem_cons_self
    have e : substC ι π hd A (s :: c) = substStep ι π hd A s ++ substC ι π hd A c := by
      simp [substC]
    rw [e, unitary_append, ← Matrix.mulVec_mulVec, substStep_spec ι π hd A hA O hB s hs v φ hφ,
      ih hc' _ (suppP_embedOp π ι hd _ v φ hφ), Matrix.mulVec_mulVec, ← embedOp_mul,
      unitary_cons]

theorem substC_counts (ι : Fin m₃ ↪ Fin MT) (π : Fin Pn ↪ Fin MT) (hd : ∀ i j, π i ≠ ι j)
    (A : OracleCircuit G12 (fun _ : Fin 1 => aO) (Pn + a₃)) (hA : QuantumLTF.Membership.Uncontrolled A)
    (c : OracleCircuit G12 (fun _ : Fin 1 => a₃) m₃) (hc : QuantumLTF.Membership.Uncontrolled c) :
    QuantumLTF.Membership.Uncontrolled (substC ι π hd A c) ∧
    (substC ι π hd A c).queryCount 0 = c.queryCount 0 * A.queryCount 0 ∧
    (substC ι π hd A c).gateCount = c.gateCount + c.queryCount 0 * A.gateCount := by
  induction c with
  | nil => exact ⟨fun st hst => by simp [substC] at hst, by simp [substC, OracleCircuit.queryCount],
      by simp [substC, OracleCircuit.gateCount, OracleCircuit.queryCount]⟩
  | cons s c ih =>
    have hc' : QuantumLTF.Membership.Uncontrolled c := fun st hst => hc st (List.mem_cons_of_mem _ hst)
    obtain ⟨u1, q1, g1⟩ := ih hc'
    have e : substC ι π hd A (s :: c) = substStep ι π hd A s ++ substC ι π hd A c := by
      simp [substC]
    have hsplit : (s :: c) = [s] ++ c := rfl
    rw [e, hsplit, queryCount_append, gateCount_append, queryCount_append, gateCount_append, q1, g1]
    cases s with
    | gate g =>
      have hall : AllGates (substStep ι π hd A (.gate g)) := allGates_single _ ⟨_, rfl⟩
      refine ⟨uncontrolled_append hall.uncontrolled u1, ?_, ?_⟩
      · rw [hall.queryCount]; simp [OracleCircuit.queryCount, OracleStep.IsQueryTo]
      · rw [hall.gateCount]; simp [substStep, OracleCircuit.gateCount, OracleCircuit.queryCount,
          OracleStep.IsQueryTo]; ring
    | query k adj ctl e' h =>
      have hk : k = 0 := Subsingleton.elim _ _
      subst hk
      have hI := invC_counts A hA 0
      refine ⟨uncontrolled_append (relabel_uncontrolled _ _) u1, ?_, ?_⟩
      · simp only [substStep]
        rw [relabel_queryCount]
        have e1 : OracleCircuit.queryCount [OracleStep.query (S := G12) (a := fun _ : Fin 1 => a₃)
            0 adj ctl e' h] 0 = 1 := by simp [OracleCircuit.queryCount, OracleStep.IsQueryTo]
        rw [e1]
        cases adj
        · simp only [Bool.false_eq_true, if_false]; ring
        · simp only [if_true]; rw [hI.2.1]; ring
      · simp only [substStep]
        rw [relabel_gateCount]
        have e1 : OracleCircuit.queryCount [OracleStep.query (S := G12) (a := fun _ : Fin 1 => a₃)
            0 adj ctl e' h] 0 = 1 := by simp [OracleCircuit.queryCount, OracleStep.IsQueryTo]
        have e2 : OracleCircuit.gateCount [OracleStep.query (S := G12) (a := fun _ : Fin 1 => a₃)
            0 adj ctl e' h] = 0 := by simp [OracleCircuit.gateCount]
        rw [e1, e2]
        cases adj
        · simp only [Bool.false_eq_true, if_false]; ring
        · simp only [if_true]; rw [hI.2.2]; ring

end SubstC

end LTFC

-- ===== module Params =====

/-! Real-number bounds on the parameters of the assembly, all `O(Λ)`, `Λ = log(n/ε)`. -/

namespace LTFC

open Real

section P

variable {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)

include hn hε hε2

end P

end LTFC

namespace LTFC

open Real

section P2

variable {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)

include hn hε hε2

end P2

end LTFC

-- ===== module Assembly =====

/-! The assembled circuit for `learningCertificate_circuit`: layout and definitions. -/

open QAlgorithms

namespace LTFC

section WinAll

variable {K' : ℕ} (O : (Fin K' → Bool) → Bool) (B : ℕ)

def winAll (L lo K : ℕ) : List (ℕ → ℕ) → BldO K' (List (List ℕ))
  | [] => fun p => ([], p)
  | s :: ss => fun p =>
    let r := truncE B s L lo K p
    let r2 := winAll L lo K ss r.2
    (r.1 :: r2.1, r2.2)

theorem winAll_spec (L lo K : ℕ) (hL : 1 ≤ L) :
    ∀ (ss : List (ℕ → ℕ)) (p : List (OIns K')),
    (∀ s ∈ ss, ∀ i, i < L → s i < B + p.length) →
    ExtL p (winAll B L lo K ss p).2 ∧ (winAll B L lo K ss p).2.length = p.length + ss.length * K ∧
    (winAll B L lo K ss p).1.length = ss.length ∧
    (∀ X ∈ (winAll B L lo K ss p).1, X.length = K ∧ ∀ v ∈ X, v < B + (winAll B L lo K ss p).2.length) ∧
    HoldsO O B (winAll B L lo K ss p).2 (fun σ => ∀ i < ss.length,
      ((numVal σ ((winAll B L lo K ss p).1.getD i []) : ℕ) : ℤ) =
        sumBits (fun j => xor (sext (fun k => σ ((ss.getD i (fun _ => 0)) k)) L (lo + j))
          (decide (j = K - 1))) K) := by
  intro ss
  induction ss with
  | nil =>
    intro p _
    refine ⟨ExtL.refl _, by simp [winAll], by simp [winAll], by simp [winAll], ?_⟩
    intro q inp i hi; simp at hi
  | cons s ss ih =>
    intro p hs
    obtain ⟨e1, l1, o1, v1, h1⟩ := truncE_spec O B s L lo K p (hs s List.mem_cons_self) hL
    set r := truncE B s L lo K p with hr
    have le1 := e1.length_le
    obtain ⟨e2, l2, o2, v2, h2⟩ := ih r.2 (fun s' hs' i hi => by
      have := hs s' (List.mem_cons_of_mem _ hs') i hi; omega)
    set r2 := winAll B L lo K ss r.2 with hr2
    change ExtL p r2.2 ∧ r2.2.length = p.length + (ss.length + 1) * K ∧
      (r.1 :: r2.1).length = ss.length + 1 ∧
      (∀ X ∈ r.1 :: r2.1, X.length = K ∧ ∀ v ∈ X, v < B + r2.2.length) ∧
      HoldsO O B r2.2 (fun σ => ∀ i < ss.length + 1,
        ((numVal σ ((r.1 :: r2.1).getD i []) : ℕ) : ℤ) =
          sumBits (fun j => xor (sext (fun k => σ (((s :: ss).getD i (fun _ => 0)) k)) L (lo + j))
            (decide (j = K - 1))) K)
    refine ⟨e1.trans e2, by rw [l2, l1]; ring, by simp [o2], ?_, ?_⟩
    · intro X hX
      rcases List.mem_cons.1 hX with h | h
      · subst h; exact ⟨o1, fun v hv => by have := v1 v hv; have := e2.length_le; omega⟩
      · exact v2 X h
    · refine ((h1.mono e2).and h2).imp ?_
      rintro σ ⟨h1, h2⟩ i hi
      cases i with
      | zero => simpa using h1
      | succ i => simpa using h2 i (by omega)

end WinAll

/-! ### Layout -/

section Layout

variable (n ℓ₁ f₁ m q ℓ f : ℕ)

abbrev tP : List (OIns (n * ℓ)) := (testProg n ℓ₁ f₁ m q ℓ f).2
abbrev tO : List ℕ := (testProg n ℓ₁ f₁ m q ℓ f).1

variable (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)

include hf hℓ in
theorem tO_valid : ∀ v ∈ tO n ℓ₁ f₁ m q ℓ f, v < n * ℓ₁ + (tP n ℓ₁ f₁ m q ℓ f).length :=
  (testProg_spec n ℓ₁ f₁ m q ℓ f hf hℓ 0 0).2.1

theorem tO_length (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ) :
    (tO n ℓ₁ f₁ m q ℓ f).length = 2 := (testProg_spec n ℓ₁ f₁ m q ℓ f hf hℓ 0 0).1

noncomputable def testCirc : OracleCircuit G12 (fun _ : Fin 1 => n * ℓ + 1)
    (bM (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f) (tO n ℓ₁ f₁ m q ℓ f)) :=
  bCirc (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f) (tO n ℓ₁ f₁ m q ℓ f) (tO_valid n ℓ₁ f₁ m q ℓ f hf hℓ)

/-- Start of the `c₃` region. -/
abbrev Q3 : ℕ := offM n ℓ₁ f₁ m q ℓ f + (tP n ℓ₁ f₁ m q ℓ f).length + 2

end Layout

end LTFC

namespace LTFC

section Circ

variable (n ℓ₁ f₁ m q ℓ f : ℕ) (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)
  (b Vb W : ℕ) (m₃ ℓo₃ fo₃ : ℕ) (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)) (Pp : ℕ)

abbrev Lw : ℕ := if ℓo₃ = 0 then 1 else ℓo₃
abbrev Fw : ℕ := if ℓo₃ = 0 then fo₃ + 1 else fo₃
abbrev fw : ℕ := min (Fw ℓo₃ fo₃) Pp
abbrev loW : ℕ := Fw ℓo₃ fo₃ - fw ℓo₃ fo₃ Pp
abbrev Kw : ℕ := fw ℓo₃ fo₃ Pp + 6
abbrev foT : ℕ := fw ℓo₃ fo₃ Pp + q + 2
abbrev ℓoT : ℕ := foT q ℓo₃ fo₃ Pp + Kw ℓo₃ fo₃ Pp + Bh m q + 2
abbrev Bw : ℕ := Q3 n ℓ₁ f₁ m q ℓ f + m₃

def srcs : List (ℕ → ℕ) :=
  List.ofFn (fun i : Fin n => fun k =>
    if h : k < ℓo₃ then Q3 n ℓ₁ f₁ m q ℓ f + (oa₃ i ⟨ℓo₃ - 1 - k, by omega⟩).val
    else Bw n ℓ₁ f₁ m q ℓ f m₃)

def winR : List (List ℕ) × List (OIns (n * ℓ)) :=
  winAll (Bw n ℓ₁ f₁ m q ℓ f m₃) (Lw ℓo₃) (loW ℓo₃ fo₃ Pp) (Kw ℓo₃ fo₃ Pp)
    (srcs n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃) (p0g (Bw n ℓ₁ f₁ m q ℓ f m₃))

abbrev Bo : ℕ := Bw n ℓ₁ f₁ m q ℓ f m₃ + (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2.length

abbrev sbv : ℕ := n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f
abbrev eqv : ℕ := offM n ℓ₁ f₁ m q ℓ f + (tP n ℓ₁ f₁ m q ℓ f).length
abbrev cv : ℕ := offM n ℓ₁ f₁ m q ℓ f + (tP n ℓ₁ f₁ m q ℓ f).length + 1

def hLw : List ℕ := (List.range (Bh m q)).map (fun i => n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f + 1 + (Bh m q - 1 - i))

def Pout : List (OIns (n * ℓ)) :=
  outProg (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (ℓoT m q ℓo₃ fo₃ Pp) (foT q ℓo₃ fo₃ Pp)
    (Kw ℓo₃ fo₃ Pp) (fw ℓo₃ fo₃ Pp) (Bh m q) (q + 1) n (sbv n ℓ₁ f₁ m q ℓ f)
    (eqv n ℓ₁ f₁ m q ℓ f) (cv n ℓ₁ f₁ m q ℓ f) (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1
    (hLw n ℓ₁ f₁ m q ℓ f)

abbrev Bc : ℕ :=
  outBc (K := n * ℓ) (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (ℓoT m q ℓo₃ fo₃ Pp) (foT q ℓo₃ fo₃ Pp)
    (Kw ℓo₃ fo₃ Pp) (fw ℓo₃ fo₃ Pp) (Bh m q) (q + 1) (sbv n ℓ₁ f₁ m q ℓ f)
    (eqv n ℓ₁ f₁ m q ℓ f) (cv n ℓ₁ f₁ m q ℓ f) (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1
    (hLw n ℓ₁ f₁ m q ℓ f)

abbrev MT : ℕ := Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp + (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).length

include hf hℓ in
theorem winR_spec (O : (Fin (n * ℓ) → Bool) → Bool) :
    (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2.length = 2 + n * Kw ℓo₃ fo₃ Pp ∧
    (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1.length = n ∧
    (∀ X ∈ (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1, X.length = Kw ℓo₃ fo₃ Pp ∧
      ∀ v ∈ X, v < Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) ∧
    HoldsO O (Bw n ℓ₁ f₁ m q ℓ f m₃) (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2 (fun σ =>
      ∀ i < n, ((numVal σ ((winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1.getD i []) : ℕ) : ℤ) =
        sumBits (fun j => xor (sext (fun k => σ (((srcs n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃).getD i
          (fun _ => 0)) k)) (Lw ℓo₃) (loW ℓo₃ fo₃ Pp + j)) (decide (j = Kw ℓo₃ fo₃ Pp - 1)))
          (Kw ℓo₃ fo₃ Pp)) := by
  have hsl : (srcs n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃).length = n := by simp [srcs]
  obtain ⟨e, l, o, v, h⟩ := winAll_spec O (Bw n ℓ₁ f₁ m q ℓ f m₃) (Lw ℓo₃) (loW ℓo₃ fo₃ Pp)
    (Kw ℓo₃ fo₃ Pp) (by simp only [Lw]; split_ifs <;> omega) (srcs n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃)
    (p0g (Bw n ℓ₁ f₁ m q ℓ f m₃)) (by
      intro s hs i hi
      simp only [srcs, List.mem_ofFn] at hs
      obtain ⟨j, rfl⟩ := hs
      simp only [p0g, List.length_cons, List.length_nil]
      split_ifs with h
      · have := (oa₃ j ⟨ℓo₃ - 1 - i, by omega⟩).isLt; simp only [Bw]; omega
      · omega)
  refine ⟨by rw [winR, l, hsl]; simp [p0g], by rw [winR, o, hsl], ?_, ?_⟩
  · intro X hX; exact v X hX
  · refine h.imp ?_
    intro σ h i hi
    exact h i (by rw [hsl]; exact hi)

end Circ

end LTFC

namespace LTFC

section Circ2

variable (n ℓ₁ f₁ m q ℓ f : ℕ) (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)
  (b Vb W : ℕ) (m₃ ℓo₃ fo₃ : ℕ) (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)) (Pp : ℕ)

theorem offM_le_Q3 : offM n ℓ₁ f₁ m q ℓ f ≤ Q3 n ℓ₁ f₁ m q ℓ f := by simp only [Q3]; omega

theorem Q3_le_MT : Q3 n ℓ₁ f₁ m q ℓ f + m₃ ≤ MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp := by
  simp only [MT, Bo, Bw]; omega

theorem offM_le_MT : offM n ℓ₁ f₁ m q ℓ f ≤ MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp := by
  have := Q3_le_MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp
  have := offM_le_Q3 n ℓ₁ f₁ m q ℓ f
  omega

theorem nl_le_offM : n * ℓ₁ ≤ offM n ℓ₁ f₁ m q ℓ f := by simp only [offM]; omega

def pinG : Fin (n * ℓ₁) ↪ Fin (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt ((nl_le_offM n ℓ₁ f₁ m q ℓ f).trans
      (offM_le_MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp))⟩,
    fun i j h => by simp only [Fin.mk.injEq] at h; exact Fin.ext h⟩

def offE : Fin (offM n ℓ₁ f₁ m q ℓ f) ↪ Fin (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt (offM_le_MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)⟩,
    fun i j h => by simp only [Fin.mk.injEq] at h; exact Fin.ext h⟩

def testE : Fin (bM (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f) (tO n ℓ₁ f₁ m q ℓ f)) ↪
    Fin (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  ⟨fun i => ⟨if i.val < n * ℓ₁ then i.val else offM n ℓ₁ f₁ m q ℓ f + (i.val - n * ℓ₁), by
      have := Q3_le_MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp
      have := offM_le_Q3 n ℓ₁ f₁ m q ℓ f
      have := tO_length n ℓ₁ f₁ m q ℓ f hf hℓ
      have hi := i.isLt
      simp only [bM, Q3, offM] at *
      split_ifs <;> omega⟩, by
    intro i j h
    simp only [Fin.mk.injEq] at h
    have := offM_le_Q3 n ℓ₁ f₁ m q ℓ f
    apply Fin.ext
    simp only [offM] at *
    split_ifs at h <;> omega⟩

def ιE : Fin m₃ ↪ Fin (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  ⟨fun j => ⟨Q3 n ℓ₁ f₁ m q ℓ f + j.val, by
      have := Q3_le_MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp; have := j.isLt; omega⟩,
    fun i j h => by simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩

theorem ιE_val (j : Fin m₃) : (ιE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp j).val =
    Q3 n ℓ₁ f₁ m q ℓ f + j.val := rfl

def πE : Fin (n * ℓ₁ + 1 + Bh m q) ↪ Fin (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  ⟨fun i => ⟨if i.val < n * ℓ₁ then i.val else n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f + (i.val - n * ℓ₁), by
      have := Q3_le_MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp
      have := offM_le_Q3 n ℓ₁ f₁ m q ℓ f
      have hi := i.isLt
      simp only [offM] at *
      split_ifs <;> omega⟩, by
    intro i j h
    simp only [Fin.mk.injEq] at h
    apply Fin.ext
    split_ifs at h <;> omega⟩

theorem πE_val (i : Fin (n * ℓ₁ + 1 + Bh m q)) :
    (πE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i).val =
      if i.val < n * ℓ₁ then i.val else n * ℓ₁ + offL n ℓ₁ f₁ m q ℓ f + (i.val - n * ℓ₁) := rfl

theorem πE_lt (i : Fin (n * ℓ₁ + 1 + Bh m q)) :
    (πE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i).val < offM n ℓ₁ f₁ m q ℓ f := by
  rw [πE_val]; have := i.isLt; simp only [offM]; split_ifs <;> omega

theorem hdE : ∀ i j, πE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i ≠ ιE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp j := by
  intro i j h
  have h1 := πE_lt n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i
  have h2 := congrArg Fin.val h
  have := offM_le_Q3 n ℓ₁ f₁ m q ℓ f
  rw [ιE_val] at h2
  omega

include hf hℓ in
theorem Pout_spec (O : (Fin (n * ℓ) → Bool) → Bool) :
    Bc n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp + (n + 1) * ℓoT m q ℓo₃ fo₃ Pp =
      MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp ∧
    (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).length =
      3 + n * (15 * ℓoT m q ℓo₃ fo₃ Pp) + 18 * ℓoT m q ℓo₃ fo₃ Pp + (n + 1) * ℓoT m q ℓo₃ fo₃ Pp ∧
    HoldsO O (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (fun σ =>
      (∀ i < n, QuantumLTF.Membership.fpVal (ℓoT m q ℓo₃ fo₃ Pp) (foT q ℓo₃ fo₃ Pp)
          (fun t => σ (Bc n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp + i * ℓoT m q ℓo₃ fo₃ Pp + t.val)) =
        if σ (eqv n ℓ₁ f₁ m q ℓ f) then 0 else
          -(sgnS (σ (sbv n ℓ₁ f₁ m q ℓ f))) * QuantumLTF.Membership.fpVal (Kw ℓo₃ fo₃ Pp)
            (fw ℓo₃ fo₃ Pp) (msbBits σ (Kw ℓo₃ fo₃ Pp)
              ((winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1.getD i []))) ∧
      QuantumLTF.Membership.fpVal (ℓoT m q ℓo₃ fo₃ Pp) (foT q ℓo₃ fo₃ Pp)
          (fun t => σ (Bc n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp + n * ℓoT m q ℓo₃ fo₃ Pp + t.val)) =
        if σ (eqv n ℓ₁ f₁ m q ℓ f) then (if σ (cv n ℓ₁ f₁ m q ℓ f) then 1 else 0) else
          sgnS (σ (sbv n ℓ₁ f₁ m q ℓ f)) * QuantumLTF.Membership.fpVal (Bh m q) (q + 1)
            (msbBits σ (Bh m q) (hLw n ℓ₁ f₁ m q ℓ f))) := by
  obtain ⟨wl, wo, wv, _⟩ := winR_spec n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp O
  have hBo := Q3_le_MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp
  have hoQ := offM_le_Q3 n ℓ₁ f₁ m q ℓ f
  have hB1 : offM n ℓ₁ f₁ m q ℓ f ≤ Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp := by
    simp only [Bo, Bw]; omega
  have hQ : Q3 n ℓ₁ f₁ m q ℓ f ≤ Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp := by simp only [Bo, Bw]; omega
  have := outProg_spec O (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (ℓoT m q ℓo₃ fo₃ Pp)
    (foT q ℓo₃ fo₃ Pp) (Kw ℓo₃ fo₃ Pp) (fw ℓo₃ fo₃ Pp) (Bh m q) (q + 1) n
    (sbv n ℓ₁ f₁ m q ℓ f) (eqv n ℓ₁ f₁ m q ℓ f) (cv n ℓ₁ f₁ m q ℓ f)
    (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1 (hLw n ℓ₁ f₁ m q ℓ f)
    (by simp only [sbv, offM] at *; omega) (by simp only [eqv, Q3] at *; omega)
    (by simp only [cv, Q3] at *; omega) wo wv (by simp [hLw])
    (by intro v hv; simp only [hLw, List.mem_map, List.mem_range] at hv
        obtain ⟨i, hi, rfl⟩ := hv; simp only [offM] at hB1; omega)
    (by simp only [foT]; omega) (by simp only [foT]; omega) (by simp only [ℓoT]; omega)
    (by simp only [ℓoT]; omega)
  exact ⟨by rw [this.1]; rfl, this.2⟩

end Circ2

end LTFC

-- ===== module Assembly2 =====

open QAlgorithms

namespace LTFC

theorem embedOp_bv_classical {k M : ℕ} (A : Matrix (Qubits k) (Qubits k) ℂ) (e : Fin k ↪ Fin M)
    (Y : Qubits M) (z' : Qubits k) (h : A.mulVec (bv (Y ∘ e)) = bv z') :
    (embedOp A e).mulVec (bv Y) = bv (setPart Y e z') := by
  rw [embedOp_mulVec_bv]
  have hA : ∀ u, A u (Y ∘ e) = if u = z' then 1 else 0 := by
    intro u
    have := congrFun h u
    rw [Matrix.mulVec_single_one] at this
    simpa [bv, Pi.single_apply] using this
  simp only [hA, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ z']
  simp

theorem prob_inj {k M : ℕ} (G : Qubits k → Qubits M) (hG : Function.Injective G) (a : Qubits k → ℂ)
    (P : Qubits M → Prop) [DecidablePred P] :
    ∑ z ∈ Finset.univ.filter P, ‖(∑ u, a u • bv (G u)) z‖ ^ 2 =
      ∑ u ∈ Finset.univ.filter (fun u => P (G u)), ‖a u‖ ^ 2 := by
  have hval : ∀ u, (∑ u', a u' • bv (G u')) (G u) = a u := by
    intro u
    simp only [Finset.sum_apply, Pi.smul_apply, bv, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_eq_single u]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (hG h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  have hoff : ∀ z, z ∉ Set.range G → (∑ u', a u' • bv (G u')) z = 0 := by
    intro z hz
    simp only [Finset.sum_apply, Pi.smul_apply, bv, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    apply Finset.sum_eq_zero
    intro u _; rw [if_neg]; intro h; exact hz ⟨u, h.symm⟩
  symm
  apply Finset.sum_of_injOn G (fun x _ y _ h => hG h)
  · intro u hu; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    exact hu
  · intro z hzP hz
    have : z ∉ Set.range G := by
      rintro ⟨u, rfl⟩; apply hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzP
      exact ⟨u, by simpa using hzP, rfl⟩
    rw [hoff z this]; simp
  · intro u _; rw [hval]

theorem bval_sumBits (l : List Bool) : (bval l : ℤ) = sumBits (fun k => l.getD k false) l.length := by
  induction l with
  | nil => simp [bval, sumBits]
  | cons b bs ih =>
    rw [show (b :: bs).length = 1 + bs.length by simp [Nat.add_comm], sumBits_add]
    simp only [bval, sumBits, Finset.sum_range_one, List.getD_cons_zero, pow_zero, mul_one,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_one] at ih ⊢
    rw [ih]
    simp [List.getD_cons_succ, Nat.add_comm]

theorem bitsToNat_sumBits {L : ℕ} (d : Fin L → Bool) :
    (bitsToNat d : ℤ) = sumBits (fun k => if h : k < L then d ⟨L - 1 - k, by omega⟩ else false) L := by
  rw [← bval_rev_bits, bval_sumBits]
  simp only [List.length_map, List.length_range]
  unfold sumBits
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  simp [List.getD_eq_getElem?_getD, hk]
  split_ifs <;> first | rfl | omega

theorem toN_fin {M : ℕ} (Y : Qubits M) (v : Fin M) : toN Y v.val = Y v := by
  simp [toN, v.isLt]

theorem toN_setPart_emb {k M : ℕ} (Y : Qubits M) (e : Fin k ↪ Fin M) (z : Qubits k) (a : Fin k)
    (v : ℕ) (hv : (e a).val = v) : toN (setPart Y e z) v = z a := by
  subst hv; rw [toN_fin, setPart_emb]

theorem toN_setPart_off {k M : ℕ} (Y : Qubits M) (e : Fin k ↪ Fin M) (z : Qubits k) (v : ℕ)
    (hv : ∀ a, (e a).val ≠ v) : toN (setPart Y e z) v = toN Y v := by
  unfold toN
  split_ifs with h
  · rw [setPart_off]; rintro ⟨a, ha⟩; exact hv a (by rw [ha])
  · rfl

theorem toN_comp {k M : ℕ} (Y : Qubits M) (e : Fin k ↪ Fin M) (a : ℕ) (ha : a < k) (v : ℕ)
    (hv : (e ⟨a, ha⟩).val = v) : toN (Y ∘ e) a = toN Y v := by
  subst hv; simp [toN, ha]

theorem toN_false {M : ℕ} (v : ℕ) : toN (fun _ : Fin M => false) v = false := by
  simp [toN]

section Stage

variable (n ℓ₁ f₁ m q ℓ f : ℕ) (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)
  (m₃ ℓo₃ fo₃ : ℕ) (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)) (Pp : ℕ)

theorem pinG_val (i : Fin (n * ℓ₁)) : (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i).val = i.val := by
  unfold pinG; rfl
theorem offE_val (i : Fin (offM n ℓ₁ f₁ m q ℓ f)) :
    (offE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i).val = i.val := by
  unfold offE; rfl
theorem testE_val (i : Fin (bM (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f) (tO n ℓ₁ f₁ m q ℓ f))) :
    (testE n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp i).val =
      if i.val < n * ℓ₁ then i.val else offM n ℓ₁ f₁ m q ℓ f + (i.val - n * ℓ₁) := by
  unfold testE; rfl

include hf hℓ in
theorem stageA (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (u : Qubits (n * ℓ₁)) :
    ∃ Y2 : Qubits (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp),
      ((relabel (testCirc n ℓ₁ f₁ m q ℓ f hf hℓ)
          (testE n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp)).unitary
          (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) *
        (relabel (offCirc n ℓ₁ f₁ m q ℓ f hf hℓ) (offE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)).unitary
          (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)).mulVec
        (bv (setPart (fun _ => false) (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) u)) = bv Y2 ∧
      (∀ i : Fin (n * ℓ₁), toN Y2 i.val = u i) ∧
      (∀ v, Q3 n ℓ₁ f₁ m q ℓ f ≤ v → toN Y2 v = false) ∧
      toN Y2 (sbv n ℓ₁ f₁ m q ℓ f) = decide
          (((QuantumLTF.Membership.boundarySearchTreeStrict
            (QuantumLTF.Membership.addrOf n ℓ₁ f₁ u) ((2 : ℝ) ^ m) q).run
            (QuantumLTF.Membership.ltf w θ)).1 = 1) ∧
      QuantumLTF.Membership.fpVal (Bh m q) (q + 1)
          (fun t => toN Y2 (sbv n ℓ₁ f₁ m q ℓ f + 1 + t.val)) =
          ((QuantumLTF.Membership.boundarySearchTreeStrict
            (QuantumLTF.Membership.addrOf n ℓ₁ f₁ u) ((2 : ℝ) ^ m) q).run
            (QuantumLTF.Membership.ltf w θ)).2 ∧
      toN Y2 (cv n ℓ₁ f₁ m q ℓ f) = decide (QuantumLTF.Membership.ltf w θ
          (((2 : ℝ) ^ m) • QuantumLTF.Membership.addrOf n ℓ₁ f₁ u) = -1) ∧
      toN Y2 (eqv n ℓ₁ f₁ m q ℓ f) = (toN Y2 (cv n ℓ₁ f₁ m q ℓ f) ==
          decide (QuantumLTF.Membership.ltf w θ
          ((-((2 : ℝ) ^ m)) • QuantumLTF.Membership.addrOf n ℓ₁ f₁ u) = -1)) := by
  obtain ⟨uo, -, -, hoff⟩ := offset_circuit n ℓ₁ f₁ m q ℓ f hf hℓ
  have htl := tO_length n ℓ₁ f₁ m q ℓ f hf hℓ
  have hoQ := offM_le_Q3 n ℓ₁ f₁ m q ℓ f
  have hnl := nl_le_offM n ℓ₁ f₁ m q ℓ f
  obtain ⟨X, hXd⟩ : ∃ X, X = setPart (fun _ => false) (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) u :=
    ⟨_, rfl⟩
  rw [← hXd]
  have hX : ∀ v, toN X v = if h : v < n * ℓ₁ then u ⟨v, h⟩ else false := by
    intro v
    split_ifs with h
    · rw [hXd]; exact toN_setPart_emb _ _ _ ⟨v, h⟩ v rfl
    · rw [hXd, toN_setPart_off _ _ _ _ (fun a ha => h (by rw [← ha, pinG_val]; exact a.isLt)), toN_false]
  obtain ⟨z1, hz1d⟩ : ∃ z1, z1 = X ∘ offE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp := ⟨_, rfl⟩
  have hz1v : ∀ v (hv : v < offM n ℓ₁ f₁ m q ℓ f), toN z1 v = toN X v :=
    fun v hv => by rw [hz1d]; exact toN_comp _ _ v hv v rfl
  have hz1 : ∀ v : Fin (offM n ℓ₁ f₁ m q ℓ f), n * ℓ₁ ≤ v.val → z1 v = false := by
    intro v hv; rw [← toN_fin z1 v, hz1v _ v.isLt, hX, dif_neg (by omega)]
  obtain ⟨z1', h1, hk1, hsw1, hhw1⟩ := hoff w θ z1 hz1
  obtain ⟨Y1, hY1d⟩ : ∃ Y1, Y1 = setPart X (offE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) z1' := ⟨_, rfl⟩
  have hY1a : ∀ v (hv : v < offM n ℓ₁ f₁ m q ℓ f), toN Y1 v = z1' ⟨v, hv⟩ :=
    fun v hv => by rw [hY1d]; exact toN_setPart_emb _ _ _ ⟨v, hv⟩ v rfl
  have hY1b : ∀ v, offM n ℓ₁ f₁ m q ℓ f ≤ v → toN Y1 v = false := by
    intro v hv
    rw [hY1d, toN_setPart_off _ _ _ _ (fun a ha => by
      have := a.isLt; rw [offE_val] at ha; omega), hX,
      dif_neg (by omega)]
  have hpin : z1 ∘ offPin n ℓ₁ f₁ m q ℓ f = u := by
    funext i
    simp only [Function.comp_apply]
    rw [← toN_fin z1, show ((offPin n ℓ₁ f₁ m q ℓ f) i).val = i.val from rfl,
      hz1v _ (by have := i.isLt; omega), hX, dif_pos i.isLt]
  have hU1 : ((relabel (offCirc n ℓ₁ f₁ m q ℓ f hf hℓ)
      (offE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)).unitary
      (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)).mulVec (bv X) = bv Y1 := by
    rw [relabel_unitary _ _ uo, hY1d]; exact embedOp_bv_classical _ _ _ _ (by rw [← hz1d]; exact h1)
  obtain ⟨ut, -, -, hbt⟩ := bennett (K := n * ℓ) (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f)
    (tO n ℓ₁ f₁ m q ℓ f) (tO_valid n ℓ₁ f₁ m q ℓ f hf hℓ)
  obtain ⟨z2, hz2d⟩ : ∃ z2, z2 = Y1 ∘ testE n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp := ⟨_, rfl⟩
  have hz2 : ∀ v : Fin (bM (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f) (tO n ℓ₁ f₁ m q ℓ f)),
      n * ℓ₁ ≤ v.val → z2 v = false := by
    intro v hv
    rw [← toN_fin z2 v, hz2d, toN_comp _ _ v.val v.isLt (offM n ℓ₁ f₁ m q ℓ f + (v.val - n * ℓ₁))
      (by rw [testE_val]; simp only [Fin.val_mk]; rw [if_neg (by omega)]),
      hY1b _ (by omega)]
  have hz2low : ∀ v (hv : v < n * ℓ₁), toN z2 v = u ⟨v, hv⟩ := by
    intro v hv
    have hvb : v < bM (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f) (tO n ℓ₁ f₁ m q ℓ f) := by
      simp only [bM]; omega
    rw [hz2d, toN_comp _ _ v hvb v (by rw [testE_val, if_pos hv]),
      hY1a v (by omega), hk1 ⟨v, by omega⟩ (by
        intro h; have := congrArg Fin.val h; simp only [offSw] at this; omega) (by
        rintro ⟨t, ht⟩; have := congrArg Fin.val ht; rw [offHw_val] at this; simp only [Fin.val_mk] at this; omega),
      ← toN_fin z1, hz1v _ (by omega), hX, dif_pos hv]
  obtain ⟨z2', h2, hk2, hout2⟩ := hbt (Owt n ℓ f w θ) (QuantumLTF.Membership.memOracle n ℓ f w θ)
    (memOracle_classical n ℓ f w θ) z2 hz2
  have hbM : bM (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f) (tO n ℓ₁ f₁ m q ℓ f) =
      n * ℓ₁ + (tP n ℓ₁ f₁ m q ℓ f).length + 2 := by simp only [bM, htl]
  have hY2off : ∀ v, (∀ a, (testE n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp a).val ≠ v) →
      toN (setPart Y1 (testE n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp) z2') v = toN Y1 v :=
    fun v hv => toN_setPart_off _ _ _ _ hv
  have hmid : ∀ v, n * ℓ₁ ≤ v → v < offM n ℓ₁ f₁ m q ℓ f →
      ∀ a, (testE n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp a).val ≠ v := by
    intro v h1 h2 a ha
    rw [testE_val] at ha
    split_ifs at ha <;> omega
  have hpin' : QuantumLTF.Membership.addrOf n ℓ₁ f₁ (z1 ∘ offPin n ℓ₁ f₁ m q ℓ f) =
      QuantumLTF.Membership.addrOf n ℓ₁ f₁ u := by rw [hpin]
  have hsvl : ∀ i : Fin (n * ℓ₁), svalO (Owt n ℓ f w θ) (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f)
      (toN z2) i.val = u i := by
    intro i; rw [svalO_lt _ _ _ _ i.isLt, hz2low _ i.isLt]
  have hpb : pBits n ℓ₁ (svalO (Owt n ℓ f w θ) (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f) (toN z2)) = u := by
    funext i; exact hsvl i
  have hT := (testProg_spec n ℓ₁ f₁ m q ℓ f hf hℓ w θ).2.2.2.2 [] (toN z2)
  simp only [List.append_nil] at hT
  rw [hpb] at hT
  have hbo : ∀ (t : ℕ) (ht : t < (tO n ℓ₁ f₁ m q ℓ f).length),
      toN (setPart Y1 (testE n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp) z2')
        (offM n ℓ₁ f₁ m q ℓ f + (tP n ℓ₁ f₁ m q ℓ f).length + t) =
        svalO (Owt n ℓ f w θ) (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f) (toN z2)
          ((tO n ℓ₁ f₁ m q ℓ f).getD t 0) := by
    intro t ht
    rw [toN_setPart_emb _ _ _ (bOut (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f) (tO n ℓ₁ f₁ m q ℓ f) ⟨t, ht⟩) _
      (by rw [testE_val]; simp only [bOut, Fin.val_mk,
        show ¬ (n * ℓ₁ + (tP n ℓ₁ f₁ m q ℓ f).length + t < n * ℓ₁) by omega, ↓reduceIte]; omega), hout2]
    rw [List.getD_eq_getElem _ _ ht]
  refine ⟨setPart Y1 (testE n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp) z2', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, hU1, relabel_unitary (testCirc n ℓ₁ f₁ m q ℓ f hf hℓ) _ ut]
    exact embedOp_bv_classical _ _ _ _ (by rw [← hz2d]; exact h2)
  · intro i
    have hib : i.val < bM (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f) (tO n ℓ₁ f₁ m q ℓ f) := by
      have := i.isLt; omega
    rw [toN_setPart_emb _ _ _ ⟨i.val, hib⟩ _ (by rw [testE_val]; simp only [Fin.val_mk]; rw [if_pos i.isLt]),
      hk2 _ (by simp only [Fin.val_mk]; have := i.isLt; omega), ← toN_fin z2, hz2low _ i.isLt]
  · intro v hv
    rw [hY2off v (by
      intro a ha; rw [testE_val] at ha; have : a.val < _ := lt_of_lt_of_eq a.isLt hbM
      simp only [Q3] at hv; split_ifs at ha <;> omega), hY1b _ (by simp only [Q3] at hv; omega)]
  · rw [hY2off _ (hmid _ (by simp only [sbv]; omega) (by simp only [sbv, offM]; omega)),
      hY1a _ (by simp only [sbv, offM]; omega),
      show (⟨sbv n ℓ₁ f₁ m q ℓ f, _⟩ : Fin (offM n ℓ₁ f₁ m q ℓ f)) = offSw n ℓ₁ f₁ m q ℓ f from
        Fin.ext (by rw [offSw_val]),
      hsw1, hpin']
  · rw [← hpin', ← hhw1]
    refine congrArg (QuantumLTF.Membership.fpVal (Bh m q) (q + 1)) ?_
    funext t
    simp only [Function.comp_apply]
    rw [hY2off _ (hmid _ (by simp only [sbv]; omega) (by have := t.isLt; simp only [sbv, offM]; omega)),
      hY1a _ (by have := t.isLt; simp only [sbv, offM]; omega)]
    exact congrArg z1' (Fin.ext (by rw [offHw_val]))
  · rw [show cv n ℓ₁ f₁ m q ℓ f = offM n ℓ₁ f₁ m q ℓ f + (tP n ℓ₁ f₁ m q ℓ f).length + 1 from rfl,
      hbo 1 (by omega)]
    exact hT.1
  · rw [show cv n ℓ₁ f₁ m q ℓ f = offM n ℓ₁ f₁ m q ℓ f + (tP n ℓ₁ f₁ m q ℓ f).length + 1 from rfl,
      show eqv n ℓ₁ f₁ m q ℓ f = offM n ℓ₁ f₁ m q ℓ f + (tP n ℓ₁ f₁ m q ℓ f).length + 0 from rfl,
      hbo 1 (by omega), hbo 0 (by omega)]
    exact hT.2

end Stage

section StageB

variable (n ℓ₁ f₁ m q ℓ f : ℕ) (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)
  (m₃ ℓo₃ fo₃ : ℕ) (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)) (Pp : ℕ) (b Vb W : ℕ)
  (cA : OracleCircuit QuantumLTF.Membership.gatesRev (fun _ : Fin 1 => n * ℓ + 1)
    (n * ℓ₁ + 1 + Bh m q + (n * b + Vb + W)))
  (c₃ : OracleCircuit G12 (fun _ : Fin 1 => n * b + Vb + W) m₃)

noncomputable def cSub : OracleCircuit G12 (fun _ : Fin 1 => n * ℓ + 1)
    (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  substC (ιE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (πE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
    (hdE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (convC cA) c₃

noncomputable def cWin : OracleCircuit G12 (fun _ : Fin 1 => n * ℓ + 1)
    (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  compileO (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2
    (Bw n ℓ₁ f₁ m q ℓ f m₃)

noncomputable def cOut : OracleCircuit G12 (fun _ : Fin 1 => n * ℓ + 1)
    (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  compileO (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
    (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)

noncomputable def cAll : OracleCircuit G12 (fun _ : Fin 1 => n * ℓ + 1)
    (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  hadCirc (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) ++
  relabel (offCirc n ℓ₁ f₁ m q ℓ f hf hℓ) (offE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) ++
  relabel (testCirc n ℓ₁ f₁ m q ℓ f hf hℓ) (testE n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp) ++
  cSub n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃ ++
  cWin n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp ++
  cOut n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp

/-- The classical post-processing map (window extraction, then output formatting). -/
def Fpost (O : (Fin (n * ℓ) → Bool) → Bool) :
    Qubits (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) → Qubits (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  runPO (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) O (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
      (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) ∘
    runPO (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) O (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2
      (Bw n ℓ₁ f₁ m q ℓ f m₃)

theorem Fpost_inj (O : (Fin (n * ℓ) → Bool) → Bool) :
    Function.Injective (Fpost n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp O) := by
  intro x y h
  have := congrArg (fun z => runRevO _ O (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2
    (Bw n ℓ₁ f₁ m q ℓ f m₃) (runRevO _ O (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
      (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) z)) h
  simp only [Fpost, Function.comp_apply, runRevO_runPO] at this
  exact this

theorem stageB (hAu : QuantumLTF.Membership.Uncontrolled cA)
    (h3u : QuantumLTF.Membership.Uncontrolled c₃) (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
    (hBD : BlockDiag (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ))
    (Y2 : Qubits (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp))
    (hY2 : ∀ v, Q3 n ℓ₁ f₁ m q ℓ f ≤ v → toN Y2 v = false) :
    ((cOut n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).unitary
        (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) *
      ((cWin n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).unitary
        (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) *
      (cSub n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃).unitary
        (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ))).mulVec (bv Y2) =
      ∑ y' : Qubits m₃, (c₃.unitary fun _ => blockOf (cA.unitary
          fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
          (Y2 ∘ πE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)) y' (fun _ => false) •
        bv (Fpost n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp (Owt n ℓ f w θ)
          (setPart Y2 (ιE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) y')) := by
  have hMo := memOracle_classical n ℓ f w θ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hsub := substC_spec (ιE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
    (πE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (hdE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (convC cA)
    (convC_counts cA hAu 0).1 (QuantumLTF.Membership.memOracle n ℓ f w θ)
    (by rw [convC_unitary]; exact hBD) c₃ h3u (Y2 ∘ πE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (bv Y2)
    (by intro Y hY; simp only [bv, Pi.single_apply] at hY; split_ifs at hY with h
        · rw [h]
        · exact absurd rfl hY)
  rw [convC_unitary] at hsub
  rw [show (cSub n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃) = substC _ _ _ (convC cA) c₃ from rfl,
    hsub, embedOp_mulVec_bv]
  have hz : Y2 ∘ ιE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp = fun _ => false := by
    funext j
    rw [Function.comp_apply, ← toN_fin Y2, ιE_val]
    exact hY2 _ (by omega)
  rw [hz, Matrix.mulVec_sum, Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro y' _
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
  refine congrArg (HSMul.hSMul _) ?_
  rw [show (cWin n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) = compileO _ _ _ from rfl,
    show (cOut n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) = compileO _ _ _ from rfl,
    impl_compileO _ _ _ hMo, impl_compileO _ _ _ hMo]
  simp only [Fpost, Function.comp_apply]
  rfl

end StageB

section StageC

variable (n ℓ₁ f₁ m q ℓ f : ℕ) (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)
  (m₃ ℓo₃ fo₃ : ℕ) (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)) (Pp : ℕ)

theorem winR_ext : ExtL (p0g (K := n * ℓ) (Bw n ℓ₁ f₁ m q ℓ f m₃))
    (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2 := by
  exact (winAll_spec (fun _ => false) (Bw n ℓ₁ f₁ m q ℓ f m₃) (Lw ℓo₃) (loW ℓo₃ fo₃ Pp)
    (Kw ℓo₃ fo₃ Pp) (by simp only [Lw]; split_ifs <;> omega) (srcs n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃)
    (p0g (Bw n ℓ₁ f₁ m q ℓ f m₃)) (by
      intro s hs i hi
      simp only [srcs, List.mem_ofFn] at hs
      obtain ⟨j, rfl⟩ := hs
      simp only [p0g, List.length_cons, List.length_nil]
      split_ifs with h
      · have := (oa₃ j ⟨ℓo₃ - 1 - i, by omega⟩).isLt; simp only [Bw]; omega
      · omega)).1

include hf hℓ in
theorem BcEq : Bc n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp + (n + 1) * ℓoT m q ℓo₃ fo₃ Pp =
    MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp :=
  (Pout_spec n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp (fun _ => false)).1

def oaT (i : Fin n) : Fin (ℓoT m q ℓo₃ fo₃ Pp) ↪ Fin (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  ⟨fun t => ⟨Bc n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp + i.val * ℓoT m q ℓo₃ fo₃ Pp + t.val, by
      have h := BcEq n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp
      have h2 := Nat.mul_le_mul_right (ℓoT m q ℓo₃ fo₃ Pp) (show i.val + 1 ≤ n + 1 by omega)
      rw [Nat.add_mul, one_mul] at h2
      have := t.isLt
      omega⟩, fun a b h => by simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩

def obT : Fin (ℓoT m q ℓo₃ fo₃ Pp) ↪ Fin (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) :=
  ⟨fun t => ⟨Bc n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp + n * ℓoT m q ℓo₃ fo₃ Pp + t.val, by
      have h := BcEq n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp
      rw [Nat.add_mul, one_mul] at h
      have := t.isLt
      omega⟩, fun a b h => by simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩

theorem oaT_val (i : Fin n) (t : Fin (ℓoT m q ℓo₃ fo₃ Pp)) :
    (oaT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp i t).val =
      Bc n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp + i.val * ℓoT m q ℓo₃ fo₃ Pp + t.val := by
  unfold oaT; rfl

theorem obT_val (t : Fin (ℓoT m q ℓo₃ fo₃ Pp)) :
    (obT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp t).val =
      Bc n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp + n * ℓoT m q ℓo₃ fo₃ Pp + t.val := by
  unfold obT; rfl

/-- Bits of the `i`-th gradient estimate of `c₃`, least significant first. -/
def eW (i : Fin n) (y' : Qubits m₃) (k : ℕ) : Bool :=
  if h : k < ℓo₃ then y' (oa₃ i ⟨ℓo₃ - 1 - k, by omega⟩) else false

/-- The truncated value written by the window program. -/
noncomputable def gW (i : Fin n) (y' : Qubits m₃) : ℝ :=
  ((sumBits (fun j => xor (sext (eW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃ i y') (Lw ℓo₃) (loW ℓo₃ fo₃ Pp + j))
      (decide (j = Kw ℓo₃ fo₃ Pp - 1))) (Kw ℓo₃ fo₃ Pp) - 2 ^ (Kw ℓo₃ fo₃ Pp - 1) : ℤ) : ℝ) /
    2 ^ fw ℓo₃ fo₃ Pp

theorem srcs_getD (i : Fin n) : (srcs n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃).getD i.val (fun _ => 0) =
    fun k => if h : k < ℓo₃ then Q3 n ℓ₁ f₁ m q ℓ f + (oa₃ i ⟨ℓo₃ - 1 - k, by omega⟩).val
      else Bw n ℓ₁ f₁ m q ℓ f m₃ := by
  unfold srcs
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

include hf hℓ in
theorem stageC (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
    (Y2 : Qubits (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp))
    (hY2 : ∀ v, Q3 n ℓ₁ f₁ m q ℓ f ≤ v → toN Y2 v = false) (y' : Qubits m₃)
    (Z : Qubits (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp))
    (hZ : Z = Fpost n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp (Owt n ℓ f w θ)
      (setPart Y2 (ιE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) y')) :
    (∀ v, v < Q3 n ℓ₁ f₁ m q ℓ f → toN Z v = toN Y2 v) ∧
    (∀ i : Fin n, QuantumLTF.Membership.readFp (oaT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp i)
        (foT q ℓo₃ fo₃ Pp) Z =
      if toN Y2 (eqv n ℓ₁ f₁ m q ℓ f) then 0 else
        -(sgnS (toN Y2 (sbv n ℓ₁ f₁ m q ℓ f))) * gW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i y') ∧
    QuantumLTF.Membership.readFp (obT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp)
        (foT q ℓo₃ fo₃ Pp) Z =
      if toN Y2 (eqv n ℓ₁ f₁ m q ℓ f) then (if toN Y2 (cv n ℓ₁ f₁ m q ℓ f) then 1 else 0) else
        sgnS (toN Y2 (sbv n ℓ₁ f₁ m q ℓ f)) * QuantumLTF.Membership.fpVal (Bh m q) (q + 1)
          (fun t => toN Y2 (sbv n ℓ₁ f₁ m q ℓ f + 1 + t.val)) := by
  have hBo : Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp ≤ MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp :=
    Nat.le_add_right _ _
  have hBw : Bw n ℓ₁ f₁ m q ℓ f m₃ + (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2.length =
    Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp := rfl
  have hQB : Q3 n ℓ₁ f₁ m q ℓ f + m₃ = Bw n ℓ₁ f₁ m q ℓ f m₃ := rfl
  have hoQ := offM_le_Q3 n ℓ₁ f₁ m q ℓ f
  obtain ⟨Z0, hZ0d⟩ : ∃ Z0, Z0 = setPart Y2 (ιE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) y' := ⟨_, rfl⟩
  rw [← hZ0d] at hZ
  have hZ0a : ∀ v, v < Q3 n ℓ₁ f₁ m q ℓ f → toN Z0 v = toN Y2 v := by
    intro v hv; rw [hZ0d]
    exact toN_setPart_off _ _ _ _ (fun a ha => by rw [ιE_val] at ha; omega)
  have hZ0b : ∀ v, Bw n ℓ₁ f₁ m q ℓ f m₃ ≤ v → toN Z0 v = false := by
    intro v hv; rw [hZ0d, toN_setPart_off _ _ _ _ (fun a ha => by
      rw [ιE_val] at ha; have := a.isLt; omega)]
    exact hY2 _ (by omega)
  have hZ0c : ∀ j : Fin m₃, toN Z0 (Q3 n ℓ₁ f₁ m q ℓ f + j.val) = y' j := by
    intro j; rw [hZ0d]; exact toN_setPart_emb _ _ _ j _ (ιE_val _ _ _ _ _ _ _ _ _ _ _ _ j)
  set O := Owt n ℓ f w θ with hO
  obtain ⟨Z1, hZ1d⟩ : ∃ Z1, Z1 = runPO (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) O
      (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2 (Bw n ℓ₁ f₁ m q ℓ f m₃) Z0 := ⟨_, rfl⟩
  have hZ1 : ∀ v (hv : v < MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp), toN Z1 v =
      svalO O (Bw n ℓ₁ f₁ m q ℓ f m₃) (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2 (toN Z0) v := by
    intro v hv
    have h1 := toN_fin Z1 ⟨v, hv⟩
    simp only [Fin.val_mk] at h1
    rw [h1, hZ1d, compile_semO _ _ _ _ (by omega) Z0 (fun v hv => by
      rw [← toN_fin Z0 v]; exact hZ0b _ hv)]
  obtain ⟨Z2, hZ2d⟩ : ∃ Z2, Z2 = runPO (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) O
      (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) Z1 := ⟨_, rfl⟩
  have hZZ : Z = Z2 := by rw [hZ, hZ2d, hZ1d, Fpost, Function.comp_apply]
  have hZ2 : ∀ v (hv : v < MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp), toN Z2 v =
      svalO O (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
        (toN Z1) v := by
    intro v hv
    have h1 := toN_fin Z2 ⟨v, hv⟩
    simp only [Fin.val_mk] at h1
    rw [h1, hZ2d, compile_semO _ _ _ _ (le_refl _) Z1 (fun v hv => by
      rw [← toN_fin Z1 v, hZ1 _ v.isLt]; exact svalO_beyond _ _ _ _ _ (by omega))]
  have hσ1lo : ∀ v, v < Bw n ℓ₁ f₁ m q ℓ f m₃ →
      svalO O (Bw n ℓ₁ f₁ m q ℓ f m₃) (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2 (toN Z0) v =
        toN Z0 v := fun v hv => svalO_lt _ _ _ _ hv
  have hσσ1 : ∀ v, v < Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp →
      svalO O (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
        (toN Z1) v =
      svalO O (Bw n ℓ₁ f₁ m q ℓ f m₃) (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2 (toN Z0) v := by
    intro v hv; rw [svalO_lt _ _ _ _ hv, hZ1 _ (by omega)]
  have hσY : ∀ v, v < Q3 n ℓ₁ f₁ m q ℓ f →
      svalO O (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
        (toN Z1) v = toN Y2 v := by
    intro v hv; rw [hσσ1 _ (by omega), hσ1lo _ (by omega), hZ0a _ hv]
  obtain ⟨-, -, hP⟩ := Pout_spec n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp O
  have hP' := hP [] (toN Z1)
  simp only [List.append_nil] at hP'
  obtain ⟨-, -, hWl, hW⟩ := winR_spec n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp O
  have hW' := hW [] (toN Z0)
  simp only [List.append_nil] at hW'
  have hσ1Bw : svalO O (Bw n ℓ₁ f₁ m q ℓ f m₃) (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2 (toN Z0)
      (Bw n ℓ₁ f₁ m q ℓ f m₃) = false := by
    obtain ⟨r, hr⟩ := winR_ext n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp
    rw [hr]; exact (p0g_holds O (Bw n ℓ₁ f₁ m q ℓ f m₃) r (toN Z0)).1
  have hE : ∀ i : Fin n, (fun k => svalO O (Bw n ℓ₁ f₁ m q ℓ f m₃)
      (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2 (toN Z0)
      (((srcs n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃).getD i.val (fun _ => 0)) k)) =
      eW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃ i y' := by
    intro i; funext k
    rw [srcs_getD]
    simp only [eW]
    split_ifs with h
    · rw [hσ1lo _ (by have := (oa₃ i ⟨ℓo₃ - 1 - k, by omega⟩).isLt; omega), hZ0c]
    · exact hσ1Bw
  have hQpos : 0 < Q3 n ℓ₁ f₁ m q ℓ f := by simp only [Q3, offM]; omega
  have hKw : Kw ℓo₃ fo₃ Pp = fw ℓo₃ fo₃ Pp + 6 := rfl
  have hG : ∀ i : Fin n, QuantumLTF.Membership.fpVal (Kw ℓo₃ fo₃ Pp) (fw ℓo₃ fo₃ Pp)
      (msbBits (svalO O (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
        (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (toN Z1)) (Kw ℓo₃ fo₃ Pp)
        ((winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1.getD i.val [])) =
      gW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i y' := by
    intro i
    have hil : i.val < (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1.length := by
      obtain ⟨-, hl, -⟩ := winR_spec n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp O
      rw [hl]; exact i.isLt
    have hmem := List.getElem_mem hil
    rw [← List.getD_eq_getElem _ [] hil] at hmem
    obtain ⟨hXl, hXv⟩ := hWl _ hmem
    have hms : msbBits (svalO O (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
        (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (toN Z1)) (Kw ℓo₃ fo₃ Pp)
        ((winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1.getD i.val []) =
        msbBits (svalO O (Bw n ℓ₁ f₁ m q ℓ f m₃) (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2 (toN Z0))
          (Kw ℓo₃ fo₃ Pp) ((winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1.getD i.val []) := by
      funext t
      simp only [msbBits]
      apply hσσ1
      rw [List.getD_eq_getElem?_getD]
      cases h : ((winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).1.getD i.val [])[Kw ℓo₃ fo₃ Pp - 1 - t.val]? with
      | none => simp only [Option.getD_none]; omega
      | some x => simp only [Option.getD_some]; exact hXv x (List.mem_of_getElem? h)
    rw [hms, fpVal_msbBits _ _ _ _ hXl, PX, hW' i.val i.isLt, hE i, gW]
    have hK : (2 : ℝ) ^ (Kw ℓo₃ fo₃ Pp) = 2 * 2 ^ (Kw ℓo₃ fo₃ Pp - 1) := by
      rw [hKw, show fw ℓo₃ fo₃ Pp + 6 - 1 = fw ℓo₃ fo₃ Pp + 5 by omega]; ring
    push_cast
    rw [hK, pow_succ]
    field_simp
  have hQM := Q3_le_MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp
  have hsQ : sbv n ℓ₁ f₁ m q ℓ f + 1 + Bh m q ≤ Q3 n ℓ₁ f₁ m q ℓ f := by
    simp only [sbv, Q3, offM] at hoQ ⊢; omega
  refine ⟨?_, ?_, ?_⟩
  · intro v hv; rw [hZZ, hZ2 _ (by omega), hσY _ hv]
  · intro i
    have hc : Z ∘ oaT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp i = fun t =>
        svalO O (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
          (toN Z1) (Bc n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp + i.val * ℓoT m q ℓo₃ fo₃ Pp + t.val) := by
      funext t
      have hlt := (oaT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp i t).isLt
      rw [oaT_val] at hlt
      rw [Function.comp_apply, ← toN_fin Z, oaT_val, hZZ, hZ2 _ hlt]
    show QuantumLTF.Membership.fpVal _ _ (Z ∘ _) = _
    rw [hc, hP'.1 i.val i.isLt, hσY _ (by simp only [eqv, Q3]; omega),
      hσY _ (by simp only [sbv, Q3, offM] at hoQ ⊢; omega), hG i]
  · have hc : Z ∘ obT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp = fun t =>
        svalO O (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
          (toN Z1) (Bc n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp + n * ℓoT m q ℓo₃ fo₃ Pp + t.val) := by
      funext t
      have hlt := (obT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp t).isLt
      rw [obT_val] at hlt
      rw [Function.comp_apply, ← toN_fin Z, obT_val, hZZ, hZ2 _ hlt]
    have hms : msbBits (svalO O (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
        (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (toN Z1)) (Bh m q) (hLw n ℓ₁ f₁ m q ℓ f) =
        fun t => toN Y2 (sbv n ℓ₁ f₁ m q ℓ f + 1 + t.val) := by
      funext t
      have ht := t.isLt
      simp only [msbBits, hLw]
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega)]
      simp only [List.getElem_map, List.getElem_range]
      rw [hσY _ (by have := hsQ; simp only [sbv] at this; omega)]
      congr 1
      simp only [sbv]
      omega
    show QuantumLTF.Membership.fpVal _ _ (Z ∘ _) = _
    rw [hc, hP'.2, hσY _ (by simp only [eqv, Q3]; omega), hσY _ (by simp only [cv, Q3]; omega),
      hσY _ (by simp only [sbv, Q3, offM] at hoQ ⊢; omega), hms]

theorem readFp_sumBits (i : Fin n) (y' : Qubits m₃) :
    QuantumLTF.Membership.readFp (oa₃ i) fo₃ y' =
      ((sumBits (eW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃ i y') (Lw ℓo₃) - 2 ^ (Lw ℓo₃ - 1) : ℤ) : ℝ) /
        2 ^ Fw ℓo₃ fo₃ := by
  have hb := bitsToNat_sumBits (y' ∘ oa₃ i)
  have he : (fun k => if h : k < ℓo₃ then (y' ∘ oa₃ i) ⟨ℓo₃ - 1 - k, by omega⟩ else false) =
      eW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃ i y' := rfl
  rw [he] at hb
  unfold QuantumLTF.Membership.readFp QuantumLTF.Membership.fpVal
  by_cases h0 : ℓo₃ = 0
  · subst h0
    have hz : bitsToNat (y' ∘ oa₃ i) = 0 := by simp [bitsToNat]
    have he0 : eW n ℓ₁ f₁ m q ℓ f m₃ 0 oa₃ i y' 0 = false := by simp [eW]
    simp only [Lw, Fw, if_true]
    rw [hz]
    simp only [sumBits, Finset.sum_range_one, he0]
    push_cast
    rw [pow_succ]
    field_simp
    norm_num
  · simp only [Lw, Fw, if_neg h0]
    have hcast : ((bitsToNat (y' ∘ oa₃ i) : ℕ) : ℝ) =
        ((sumBits (eW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃ i y') ℓo₃ : ℤ) : ℝ) := by
      rw [← hb]; rfl
    rw [hcast]
    have hp : (2 : ℝ) ^ ℓo₃ / 2 = 2 ^ (ℓo₃ - 1) := by
      rw [show ℓo₃ = (ℓo₃ - 1) + 1 by omega, pow_succ]; simp
    rw [hp]
    push_cast
    rfl

theorem trunc_err (i : Fin n) (y' : Qubits m₃)
    (hb : |QuantumLTF.Membership.readFp (oa₃ i) fo₃ y'| < 16) :
    |gW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i y' - QuantumLTF.Membership.readFp (oa₃ i) fo₃ y'| ≤
      (1 / 2) ^ Pp := by
  rw [readFp_sumBits] at hb ⊢
  set e := eW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ oa₃ i y' with he
  set X : ℤ := sumBits e (Lw ℓo₃) - 2 ^ (Lw ℓo₃ - 1) with hXd
  have hfw : fw ℓo₃ fo₃ Pp ≤ Fw ℓo₃ fo₃ := min_le_left _ _
  have hlo : loW ℓo₃ fo₃ Pp + fw ℓo₃ fo₃ Pp = Fw ℓo₃ fo₃ := by simp only [loW]; omega
  have hpF : (0 : ℝ) < 2 ^ Fw ℓo₃ fo₃ := by positivity
  have hXr : |(X : ℝ)| < 2 ^ (Fw ℓo₃ fo₃ + 4) := by
    rw [abs_div, abs_of_pos hpF, div_lt_iff₀ hpF] at hb
    have h16 : (2 : ℝ) ^ (Fw ℓo₃ fo₃ + 4) = 16 * 2 ^ Fw ℓo₃ fo₃ := by rw [pow_add]; ring
    rw [h16]; exact hb
  have hX : |X| < 2 ^ (loW ℓo₃ fo₃ Pp + Kw ℓo₃ fo₃ Pp - 1) := by
    have h2 : (2 : ℝ) ^ (Fw ℓo₃ fo₃ + 4) ≤ 2 ^ (loW ℓo₃ fo₃ Pp + Kw ℓo₃ fo₃ Pp - 1) :=
      pow_le_pow_right₀ (by norm_num) (by simp only [Kw]; omega)
    have : |(X : ℝ)| < ((2 ^ (loW ℓo₃ fo₃ Pp + Kw ℓo₃ fo₃ Pp - 1) : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  obtain ⟨Xl, h0, h1, heq⟩ := window_lemma e (Lw ℓo₃) (loW ℓo₃ fo₃ Pp) (Kw ℓo₃ fo₃ Pp)
    (by simp only [Lw]; split_ifs <;> omega) (by simp only [Kw]; omega) hX
  rw [← hXd] at heq
  unfold gW
  rw [← he, heq]
  set S : ℤ := sumBits (fun j => xor (sext e (Lw ℓo₃) (loW ℓo₃ fo₃ Pp + j))
    (decide (j = Kw ℓo₃ fo₃ Pp - 1))) (Kw ℓo₃ fo₃ Pp) - 2 ^ (Kw ℓo₃ fo₃ Pp - 1) with hS
  have hF : (2 : ℝ) ^ Fw ℓo₃ fo₃ = 2 ^ loW ℓo₃ fo₃ Pp * 2 ^ fw ℓo₃ fo₃ Pp := by
    rw [← pow_add, hlo]
  have hdiff : (S : ℝ) / 2 ^ fw ℓo₃ fo₃ Pp - ((Xl + 2 ^ loW ℓo₃ fo₃ Pp * S : ℤ) : ℝ) /
      2 ^ Fw ℓo₃ fo₃ = -((Xl : ℝ) / 2 ^ Fw ℓo₃ fo₃) := by
    rw [hF]; push_cast; field_simp; ring
  rw [hdiff, abs_neg, abs_of_nonneg (by positivity)]
  by_cases hl0 : loW ℓo₃ fo₃ Pp = 0
  · rw [hl0, pow_zero] at h1
    have : Xl = 0 := by omega
    rw [this]; simp
  · have hfP : fw ℓo₃ fo₃ Pp = Pp := by
      simp only [loW, fw] at hl0 ⊢; omega
    have h1r : (Xl : ℝ) < 2 ^ loW ℓo₃ fo₃ Pp := by exact_mod_cast h1
    rw [div_le_iff₀ hpF, hF, hfP]
    have : (1 / 2 : ℝ) ^ Pp * (2 ^ loW ℓo₃ fo₃ Pp * 2 ^ Pp) = 2 ^ loW ℓo₃ fo₃ Pp := by
      rw [one_div, inv_pow]; field_simp
    rw [this]; exact h1r.le

end StageC

end LTFC

-- ===== module Assembly3 =====

open QAlgorithms

namespace LTFC

theorem invol_unitary {k : ℕ} (τ : Qubits k → Qubits k) (hτ : Function.Involutive τ)
    (M : Matrix (Qubits k) (Qubits k) ℂ) (hM : ∀ y x, M y x = if y = τ x then 1 else 0) :
    M ∈ Matrix.unitaryGroup (Qubits k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext y z
  simp only [Matrix.mul_apply, Matrix.star_apply, hM, Matrix.one_apply]
  have h1 : ∀ x, (y = τ x) ↔ (x = τ y) := fun x => ⟨fun h => by rw [h, hτ], fun h => by rw [h, hτ]⟩
  have h2 : ∀ x, (z = τ x) ↔ (x = τ z) := fun x => ⟨fun h => by rw [h, hτ], fun h => by rw [h, hτ]⟩
  simp only [h1, h2]
  simp only [apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (τ z)]
  simp only [Finset.mem_univ, if_true]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg (fun h => hyz (hτ.injective h).symm), if_neg hyz]

theorem classical_unitary {K : ℕ} (O : (Fin K → Bool) → Bool)
    (Mo : Matrix (Qubits (K + 1)) (Qubits (K + 1)) ℂ) (h : IsClassicalOracle O Mo) :
    Mo ∈ Matrix.unitaryGroup (Qubits (K + 1)) ℂ := by
  apply invol_unitary (fun x => Fin.snoc (α := fun _ => Bool) (Fin.init x)
    (xor (x (Fin.last _)) (O (Fin.init x)))) _ Mo h
  intro x
  simp only [Fin.init_snoc, Fin.snoc_last, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  exact Fin.snoc_init_self x

theorem memOracle_unitary (n ℓ f : ℕ) (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    QuantumLTF.Membership.memOracle n ℓ f w θ ∈ Matrix.unitaryGroup (Qubits (n * ℓ + 1)) ℂ :=
  classical_unitary _ _ (memOracle_classical n ℓ f w θ)

theorem euclid_norm_le {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ i, |v i| ≤ δ) : ‖v‖ ≤ Real.sqrt n * δ := by
  rw [EuclideanSpace.norm_eq]
  rw [show Real.sqrt n * δ = Real.sqrt (n * δ ^ 2) by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hδ]]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin n, δ ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = n * δ ^ 2 := by simp

theorem ltf_smul {n : ℕ} (w p : EuclideanSpace ℝ (Fin n)) (θ L : ℝ) :
    QuantumLTF.Membership.ltf w θ (L • p) = QuantumLTF.Membership.sgn (L * inner ℝ w p - θ) := by
  unfold QuantumLTF.Membership.ltf; rw [real_inner_smul_right]

theorem eq_branch {n : ℕ} (w p : EuclideanSpace ℝ (Fin n)) (θ L : ℝ)
    (h : (decide (QuantumLTF.Membership.ltf w θ (L • p) = -1) ==
      decide (QuantumLTF.Membership.ltf w θ ((-L) • p) = -1)) = true) :
    |L * inner ℝ w p| ≤ |θ| ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      QuantumLTF.Membership.ltf (0 : EuclideanSpace ℝ (Fin n))
        (if decide (QuantumLTF.Membership.ltf w θ (L • p) = -1) then 1 else 0) x =
      QuantumLTF.Membership.ltf w θ 0 := by
  rw [ltf_smul, ltf_smul] at h
  rw [ltf_smul]
  set A := L * inner ℝ w p
  have hA : -L * inner ℝ w p = -A := by ring
  rw [hA] at h
  unfold QuantumLTF.Membership.ltf
  simp only [inner_zero_left, zero_sub]
  unfold QuantumLTF.Membership.sgn at h ⊢
  by_cases h1 : 0 ≤ A - θ <;> by_cases h2 : 0 ≤ -A - θ <;> simp [h1, h2] at h ⊢
  · constructor
    · rw [abs_le]; constructor <;> cases abs_cases A <;> cases abs_cases θ <;> linarith
    · cases abs_cases A <;> linarith
  · constructor
    · cases abs_cases A <;> cases abs_cases θ <;> linarith
    · rw [if_neg (by norm_num), if_neg (by linarith)]

theorem differ_branch {n : ℕ} (w p : EuclideanSpace ℝ (Fin n)) (θ L : ℝ)
    (h : (decide (QuantumLTF.Membership.ltf w θ (L • p) = -1) ==
      decide (QuantumLTF.Membership.ltf w θ ((-L) • p) = -1)) = false) :
    |θ| ≤ |L * inner ℝ w p| := by
  rw [ltf_smul, ltf_smul] at h
  set A := L * inner ℝ w p
  have hA : -L * inner ℝ w p = -A := by ring
  rw [hA] at h
  unfold QuantumLTF.Membership.sgn at h
  by_cases h1 : 0 ≤ A - θ <;> by_cases h2 : 0 ≤ -A - θ <;> simp [h1, h2] at h <;>
    cases abs_cases A <;> cases abs_cases θ <;> linarith

theorem cert_nonconst {n : ℕ} (ε δ : ℝ) (w p : EuclideanSpace ℝ (Fin n)) (θ ht : ℝ)
    (gt : Fin n → ℝ) (hw : ‖w‖ = 1)
    (ha1 : 1 / 10 ≤ |inner ℝ w p|) (ha2 : |inner ℝ w p| ≤ 3)
    (hL1 : 1 ≤ QuantumLTF.Membership.Leps ε)
    (hh : |θ / inner ℝ w p| ≤ QuantumLTF.Membership.Leps ε)
    (hht : |ht - θ / inner ℝ w p| ≤ ε / 100) (hδ : 0 ≤ δ)
    (hg : ∀ i, |gt i - (-(w i) / inner ℝ w p)| ≤ δ)
    (hδn : Real.sqrt n * δ ≤ ε / (100 * (QuantumLTF.Membership.Leps ε + 1))) :
    QuantumLTF.Membership.LearningCertificate ε w θ
      (WithLp.toLp 2 (fun i => -((QuantumLTF.Membership.sgn (inner ℝ w p) : ℤ) : ℝ) * gt i))
      (((QuantumLTF.Membership.sgn (inner ℝ w p) : ℤ) : ℝ) * ht) := by
  set a := inner ℝ w p with had
  set s := QuantumLTF.Membership.sgn a with hsd
  have ha0 : a ≠ 0 := by intro h; rw [h, abs_zero] at ha1; norm_num at ha1
  have hsa : (s : ℝ) * |a| = a := by
    rw [hsd]; unfold QuantumLTF.Membership.sgn
    split_ifs with h
    · rw [abs_of_nonneg h]; simp
    · rw [abs_of_neg (by linarith)]; simp
  have hs2 : (s : ℝ) * s = 1 := by
    rw [hsd]; unfold QuantumLTF.Membership.sgn; split_ifs <;> norm_num
  have hapos : 0 < |a| := abs_pos.2 ha0
  set g : EuclideanSpace ℝ (Fin n) := (-(1 / a)) • w with hg_def
  have hgn : ‖g‖ = 1 / |a| := by
    rw [hg_def, norm_smul, hw, mul_one, norm_neg, Real.norm_eq_abs, abs_div, abs_one]
  have hgi : ∀ i, g i = -(w i) / a := by
    intro i; rw [hg_def]; simp; ring
  refine Or.inr ⟨s, θ / a, ht, g, WithLp.toLp 2 gt, ?_, hL1, ?_, ?_, ?_, ?_, hht, hh, ?_, ?_, rfl⟩
  · rw [hsd]; unfold QuantumLTF.Membership.sgn; split_ifs <;> simp
  · rw [hgn, le_div_iff₀ hapos]; linarith
  · rw [hgn, div_le_iff₀ hapos]; linarith
  · rw [hgn, hg_def, smul_smul, smul_smul]
    have : -(s : ℝ) * (1 / |a|)⁻¹ * -(1 / a) = 1 := by
      rw [show -(s : ℝ) * (1 / |a|)⁻¹ * -(1 / a) = ((s : ℝ) * |a|) * a⁻¹ by field_simp, hsa,
        mul_inv_cancel₀ ha0]
    rw [this, one_smul]
  · rw [hgn]
    field_simp
    rw [mul_assoc, hsa]
  · calc ‖WithLp.toLp 2 gt - g‖ ≤ Real.sqrt n * δ := by
          apply euclid_norm_le _ δ hδ
          intro i
          have := hg i
          simp only [PiLp.sub_apply, hgi]
          exact this
      _ ≤ _ := hδn
  · ext i; simp

theorem mulVec_bv_apply {k : ℕ} (U : Matrix (Qubits k) (Qubits k) ℂ) (y z : Qubits k) :
    (U.mulVec (bv z)) y = U y z := by
  simp [bv, Matrix.mulVec_single_one]

section Core

variable (n ℓ₁ f₁ m q ℓ f : ℕ) (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)
  (m₃ ℓo₃ fo₃ : ℕ) (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)) (Pp : ℕ) (b Vb W : ℕ)
  (cA : OracleCircuit QuantumLTF.Membership.gatesRev (fun _ : Fin 1 => n * ℓ + 1)
    (n * ℓ₁ + 1 + Bh m q + (n * b + Vb + W)))
  (c₃ : OracleCircuit G12 (fun _ : Fin 1 => n * b + Vb + W) m₃)

theorem comp_πE (Y : Qubits (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)) :
    Y ∘ πE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp =
      Fin.append (Fin.append (fun i : Fin (n * ℓ₁) => toN Y i.val)
        (fun _ : Fin 1 => toN Y (sbv n ℓ₁ f₁ m q ℓ f)))
        (fun t : Fin (Bh m q) => toN Y (sbv n ℓ₁ f₁ m q ℓ f + 1 + t.val)) := by
  funext j
  rw [Function.comp_apply, ← toN_fin Y, πE_val]
  induction j using Fin.addCases with
  | left k =>
    rw [Fin.append_left]
    induction k using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      simp only [Fin.coe_castAdd, i.isLt, if_true]
    | right o =>
      rw [Fin.append_right]
      have : o.val = 0 := by omega
      simp only [Fin.coe_castAdd, Fin.val_natAdd, this, sbv]
      rw [if_neg (by omega)]
      congr 1
      omega
  | right t =>
    rw [Fin.append_right]
    simp only [Fin.val_natAdd, sbv]
    rw [if_neg (by omega)]
    congr 1
    omega

noncomputable def Vmat (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    Matrix (Qubits (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)) (Qubits (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)) ℂ :=
  (cOut n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).unitary
      (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) *
    ((cWin n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).unitary
      (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) *
    ((cSub n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃).unitary
      (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) *
    ((relabel (testCirc n ℓ₁ f₁ m q ℓ f hf hℓ)
        (testE n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp)).unitary
        (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) *
      (relabel (offCirc n ℓ₁ f₁ m q ℓ f hf hℓ) (offE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)).unitary
        (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ))))

/-- The success event. -/
def Ecert (ε : ℝ) (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
    (z : Qubits (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)) : Prop :=
  QuantumLTF.Membership.LearningCertificate ε w θ
    (WithLp.toLp 2 fun i => QuantumLTF.Membership.readFp
      (oaT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp i) (foT q ℓo₃ fo₃ Pp) z)
    (QuantumLTF.Membership.readFp (obT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp)
      (foT q ℓo₃ fo₃ Pp) z)

open Classical in
theorem perU (hAu : QuantumLTF.Membership.Uncontrolled cA)
    (h3u : QuantumLTF.Membership.Uncontrolled c₃) (ε εg η : ℝ) (Vf : ℕ)
    (hm : QuantumLTF.Membership.Leps ε = 2 ^ m)
    (hq : 2 * QuantumLTF.Membership.Leps ε / 2 ^ (q + 1) ≤ ε / 100)
    (hL1 : 1 ≤ QuantumLTF.Membership.Leps ε)
    (hLT : 20 * QuantumLTF.Membership.Teps ε ≤ QuantumLTF.Membership.Leps ε)
    (hεg0 : 0 ≤ εg) (hεg1 : εg ≤ 1) (hPp : (1 / 2 : ℝ) ^ Pp ≤ εg)
    (hεgn : Real.sqrt n * (2 * εg) ≤ ε / (100 * (QuantumLTF.Membership.Leps ε + 1)))
    (hBD : ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ),
      BlockDiag (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ))
    (hAact : ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (zp : Qubits (n * ℓ₁)) (sb : Bool)
        (hb : Qubits (Bh m q)), ‖w‖ = 1 →
        1 / 10 ≤ |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)| →
        |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)| ≤ 3 →
        (if sb then (1 : ℤ) else -1) =
          QuantumLTF.Membership.sgn (inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)) →
        |QuantumLTF.Membership.fpVal (Bh m q) (q + 1) hb -
          QuantumLTF.Membership.height w θ (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp) 0| ≤ ε / 100 →
        ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
          (∀ x, act (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
              (ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                (QuantumLTF.Membership.regBasis n b Vb W x fun _ => false))) =
            ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                (QuantumLTF.Membership.regBasis n b Vb W x (Htil x)))) ∧
          ∀ x, |QuantumLTF.Membership.fpVal Vb Vf (Htil x) -
            QuantumLTF.Membership.height w θ (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)
              (QuantumLTF.Membership.rho n • QuantumLTF.Membership.gridVec n b x)| ≤ η)
    (h3 : ∀ (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
        1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 →
        ∀ Htil : (Fin n → Qubits b) → Qubits Vb,
          (∀ x, |QuantumLTF.Membership.fpVal Vb Vf (Htil x) -
            QuantumLTF.Membership.height w θ p (QuantumLTF.Membership.rho n •
              QuantumLTF.Membership.gridVec n b x)| ≤ η) →
        ∀ OH : Matrix (Qubits (n * b + Vb + W)) (Qubits (n * b + Vb + W)) ℂ,
          OH ∈ Matrix.unitaryGroup (Qubits (n * b + Vb + W)) ℂ →
          (∀ x, act OH (ket (QuantumLTF.Membership.regBasis n b Vb W x fun _ => false)) =
            ket (QuantumLTF.Membership.regBasis n b Vb W x (Htil x))) →
          probEvent (act (c₃.unitary fun _ => OH) (zeroKet m₃))
            (fun z => ∀ i, |QuantumLTF.Membership.readFp (oa₃ i) fo₃ z - (-(w i) / inner ℝ w p)| ≤ εg)
            ≥ 5 / 6)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) (θ : ℝ) (u : Qubits (n * ℓ₁)) :
    (∀ y, ((Vmat n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃ w θ).mulVec
        (bv (setPart (fun _ => false) (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) u))) y ≠ 0 →
        y ∘ pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp = u) ∧
    (1 / 10 ≤ |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ u)| →
      |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ u)| ≤ 3 →
      5 / 6 ≤ ∑ y ∈ Finset.univ.filter (Ecert n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp ε w θ),
        ‖((Vmat n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃ w θ).mulVec
          (bv (setPart (fun _ => false) (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) u))) y‖ ^ 2) := by
  obtain ⟨Y2, hY2V, hY2u, hY2z, hsb, hhb, hcv, heq⟩ :=
    stageA n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp w θ u
  have hB := stageB n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃ hAu h3u w θ (hBD w θ) Y2 hY2z
  obtain ⟨G, hGd⟩ : ∃ G : Qubits m₃ → Qubits (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp),
      G = fun y' => Fpost n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp (Owt n ℓ f w θ)
        (setPart Y2 (ιE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) y') := ⟨_, rfl⟩
  have hGi : Function.Injective G := by
    intro x y h
    rw [hGd] at h
    have h1 := Fpost_inj n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp _ h
    have h2 := congrArg (fun Z => Z ∘ ιE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) h1
    simpa only [setPart_comp] using h2
  obtain ⟨OH, hOHd⟩ : ∃ OH, OH = blockOf (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
      (Y2 ∘ πE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) := ⟨_, rfl⟩
  have hV : (Vmat n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃ w θ).mulVec
      (bv (setPart (fun _ => false) (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) u)) =
      ∑ y', (c₃.unitary fun _ => OH) y' (fun _ => false) • bv (G y') := by
    unfold Vmat
    rw [← mul_assoc, ← mul_assoc, ← Matrix.mulVec_mulVec, hY2V, mul_assoc, hB, hGd, hOHd]
  have hC := fun y' => stageC n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp w θ Y2 hY2z y' (G y')
    (by rw [hGd])
  have hnl := nl_le_offM n ℓ₁ f₁ m q ℓ f
  have hoQ := offM_le_Q3 n ℓ₁ f₁ m q ℓ f
  refine ⟨?_, ?_⟩
  · intro y hy
    rw [hV] at hy
    obtain ⟨y', hy'⟩ : ∃ y', y = G y' := by
      by_contra hne
      push_neg at hne
      apply hy
      simp only [Finset.sum_apply, Pi.smul_apply, bv, Pi.single_apply, smul_eq_mul]
      apply Finset.sum_eq_zero
      intro y' _
      rw [if_neg (hne y')]
      simp
    funext i
    rw [hy', Function.comp_apply, ← toN_fin (G y'), pinG_val, (hC y').1 _ (by have := i.isLt; omega),
      hY2u]
  · intro ha1 ha2
    set p := QuantumLTF.Membership.addrOf n ℓ₁ f₁ u with hpd
    set A := inner ℝ w p with hAd
    have hA0 : A ≠ 0 := by intro h; rw [h, abs_zero] at ha1; norm_num at ha1
    have hApos : 0 < |A| := abs_pos.2 hA0
    have hUA : (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) ∈
        Matrix.unitaryGroup _ ℂ := by
      rw [← convC_unitary]
      exact circuit_unitary (convC cA) (convC_counts cA hAu 0).1 _
        (fun _ => memOracle_unitary n ℓ f w θ)
    have hOHu : OH ∈ Matrix.unitaryGroup _ ℂ := by rw [hOHd]; exact blockOf_unitary (hBD w θ) hUA _
    have hc3u := circuit_unitary c₃ h3u (fun _ => OH) (fun _ => hOHu)
    rw [hV, prob_inj G hGi]
    beta_reduce
    have hL2 : (2 : ℝ) ^ m = QuantumLTF.Membership.Leps ε := hm.symm
    have hT0 : 0 ≤ QuantumLTF.Membership.Teps ε := Real.sqrt_nonneg _
    by_cases he : toN Y2 (eqv n ℓ₁ f₁ m q ℓ f) = true
    · -- both test answers agree: constant certificate, with certainty
      have hce : (decide (QuantumLTF.Membership.ltf w θ (((2 : ℝ) ^ m) • p) = -1) ==
          decide (QuantumLTF.Membership.ltf w θ ((-((2 : ℝ) ^ m)) • p) = -1)) = true := by
        rw [← hcv, ← heq]; exact he
      obtain ⟨hθ, hltf⟩ := eq_branch w p θ _ hce
      have hall : ∀ y', Ecert n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp ε w θ (G y') := by
        intro y'
        obtain ⟨-, h2, h3'⟩ := hC y'
        unfold Ecert
        have hvec : (WithLp.toLp 2 fun i => QuantumLTF.Membership.readFp
            (oaT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp i) (foT q ℓo₃ fo₃ Pp) (G y')) =
            (0 : EuclideanSpace ℝ (Fin n)) := by
          ext i; simp only [h2 i, he, if_true]; rfl
        rw [hvec, h3', if_pos he, hcv]
        refine Or.inl ⟨fun x => ?_, ?_⟩
        · exact hltf x
        · have hpos : (0 : ℝ) < 2 ^ m := by positivity
          have h1 : |(2 : ℝ) ^ m * A| = QuantumLTF.Membership.Leps ε * |A| := by
            rw [abs_mul, abs_of_pos hpos, hL2]
          have h2 : QuantumLTF.Membership.Leps ε * (1 / 10) ≤ QuantumLTF.Membership.Leps ε * |A| :=
            mul_le_mul_of_nonneg_left ha1 (le_trans zero_le_one hL1)
          linarith only [h1, h2, hθ, hLT, hT0]
      have hcs := colsum_one hc3u (fun _ => false)
      have hfu : Finset.univ.filter (fun y' => Ecert n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp ε w θ (G y')) =
          Finset.univ := Finset.filter_true_of_mem (fun y' _ => hall y')
      rw [hfu, hcs]
      norm_num
    · -- the answers differ: |h_p(0)| ≤ L, all estimates are valid
      have he' : toN Y2 (eqv n ℓ₁ f₁ m q ℓ f) = false := by simpa using he
      have hce : (decide (QuantumLTF.Membership.ltf w θ (((2 : ℝ) ^ m) • p) = -1) ==
          decide (QuantumLTF.Membership.ltf w θ ((-((2 : ℝ) ^ m)) • p) = -1)) = false := by
        rw [← hcv, ← heq]; exact he'
      have hθ := differ_branch w p θ _ hce
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m), hL2] at hθ
      have hheight : QuantumLTF.Membership.height w θ p 0 = θ / A := by
        unfold QuantumLTF.Membership.height; rw [inner_zero_right, sub_zero]
      have hh : |θ / A| ≤ QuantumLTF.Membership.Leps ε := by
        rw [abs_div, div_le_iff₀ hApos]; exact hθ
      have hrun := QuantumLTF.Membership.boundarySearchTreeStrict_run w p θ ((2 : ℝ) ^ m) q hA0
        (by rw [hheight, hL2]; exact hh)
      rw [hrun] at hsb hhb
      have hsgn : (if toN Y2 (sbv n ℓ₁ f₁ m q ℓ f) then (1 : ℤ) else -1) =
          QuantumLTF.Membership.sgn A := by
        rw [hsb]
        rcases (show QuantumLTF.Membership.sgn A = 1 ∨ QuantumLTF.Membership.sgn A = -1 by
          unfold QuantumLTF.Membership.sgn; split_ifs <;> simp) with h | h <;> rw [h] <;> simp
      have hsgnR : sgnS (toN Y2 (sbv n ℓ₁ f₁ m q ℓ f)) = ((QuantumLTF.Membership.sgn A : ℤ) : ℝ) := by
        rw [← hsgn]; unfold sgnS; split_ifs <;> simp
      have hhb' : |QuantumLTF.Membership.fpVal (Bh m q) (q + 1)
          (fun t => toN Y2 (sbv n ℓ₁ f₁ m q ℓ f + 1 + t.val)) -
          QuantumLTF.Membership.height w θ p 0| ≤ ε / 100 := by
        rw [hhb, hheight]
        have hlo : -(2 : ℝ) ^ m ≤ θ / A := by rw [hL2]; exact (abs_le.1 hh).1
        have hhi : θ / A ≤ (2 : ℝ) ^ m := by rw [hL2]; exact (abs_le.1 hh).2
        have := QuantumLTF.Membership.orientedBisectValue_error (QuantumLTF.Membership.sgn A) q
          (-(2 : ℝ) ^ m) ((2 : ℝ) ^ m) (θ / A) hlo hhi
        calc _ ≤ ((2 : ℝ) ^ m - -(2 : ℝ) ^ m) / 2 ^ (q + 1) := this
          _ = 2 * QuantumLTF.Membership.Leps ε / 2 ^ (q + 1) := by rw [hL2]; ring
          _ ≤ ε / 100 := hq
      have hπ : Y2 ∘ πE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp =
          Fin.append (Fin.append u (fun _ : Fin 1 => toN Y2 (sbv n ℓ₁ f₁ m q ℓ f)))
            (fun t : Fin (Bh m q) => toN Y2 (sbv n ℓ₁ f₁ m q ℓ f + 1 + t.val)) := by
        rw [comp_πE]
        have hu' : (fun i : Fin (n * ℓ₁) => toN Y2 i.val) = u := funext hY2u
        rw [hu']
      obtain ⟨Htil, hact, hacc⟩ := hAact w θ u (toN Y2 (sbv n ℓ₁ f₁ m q ℓ f))
        (fun t => toN Y2 (sbv n ℓ₁ f₁ m q ℓ f + 1 + t.val)) hw ha1 ha2 hsgn hhb'
      have hOHact : ∀ x, act OH (ket (QuantumLTF.Membership.regBasis n b Vb W x fun _ => false)) =
          ket (QuantumLTF.Membership.regBasis n b Vb W x (Htil x)) := by
        intro x; rw [hOHd]; exact blockOf_act _ _ _ _ (by rw [hπ]; exact hact x)
      have h3' := h3 w p θ hw ha1 ha2 Htil hacc OH hOHu hOHact
      rw [ge_iff_le, probEvent_zero] at h3'
      simp only [mulVec_bv_apply] at h3'
      refine le_trans h3' (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _))
      intro y' hy'
      rw [Finset.mem_filter] at hy' ⊢
      replace hy' := hy'.2
      refine ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨-, h2, h3''⟩ := hC y'
      unfold Ecert
      have hvec : (fun i => QuantumLTF.Membership.readFp
          (oaT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp i) (foT q ℓo₃ fo₃ Pp) (G y')) =
          fun i => -((QuantumLTF.Membership.sgn A : ℤ) : ℝ) *
            gW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i y' := by
        funext i; rw [h2 i, if_neg he, hsgnR]
      rw [hvec, h3'', if_neg he, hsgnR]
      apply cert_nonconst ε (2 * εg) w p θ _ _ hw ha1 ha2 hL1 hh
        (by rw [← hheight]; exact hhb') (by linarith only [hεg0]) _ hεgn
      intro i
      have hgi : |-(w i) / A| ≤ 10 := by
        rw [abs_div, abs_neg, div_le_iff₀ hApos]
        have := PiLp.norm_apply_le w i
        rw [hw, Real.norm_eq_abs] at this
        nlinarith only [this, ha1]
      have hr := hy' i
      have hrb : |QuantumLTF.Membership.readFp (oa₃ i) fo₃ y'| < 16 := by
        have := abs_sub_abs_le_abs_sub (QuantumLTF.Membership.readFp (oa₃ i) fo₃ y') (-(w i) / A)
        linarith only [this, hgi, hr, hεg1]
      have ht := trunc_err n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i y' hrb
      calc |gW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i y' - -(w i) / A|
          ≤ |gW n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp i y' - QuantumLTF.Membership.readFp (oa₃ i) fo₃ y'| +
            |QuantumLTF.Membership.readFp (oa₃ i) fo₃ y' - -(w i) / A| := abs_sub_le _ _ _
        _ ≤ 2 * εg := by linarith only [ht, hr, hPp]

open Classical in
theorem core (hAu : QuantumLTF.Membership.Uncontrolled cA)
    (h3u : QuantumLTF.Membership.Uncontrolled c₃) (ε εg η : ℝ) (Vf : ℕ)
    (hm : QuantumLTF.Membership.Leps ε = 2 ^ m)
    (hq : 2 * QuantumLTF.Membership.Leps ε / 2 ^ (q + 1) ≤ ε / 100)
    (hL1 : 1 ≤ QuantumLTF.Membership.Leps ε)
    (hLT : 20 * QuantumLTF.Membership.Teps ε ≤ QuantumLTF.Membership.Leps ε)
    (hεg0 : 0 ≤ εg) (hεg1 : εg ≤ 1) (hPp : (1 / 2 : ℝ) ^ Pp ≤ εg)
    (hεgn : Real.sqrt n * (2 * εg) ≤ ε / (100 * (QuantumLTF.Membership.Leps ε + 1)))
    (hBD : ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ),
      BlockDiag (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ))
    (hAact : ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (zp : Qubits (n * ℓ₁)) (sb : Bool)
        (hb : Qubits (Bh m q)), ‖w‖ = 1 →
        1 / 10 ≤ |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)| →
        |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)| ≤ 3 →
        (if sb then (1 : ℤ) else -1) =
          QuantumLTF.Membership.sgn (inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)) →
        |QuantumLTF.Membership.fpVal (Bh m q) (q + 1) hb -
          QuantumLTF.Membership.height w θ (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp) 0| ≤ ε / 100 →
        ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
          (∀ x, act (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
              (ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                (QuantumLTF.Membership.regBasis n b Vb W x fun _ => false))) =
            ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                (QuantumLTF.Membership.regBasis n b Vb W x (Htil x)))) ∧
          ∀ x, |QuantumLTF.Membership.fpVal Vb Vf (Htil x) -
            QuantumLTF.Membership.height w θ (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)
              (QuantumLTF.Membership.rho n • QuantumLTF.Membership.gridVec n b x)| ≤ η)
    (h3 : ∀ (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
        1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 →
        ∀ Htil : (Fin n → Qubits b) → Qubits Vb,
          (∀ x, |QuantumLTF.Membership.fpVal Vb Vf (Htil x) -
            QuantumLTF.Membership.height w θ p (QuantumLTF.Membership.rho n •
              QuantumLTF.Membership.gridVec n b x)| ≤ η) →
        ∀ OH : Matrix (Qubits (n * b + Vb + W)) (Qubits (n * b + Vb + W)) ℂ,
          OH ∈ Matrix.unitaryGroup (Qubits (n * b + Vb + W)) ℂ →
          (∀ x, act OH (ket (QuantumLTF.Membership.regBasis n b Vb W x fun _ => false)) =
            ket (QuantumLTF.Membership.regBasis n b Vb W x (Htil x))) →
          probEvent (act (c₃.unitary fun _ => OH) (zeroKet m₃))
            (fun z => ∀ i, |QuantumLTF.Membership.readFp (oa₃ i) fo₃ z - (-(w i) / inner ℝ w p)| ≤ εg)
            ≥ 5 / 6)
    (hgood : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
      ((PMF.uniformOfFintype (Qubits (n * ℓ₁))).toOuterMeasure
        {z | 1 / 10 ≤ |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ z)| ∧
          |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ z)| ≤ 3}).toReal ≥ 4 / 5)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) (θ : ℝ) :
    probEvent (act ((cAll n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃).unitary
        fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
      (zeroKet (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)))
      (Ecert n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp ε w θ) ≥ 2 / 3 := by
  have hP := perU n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃ hAu h3u ε εg η Vf hm hq hL1 hLT
    hεg0 hεg1 hPp hεgn hBD hAact h3 w hw θ
  have hU : (cAll n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃).unitary
      (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) =
      Vmat n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃ w θ *
        (hadCirc (ar := fun _ : Fin 1 => n * ℓ + 1) (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)).unitary
          (fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) := by
    unfold cAll Vmat
    simp only [unitary_append, mul_assoc]
  rw [ge_iff_le, probEvent_zero, hU, prob_mix (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) _
    (fun u y hy => (hP u).1 y hy) _ (hadCirc_zero _ _)]
  set S : Set (Qubits (n * ℓ₁)) := {z | 1 / 10 ≤ |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ z)| ∧
          |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ z)| ≤ 3} with hS
  have hg := hgood w hw
  rw [← hS, uniform_toReal] at hg
  have hcard : (Fintype.card (Qubits (n * ℓ₁)) : ℝ) = 2 ^ (n * ℓ₁) := by
    simp
  rw [hcard] at hg
  have h2pos : (0 : ℝ) < 2 ^ (n * ℓ₁) := by positivity
  rw [ge_iff_le, le_div_iff₀ h2pos] at hg
  set T := Finset.univ.filter (· ∈ S) with hT
  have hsum : (T.card : ℝ) * (5 / 6) ≤ ∑ u : Qubits (n * ℓ₁), ∑ y ∈ Finset.univ.filter
      (Ecert n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp ε w θ),
      ‖((Vmat n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃ w θ).mulVec
        (bv (setPart (fun _ => false) (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) u))) y‖ ^ 2 := by
    calc (T.card : ℝ) * (5 / 6) = ∑ u ∈ T, (5 / 6 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ u ∈ T, ∑ y ∈ Finset.univ.filter
          (Ecert n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp ε w θ),
          ‖((Vmat n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃ w θ).mulVec
            (bv (setPart (fun _ => false) (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) u))) y‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro u hu
          rw [hT, Finset.mem_filter] at hu
          exact (hP u).2 hu.2.1 hu.2.2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hfin : (1 / 2 : ℝ) ^ (n * ℓ₁) * 2 ^ (n * ℓ₁) = 1 := by
    rw [← mul_pow]; norm_num
  have h12 : (0 : ℝ) ≤ (1 / 2) ^ (n * ℓ₁) := by positivity
  calc (2 / 3 : ℝ) = (1 / 2) ^ (n * ℓ₁) * ((4 / 5 * 2 ^ (n * ℓ₁)) * (5 / 6)) := by
        rw [show (4 / 5 * (2 : ℝ) ^ (n * ℓ₁)) * (5 / 6) = (2 / 3) * 2 ^ (n * ℓ₁) by ring,
          ← mul_assoc, mul_comm _ (2 / 3 : ℝ), mul_assoc, hfin, mul_one]
    _ ≤ (1 / 2) ^ (n * ℓ₁) * ((T.card : ℝ) * (5 / 6)) := by
        apply mul_le_mul_of_nonneg_left _ h12
        exact mul_le_mul_of_nonneg_right (by convert hg using 4) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum h12

end Core

end LTFC

-- ===== module Final2 =====

open QAlgorithms

namespace LTFC

section Bins2

variable {K : ℕ} (B : ℕ)

theorem blockE_bin {k : ℕ} (g : Fin k → Instr) (p : List (OIns K)) :
    BinExt p (blockE (K := K) g p).2 := ⟨_, rfl⟩

theorem truncE_bin (src : ℕ → ℕ) (L lo K₀ : ℕ) (p : List (OIns K)) :
    BinExt p (truncE (K' := K) B src L lo K₀ p).2 := blockE_bin _ p

theorem winAll_bin (L lo K₀ : ℕ) : ∀ (ss : List (ℕ → ℕ)) (p : List (OIns K)),
    BinExt p (winAll (K' := K) B L lo K₀ ss p).2 := by
  intro ss
  induction ss with
  | nil => intro p; exact BinExt.refl _
  | cons s ss ih => intro p; exact (truncE_bin B s L lo K₀ p).trans (ih _)

theorem zipE2_bin (f : Bool → Bool → Bool) (X Y : List ℕ) (p : List (OIns K)) :
    BinExt p (zipE2 (K := K) B f X Y p).2 := ⟨_, rfl⟩

theorem muxL_bin (e : ℕ) (X Y : List ℕ) (p : List (OIns K)) :
    BinExt p (muxL (K := K) B e X Y p).2 :=
  ((mapE_bin B _ _ _ p).trans (mapE_bin B _ _ _ _)).trans (zipE2_bin B _ _ _ _)

theorem addScaledX_bin (ℓo zw ow : ℕ) (A X : List ℕ) (L' e negv negb : ℕ) (p : List (OIns K)) :
    BinExt p (addScaledX (K := K) B ℓo zw ow A X L' e negv negb p).2 :=
  (csub_bin B _ _ _ p).trans (csub_bin B _ _ _ _)

theorem outCoords_bin (ℓo fo ℓo₃ fo₃ zw ow sbv nsb eqv : ℕ) (A0 : List ℕ) :
    ∀ (Xs : List (List ℕ)) (p : List (OIns K)),
    BinExt p (outCoords (K := K) B ℓo fo ℓo₃ fo₃ zw ow sbv nsb eqv A0 Xs p).2 := by
  intro Xs
  induction Xs with
  | nil => intro p; exact BinExt.refl _
  | cons X Xs ih =>
    intro p
    exact ((addScaledX_bin B _ _ _ _ _ _ _ _ _ p).trans (muxL_bin B _ _ _ _)).trans (ih _)

theorem p0g_orc : orcCount (p0g (K := K) B) = 0 := rfl

theorem outProg_orc (ℓo fo ℓo₃ fo₃ Bh fhh n sbv eqv cv : ℕ) (gtL : List (List ℕ)) (hL : List ℕ) :
    orcCount (outProg (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh n sbv eqv cv gtL hL) = 0 := by
  unfold outProg
  rw [(blockE_bin _ _).orc]
  have h : BinExt (p0g (K := K) B)
      (outProgR (K := K) B ℓo fo ℓo₃ fo₃ Bh fhh sbv eqv cv gtL hL).2 := by
    unfold outProgR
    exact ((((emitO_bin B _ _ _ _).trans (outCoords_bin B _ _ _ _ _ _ _ _ _ _ _ _)).trans
      (addScaledX_bin B _ _ _ _ _ _ _ _ _ _)).trans (muxL_bin B _ _ _ _)).trans (muxL_bin B _ _ _ _)
  rw [h.orc, p0g_orc]

end Bins2

theorem winR_orc (n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ : ℕ) (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)) (Pp : ℕ) :
    orcCount (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2 = 0 := by
  unfold winR
  rw [(winAll_bin _ _ _ _ _ _).orc, p0g_orc]

theorem Pout_orc (n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ : ℕ) (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)) (Pp : ℕ) :
    orcCount (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) = 0 := by
  unfold Pout; exact outProg_orc _ _ _ _ _ _ _ _ _ _ _ _ _

section Counts

variable (n ℓ₁ f₁ m q ℓ f : ℕ) (hf : f₁ + q + 1 ≤ f) (hℓ : f + m + ℓ₁ + 2 ≤ ℓ)
  (m₃ ℓo₃ fo₃ : ℕ) (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)) (Pp : ℕ) (b Vb W : ℕ)
  (cA : OracleCircuit QuantumLTF.Membership.gatesRev (fun _ : Fin 1 => n * ℓ + 1)
    (n * ℓ₁ + 1 + Bh m q + (n * b + Vb + W)))
  (c₃ : OracleCircuit G12 (fun _ : Fin 1 => n * b + Vb + W) m₃)

theorem cAll_counts (hAu : QuantumLTF.Membership.Uncontrolled cA)
    (h3u : QuantumLTF.Membership.Uncontrolled c₃) :
    QuantumLTF.Membership.Uncontrolled (cAll n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃) ∧
    (cAll n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃).queryCount 0 ≤
      2 * (q + 2) + 4 + c₃.queryCount 0 * cA.queryCount 0 ∧
    (cAll n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp b Vb W cA c₃).gateCount ≤
      n * ℓ₁ + 1200 * (n * ℓ + m + q + 2) * (q + 2) +
      (20 * (2 + 2 * (n * (12 * ℓ)) + 2 * (n * ℓ + 1) + 1) + 2) +
      (c₃.gateCount + c₃.queryCount 0 * (7 * cA.gateCount)) +
      10 * (2 + n * Kw ℓo₃ fo₃ Pp) +
      10 * (3 + n * (15 * ℓoT m q ℓo₃ fo₃ Pp) + 18 * ℓoT m q ℓo₃ fo₃ Pp +
        (n + 1) * ℓoT m q ℓo₃ fo₃ Pp) := by
  obtain ⟨hu, hg, hq0⟩ := hadCirc_counts (ar := fun _ : Fin 1 => n * ℓ + 1)
    (pinG n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
  obtain ⟨ou, oq, og, -⟩ := offset_circuit n ℓ₁ f₁ m q ℓ f hf hℓ
  obtain ⟨tu, tq, tg, -⟩ := bennett (K := n * ℓ) (n * ℓ₁) (tP n ℓ₁ f₁ m q ℓ f)
    (tO n ℓ₁ f₁ m q ℓ f) (tO_valid n ℓ₁ f₁ m q ℓ f hf hℓ)
  have hts := testProg_spec n ℓ₁ f₁ m q ℓ f hf hℓ 0 0
  have htorc : orcCount (tP n ℓ₁ f₁ m q ℓ f) = 2 := hts.2.2.1
  have htlen : (tP n ℓ₁ f₁ m q ℓ f).length = 2 + 2 * (n * (12 * ℓ)) + 2 * (n * ℓ + 1) + 1 :=
    hts.2.2.2.1
  have htol : (tO n ℓ₁ f₁ m q ℓ f).length = 2 := hts.1
  obtain ⟨cu, cq, cg⟩ := convC_counts cA hAu 0
  obtain ⟨su, sq, sg⟩ := substC_counts (ιE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
    (πE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (hdE n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (convC cA) cu c₃ h3u
  obtain ⟨wu, wg, wq, -⟩ := counts_compileO (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
    (winR n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp).2 (Bw n ℓ₁ f₁ m q ℓ f m₃)
  obtain ⟨pu, pg, pq, -⟩ := counts_compileO (MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
    (Pout n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp) (Bo n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ Pp)
  rw [winR_orc] at wq
  rw [Pout_orc] at pq
  have hwl := (winR_spec n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp (fun _ => false)).1
  have hpl := (Pout_spec n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ Pp (fun _ => false)).2.1
  rw [hwl] at wg
  rw [hpl] at pg
  rw [cq] at sq
  refine ⟨?_, ?_, ?_⟩
  · unfold cAll
    exact uncontrolled_append (uncontrolled_append (uncontrolled_append (uncontrolled_append
      (uncontrolled_append hu (relabel_uncontrolled _ _)) (relabel_uncontrolled _ _)) su) wu) pu
  · unfold cAll cSub cWin cOut testCirc
    simp only [queryCount_append, relabel_queryCount, hq0]
    rw [sq]
    rw [htorc] at tq
    omega
  · unfold cAll cSub cWin cOut testCirc
    simp only [gateCount_append, relabel_gateCount, hg]
    rw [sg]
    rw [htlen, htol] at tg
    have := Nat.mul_le_mul_left (c₃.queryCount 0) cg
    omega

end Counts

end LTFC

-- ===== module H3Final =====

open QAlgorithms

namespace LTFC

theorem assembly_main :
    ∀ (n ℓ₁ f₁ m q ℓ f b Vb W Vf m₃ ℓo₃ fo₃ P : ℕ) (ε εg η : ℝ),
      f₁ + q + 1 ≤ f → f + m + ℓ₁ + 2 ≤ ℓ →
      ∀ (cA : QAlgorithms.OracleCircuit QuantumLTF.Membership.gatesRev (fun _ : Fin 1 => n * ℓ + 1)
            (n * ℓ₁ + 1 + (m + q + 2) + (n * b + Vb + W)))
        (c₃ : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
            (fun _ : Fin 1 => n * b + Vb + W) m₃)
        (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)),
      QuantumLTF.Membership.Uncontrolled cA → QuantumLTF.Membership.Uncontrolled c₃ →
      QuantumLTF.Membership.Leps ε = 2 ^ m →
      2 * QuantumLTF.Membership.Leps ε / 2 ^ (q + 1) ≤ ε / 100 →
      1 ≤ QuantumLTF.Membership.Leps ε →
      20 * QuantumLTF.Membership.Teps ε ≤ QuantumLTF.Membership.Leps ε →
      0 ≤ εg → εg ≤ 1 → (1 / 2 : ℝ) ^ P ≤ εg →
      Real.sqrt n * (2 * εg) ≤ ε / (100 * (QuantumLTF.Membership.Leps ε + 1)) →
      -- H1's block-diagonality, for this cA
      (∀ w θ (y y' : QAlgorithms.Qubits (n * ℓ₁ + 1 + (m + q + 2) + (n * b + Vb + W))),
        (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) y' y ≠ 0 →
        ∀ i : Fin (n * ℓ₁ + 1 + (m + q + 2)),
          y' (Fin.castAdd (n * b + Vb + W) i) = y (Fin.castAdd (n * b + Vb + W) i)) →
      -- H1's action, for this cA, with Bh = m + q + 2 and fh = q + 1
      (∀ w θ (zp : QAlgorithms.Qubits (n * ℓ₁)) (sb : Bool) (hb : QAlgorithms.Qubits (m + q + 2)),
        ‖w‖ = 1 → 1 / 10 ≤ |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)| →
        |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)| ≤ 3 →
        (if sb then (1 : ℤ) else -1) =
          QuantumLTF.Membership.sgn (inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)) →
        |QuantumLTF.Membership.fpVal (m + q + 2) (q + 1) hb -
          QuantumLTF.Membership.height w θ (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp) 0| ≤ ε / 100 →
        ∃ Htil : (Fin n → QAlgorithms.Qubits b) → QAlgorithms.Qubits Vb,
          (∀ x, QAlgorithms.act (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
              (QAlgorithms.ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                (QuantumLTF.Membership.regBasis n b Vb W x fun _ => false))) =
            QAlgorithms.ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                (QuantumLTF.Membership.regBasis n b Vb W x (Htil x)))) ∧
          ∀ x, |QuantumLTF.Membership.fpVal Vb Vf (Htil x) -
            QuantumLTF.Membership.height w θ (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)
              (QuantumLTF.Membership.rho n • QuantumLTF.Membership.gridVec n b x)| ≤ η) →
      -- theorem_3_3's conclusion for this c₃ (γ = 1/6)
      (∀ (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 → 1 / 10 ≤ |inner ℝ w p| →
        |inner ℝ w p| ≤ 3 → ∀ Htil : (Fin n → QAlgorithms.Qubits b) → QAlgorithms.Qubits Vb,
        (∀ x, |QuantumLTF.Membership.fpVal Vb Vf (Htil x) - QuantumLTF.Membership.height w θ p
            (QuantumLTF.Membership.rho n • QuantumLTF.Membership.gridVec n b x)| ≤ η) →
        ∀ OH : Matrix (QAlgorithms.Qubits (n * b + Vb + W)) (QAlgorithms.Qubits (n * b + Vb + W)) ℂ,
          OH ∈ Matrix.unitaryGroup (QAlgorithms.Qubits (n * b + Vb + W)) ℂ →
          (∀ x, QAlgorithms.act OH (QAlgorithms.ket (QuantumLTF.Membership.regBasis n b Vb W x
              fun _ => false)) = QAlgorithms.ket (QuantumLTF.Membership.regBasis n b Vb W x (Htil x))) →
          open Classical in
          QAlgorithms.probEvent (QAlgorithms.act (c₃.unitary fun _ => OH) (QAlgorithms.zeroKet m₃))
            (fun z => ∀ i, |QuantumLTF.Membership.readFp (oa₃ i) fo₃ z - (-(w i) / inner ℝ w p)| ≤ εg)
            ≥ 5 / 6) →
      -- uniform_dyadic_reference_direction's conclusion for (ℓ₁, f₁)
      (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
        ((PMF.uniformOfFintype (QAlgorithms.Qubits (n * ℓ₁))).toOuterMeasure
          {z | 1 / 10 ≤ |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ z)| ∧
            |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ z)| ≤ 3}).toReal ≥ 4 / 5) →
      ∃ (M ℓo fo : ℕ) (c : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
          (fun _ : Fin 1 => n * ℓ + 1) M) (oa : Fin n → (Fin ℓo ↪ Fin M)) (ob : Fin ℓo ↪ Fin M),
        QuantumLTF.Membership.Uncontrolled c ∧
        ℓo ≤ 2 * P + (q + 2) + (m + q + 2) + 8 ∧
        c.queryCount 0 ≤ 2 * (q + 2) + 4 + c₃.queryCount 0 * cA.queryCount 0 ∧
        c.gateCount ≤ n * ℓ₁ + 1200 * (n * ℓ + m + q + 2) * (q + 2) +
          (20 * (2 + 2 * (n * (12 * ℓ)) + 2 * (n * ℓ + 1) + 1) + 2) +
          (c₃.gateCount + c₃.queryCount 0 * (7 * cA.gateCount)) + 10 * (2 + n * ℓo) +
          10 * (3 + n * (15 * ℓo) + 18 * ℓo + (n + 1) * ℓo) ∧
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ θ : ℝ,
          open Classical in
          QAlgorithms.probEvent
            (QAlgorithms.act (c.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
              (QAlgorithms.zeroKet M))
            (fun z => QuantumLTF.Membership.LearningCertificate ε w θ
              (WithLp.toLp 2 fun i => QuantumLTF.Membership.readFp (oa i) fo z)
              (QuantumLTF.Membership.readFp ob fo z)) ≥ 2 / 3 := by
  intro n ℓ₁ f₁ m q ℓ f b Vb W Vf m₃ ℓo₃ fo₃ P ε εg η hf hℓ cA c₃ oa₃ hAu h3u hm hq hL1 hLT
    hεg0 hεg1 hPp hεgn hBD hAact h3 hgood
  obtain ⟨cu, cq, cg⟩ := cAll_counts n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ P b Vb W cA c₃ hAu h3u
  have hKwN : Kw ℓo₃ fo₃ P ≤ ℓoT m q ℓo₃ fo₃ P := by simp only [ℓoT, foT]; omega
  have hLoTN : ℓoT m q ℓo₃ fo₃ P ≤ 2 * P + (q + 2) + (m + q + 2) + 8 := by
    simp only [ℓoT, foT, Kw, fw, Bh]; have := Nat.min_le_right (Fw ℓo₃ fo₃) P; omega
  have hnK := Nat.mul_le_mul_left n hKwN
  refine ⟨MT n ℓ₁ f₁ m q ℓ f m₃ ℓo₃ fo₃ oa₃ P, ℓoT m q ℓo₃ fo₃ P, foT q ℓo₃ fo₃ P,
    cAll n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ P b Vb W cA c₃,
    oaT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ P, obT n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ P,
    cu, hLoTN, cq, by omega, ?_⟩
  intro w hw θ
  exact core n ℓ₁ f₁ m q ℓ f hf hℓ m₃ ℓo₃ fo₃ oa₃ P b Vb W cA c₃ hAu h3u ε εg η Vf hm hq hL1 hLT
    hεg0 hεg1 hPp hεgn (fun w θ => hBD w θ) hAact h3 hgood w hw θ

end LTFC

-- ===== final =====
theorem solution :
    ∀ (n ℓ₁ f₁ m q ℓ f b Vb W Vf m₃ ℓo₃ fo₃ P : ℕ) (ε εg η : ℝ),
      f₁ + q + 1 ≤ f → f + m + ℓ₁ + 2 ≤ ℓ →
      ∀ (cA : QAlgorithms.OracleCircuit QuantumLTF.Membership.gatesRev (fun _ : Fin 1 => n * ℓ + 1)
            (n * ℓ₁ + 1 + (m + q + 2) + (n * b + Vb + W)))
        (c₃ : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
            (fun _ : Fin 1 => n * b + Vb + W) m₃)
        (oa₃ : Fin n → (Fin ℓo₃ ↪ Fin m₃)),
      QuantumLTF.Membership.Uncontrolled cA → QuantumLTF.Membership.Uncontrolled c₃ →
      QuantumLTF.Membership.Leps ε = 2 ^ m →
      2 * QuantumLTF.Membership.Leps ε / 2 ^ (q + 1) ≤ ε / 100 →
      1 ≤ QuantumLTF.Membership.Leps ε →
      20 * QuantumLTF.Membership.Teps ε ≤ QuantumLTF.Membership.Leps ε →
      0 ≤ εg → εg ≤ 1 → (1 / 2 : ℝ) ^ P ≤ εg →
      Real.sqrt n * (2 * εg) ≤ ε / (100 * (QuantumLTF.Membership.Leps ε + 1)) →
      -- H1's block-diagonality, for this cA
      (∀ w θ (y y' : QAlgorithms.Qubits (n * ℓ₁ + 1 + (m + q + 2) + (n * b + Vb + W))),
        (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ) y' y ≠ 0 →
        ∀ i : Fin (n * ℓ₁ + 1 + (m + q + 2)),
          y' (Fin.castAdd (n * b + Vb + W) i) = y (Fin.castAdd (n * b + Vb + W) i)) →
      -- H1's action, for this cA, with Bh = m + q + 2 and fh = q + 1
      (∀ w θ (zp : QAlgorithms.Qubits (n * ℓ₁)) (sb : Bool) (hb : QAlgorithms.Qubits (m + q + 2)),
        ‖w‖ = 1 → 1 / 10 ≤ |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)| →
        |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)| ≤ 3 →
        (if sb then (1 : ℤ) else -1) =
          QuantumLTF.Membership.sgn (inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)) →
        |QuantumLTF.Membership.fpVal (m + q + 2) (q + 1) hb -
          QuantumLTF.Membership.height w θ (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp) 0| ≤ ε / 100 →
        ∃ Htil : (Fin n → QAlgorithms.Qubits b) → QAlgorithms.Qubits Vb,
          (∀ x, QAlgorithms.act (cA.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
              (QAlgorithms.ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                (QuantumLTF.Membership.regBasis n b Vb W x fun _ => false))) =
            QAlgorithms.ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                (QuantumLTF.Membership.regBasis n b Vb W x (Htil x)))) ∧
          ∀ x, |QuantumLTF.Membership.fpVal Vb Vf (Htil x) -
            QuantumLTF.Membership.height w θ (QuantumLTF.Membership.addrOf n ℓ₁ f₁ zp)
              (QuantumLTF.Membership.rho n • QuantumLTF.Membership.gridVec n b x)| ≤ η) →
      -- theorem_3_3's conclusion for this c₃ (γ = 1/6)
      (∀ (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 → 1 / 10 ≤ |inner ℝ w p| →
        |inner ℝ w p| ≤ 3 → ∀ Htil : (Fin n → QAlgorithms.Qubits b) → QAlgorithms.Qubits Vb,
        (∀ x, |QuantumLTF.Membership.fpVal Vb Vf (Htil x) - QuantumLTF.Membership.height w θ p
            (QuantumLTF.Membership.rho n • QuantumLTF.Membership.gridVec n b x)| ≤ η) →
        ∀ OH : Matrix (QAlgorithms.Qubits (n * b + Vb + W)) (QAlgorithms.Qubits (n * b + Vb + W)) ℂ,
          OH ∈ Matrix.unitaryGroup (QAlgorithms.Qubits (n * b + Vb + W)) ℂ →
          (∀ x, QAlgorithms.act OH (QAlgorithms.ket (QuantumLTF.Membership.regBasis n b Vb W x
              fun _ => false)) = QAlgorithms.ket (QuantumLTF.Membership.regBasis n b Vb W x (Htil x))) →
          open Classical in
          QAlgorithms.probEvent (QAlgorithms.act (c₃.unitary fun _ => OH) (QAlgorithms.zeroKet m₃))
            (fun z => ∀ i, |QuantumLTF.Membership.readFp (oa₃ i) fo₃ z - (-(w i) / inner ℝ w p)| ≤ εg)
            ≥ 5 / 6) →
      -- uniform_dyadic_reference_direction's conclusion for (ℓ₁, f₁)
      (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
        ((PMF.uniformOfFintype (QAlgorithms.Qubits (n * ℓ₁))).toOuterMeasure
          {z | 1 / 10 ≤ |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ z)| ∧
            |inner ℝ w (QuantumLTF.Membership.addrOf n ℓ₁ f₁ z)| ≤ 3}).toReal ≥ 4 / 5) →
      ∃ (M ℓo fo : ℕ) (c : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
          (fun _ : Fin 1 => n * ℓ + 1) M) (oa : Fin n → (Fin ℓo ↪ Fin M)) (ob : Fin ℓo ↪ Fin M),
        QuantumLTF.Membership.Uncontrolled c ∧
        ℓo ≤ 2 * P + (q + 2) + (m + q + 2) + 8 ∧
        c.queryCount 0 ≤ 2 * (q + 2) + 4 + c₃.queryCount 0 * cA.queryCount 0 ∧
        c.gateCount ≤ n * ℓ₁ + 1200 * (n * ℓ + m + q + 2) * (q + 2) +
          (20 * (2 + 2 * (n * (12 * ℓ)) + 2 * (n * ℓ + 1) + 1) + 2) +
          (c₃.gateCount + c₃.queryCount 0 * (7 * cA.gateCount)) + 10 * (2 + n * ℓo) +
          10 * (3 + n * (15 * ℓo) + 18 * ℓo + (n + 1) * ℓo) ∧
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ θ : ℝ,
          open Classical in
          QAlgorithms.probEvent
            (QAlgorithms.act (c.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
              (QAlgorithms.zeroKet M))
            (fun z => QuantumLTF.Membership.LearningCertificate ε w θ
              (WithLp.toLp 2 fun i => QuantumLTF.Membership.readFp (oa i) fo z)
              (QuantumLTF.Membership.readFp ob fo z)) ≥ 2 / 3 :=
  LTFC.assembly_main
