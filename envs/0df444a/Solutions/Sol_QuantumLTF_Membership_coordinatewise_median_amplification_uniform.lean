-- Prove2me | solution 1 for QuantumLTF.Membership.coordinatewise_median_amplification_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-23T20:00:50.031218+00:00
-- url     : https://prove2.me/submissions/12634042-1154-4e0d-bf0b-eac8d6271c04

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled

set_option maxHeartbeats 1000000

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

theorem setPart_self (z : Qubits n) (w : Fin k ↪ Fin n) : setPart z w (z ∘ w) = z := by
  symm; rw [eq_setPart_iff]; exact ⟨rfl, fun _ _ => rfl⟩

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

theorem relabel_append {m n : ℕ} (c₁ c₂ : OracleCircuit S a m) (e : Fin m ↪ Fin n) :
    relabel (c₁ ++ c₂) e = relabel c₁ e ++ relabel c₂ e := by
  simp [relabel]

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

theorem comp_w2 {n : ℕ} (z : Qubits n) (a b : Fin n) (h : a ≠ b) :
    z ∘ (w2 a b h) = ![z a, z b] := by
  funext x; fin_cases x <;> simp

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

/-- Value of variable `v`: inputs below `B`; instruction `i` defines variable `B + i`. -/
def sval (B : ℕ) (P : List Instr) (inp : ℕ → Bool) (v : ℕ) : Bool :=
  if v < B then inp v else
    if h : v - B < P.length then
      if ha : P[v - B].a < v ∧ P[v - B].b < v then
        P[v - B].f (sval B P inp P[v - B].a) (sval B P inp P[v - B].b)
      else false
    else false
termination_by v
decreasing_by all_goals omega

theorem sval_lt (B : ℕ) (P : List Instr) (inp : ℕ → Bool) {v : ℕ} (hv : v < B) :
    sval B P inp v = inp v := by
  rw [sval, if_pos hv]

theorem sval_append (B : ℕ) (p q : List Instr) (inp : ℕ → Bool) :
    ∀ v, v < B + p.length → sval B (p ++ q) inp v = sval B p inp v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro hv
  rw [sval, sval]
  by_cases hB : v < B
  · simp [hB]
  · simp only [hB, if_false]
    have h1 : v - B < p.length := by omega
    have h2 : v - B < (p ++ q).length := by simp; omega
    rw [dif_pos h1, dif_pos h2]
    have he : (p ++ q)[v - B] = p[v - B] := List.getElem_append_left h1
    simp only [he]
    split_ifs with ha
    · rw [ih _ ha.1 (by omega), ih _ ha.2 (by omega)]
    · rfl

theorem sval_at (B : ℕ) (P : List Instr) (inp : ℕ → Bool) (i : ℕ) (hi : i < P.length)
    (ha : P[i].a < B + i) (hb : P[i].b < B + i) :
    sval B P inp (B + i) = P[i].f (sval B P inp P[i].a) (sval B P inp P[i].b) := by
  rw [sval, if_neg (by omega)]
  have e : B + i - B = i := by omega
  simp only [e]
  rw [dif_pos hi, dif_pos ⟨ha, hb⟩]

theorem sval_at_invalid (B : ℕ) (P : List Instr) (inp : ℕ → Bool) (i : ℕ) (hi : i < P.length)
    (h : ¬ (P[i].a < B + i ∧ P[i].b < B + i)) :
    sval B P inp (B + i) = false := by
  rw [sval, if_neg (by omega)]
  have e : B + i - B = i := by omega
  simp only [e]
  rw [dif_pos hi, dif_neg h]

/-- Shift the base by one instruction. -/
theorem sval_cons (B : ℕ) (g : Instr) (gs : List Instr) (inp : ℕ → Bool) :
    ∀ v, sval B (g :: gs) inp v =
      sval (B + 1) gs (Function.update inp B
        (if g.a < B ∧ g.b < B then g.f (inp g.a) (inp g.b) else false)) v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  by_cases hB : v < B
  · rw [sval_lt _ _ _ hB, sval_lt _ _ _ (show v < B + 1 by omega),
      Function.update_of_ne (show v ≠ B by omega)]
  by_cases hB1 : v = B
  · rw [hB1, sval_lt _ _ _ (show B < B + 1 by omega), Function.update_self]
    have := sval_at B (g :: gs) inp 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at this
    by_cases hc : g.a < B ∧ g.b < B
    · rw [if_pos hc, this hc.1 hc.2, sval_lt _ _ _ hc.1, sval_lt _ _ _ hc.2]
    · rw [if_neg hc]
      have := sval_at_invalid B (g :: gs) inp 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at this
      exact this hc
  · rw [sval, sval, if_neg hB, if_neg (show ¬ v < B + 1 by omega)]
    have e : v - B = (v - (B + 1)) + 1 := by omega
    by_cases hl : v - (B + 1) < gs.length
    · have hl' : v - B < (g :: gs).length := by simp; omega
      rw [dif_pos hl', dif_pos hl]
      have he : (g :: gs)[v - B] = gs[v - (B + 1)] := by
        simp only [e, List.getElem_cons_succ]
      simp only [he]
      by_cases ha : gs[v - (B + 1)].a < v ∧ gs[v - (B + 1)].b < v
      · rw [dif_pos ha, dif_pos ha, ih _ ha.1, ih _ ha.2]
      · rw [dif_neg ha, dif_neg ha]
    · have hl' : ¬ (v - B < (g :: gs).length) := by simp; omega
      rw [dif_neg hl', dif_neg hl]

/-! ### Holds: properties of all evaluations of all extensions -/

def Holds (B : ℕ) (p : List Instr) (Q : (ℕ → Bool) → Prop) : Prop :=
  ∀ q inp, Q (sval B (p ++ q) inp)

def Ext (p p' : List Instr) : Prop := ∃ r, p' = p ++ r

theorem Ext.refl (p : List Instr) : Ext p p := ⟨[], by simp⟩

theorem Ext.trans {p p' p'' : List Instr} (h₁ : Ext p p') (h₂ : Ext p' p'') : Ext p p'' := by
  obtain ⟨r, rfl⟩ := h₁; obtain ⟨r', rfl⟩ := h₂; exact ⟨r ++ r', by simp⟩

theorem Ext.app (p r : List Instr) : Ext p (p ++ r) := ⟨r, rfl⟩

theorem Ext.length_le {p p' : List Instr} (h : Ext p p') : p.length ≤ p'.length := by
  obtain ⟨r, rfl⟩ := h; simp

theorem Holds.mono {B : ℕ} {p p' : List Instr} {Q : (ℕ → Bool) → Prop} (h : Holds B p Q)
    (he : Ext p p') : Holds B p' Q := by
  obtain ⟨r, rfl⟩ := he
  intro q inp
  have := h (r ++ q) inp
  simpa [List.append_assoc] using this

theorem Holds.and {B : ℕ} {p : List Instr} {Q₁ Q₂ : (ℕ → Bool) → Prop} (h₁ : Holds B p Q₁)
    (h₂ : Holds B p Q₂) : Holds B p (fun σ => Q₁ σ ∧ Q₂ σ) := fun q inp => ⟨h₁ q inp, h₂ q inp⟩

theorem Holds.imp {B : ℕ} {p : List Instr} {Q₁ Q₂ : (ℕ → Bool) → Prop} (h₁ : Holds B p Q₁)
    (h : ∀ σ, Q₁ σ → Q₂ σ) : Holds B p Q₂ := fun q inp => h _ (h₁ q inp)

/-- A block of instructions appended at once. -/
theorem holds_block (B : ℕ) (p : List Instr) {k : ℕ} (g : Fin k → Instr)
    (hg : ∀ j, (g j).a < B + p.length ∧ (g j).b < B + p.length) :
    Holds B (p ++ List.ofFn g) (fun σ => ∀ j : Fin k,
      σ (B + p.length + j) = (g j).f (σ (g j).a) (σ (g j).b)) := by
  intro q inp j
  have hi : p.length + j < (p ++ List.ofFn g ++ q).length := by simp; omega
  have hget : (p ++ List.ofFn g ++ q)[p.length + j] = g j := by
    rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn]; omega)]
    rw [List.getElem_append_right (by omega)]
    simp
  have := sval_at B (p ++ List.ofFn g ++ q) inp (p.length + j) hi
    (by rw [hget]; have := (hg j).1; omega) (by rw [hget]; have := (hg j).2; omega)
  rw [hget] at this
  rw [← this, Nat.add_assoc]

theorem holds_single (B : ℕ) (p : List Instr) (g : Instr)
    (ha : g.a < B + p.length) (hb : g.b < B + p.length) :
    Holds B (p ++ [g]) (fun σ => σ (B + p.length) = g.f (σ g.a) (σ g.b)) := by
  intro q inp
  have hi : p.length < (p ++ [g] ++ q).length := by simp
  have hget : (p ++ [g] ++ q)[p.length] = g := by simp
  have := sval_at B (p ++ [g] ++ q) inp p.length hi (by rw [hget]; exact ha)
    (by rw [hget]; exact hb)
  rw [hget] at this
  exact this

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

theorem flipT_false {M : ℕ} (t : Fin M) (z : Qubits M) : flipT t (fun _ => false) z = z := by
  simp [flipT]

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

noncomputable def compileAux (M : ℕ) : List Instr → ℕ → OracleCircuit G12 ar M
  | [], _ => []
  | g :: gs, pos => instrCirc M g pos ++ compileAux M gs (pos + 1)

def runP (M : ℕ) : List Instr → ℕ → Qubits M → Qubits M
  | [], _ => id
  | g :: gs, pos => runP M gs (pos + 1) ∘ stepF M g pos

theorem impl_compile (M : ℕ) (P : List Instr) (pos : ℕ) :
    Implements (compileAux M P pos : OracleCircuit G12 ar M) (runP M P pos) := by
  induction P generalizing pos with
  | nil => exact Implements.nil
  | cons g gs ih => exact (impl_instr M g pos).append (ih (pos + 1))

theorem toN_update {M : ℕ} (z : Qubits M) (t : ℕ) (ht : t < M) (v : Bool) :
    toN (Function.update z ⟨t, ht⟩ v) = Function.update (toN z) t v := by
  funext x
  unfold toN
  by_cases hx : x = t
  · subst hx; simp [ht]
  · rw [Function.update_of_ne hx]
    split_ifs with h
    · rw [Function.update_of_ne]; intro e; simp at e; exact hx e
    · rfl

theorem run_correct (M : ℕ) (P : List Instr) :
    ∀ (pos : ℕ) (z : Qubits M), pos + P.length ≤ M → (∀ v : Fin M, pos ≤ v.val → z v = false) →
      toN (runP M P pos z) = fun v => if v < M then sval pos P (toN z) v else false := by
  induction P with
  | nil =>
    intro pos z _ hz
    funext v
    simp only [runP, id]
    split_ifs with hv
    · rw [sval]
      by_cases h1 : v < pos
      · rw [if_pos h1]
      · rw [if_neg h1, dif_neg (by simp)]
        have := hz ⟨v, hv⟩ (by show pos ≤ v; omega)
        simp only [toN, dif_pos hv]; exact this
    · simp [toN, hv]
  | cons g gs ih =>
    intro pos z hlen hz
    simp only [runP, Function.comp_apply]
    have hpos : pos < M := by simp at hlen; omega
    have hz' : ∀ v : Fin M, pos + 1 ≤ v.val → stepF M g pos z v = false := by
      intro v hv
      unfold stepF
      split_ifs with h
      · rw [Function.update_of_ne]; · exact hz v (by omega)
        intro e; rw [e] at hv; simp at hv
      · exact hz v (by omega)
    rw [ih (pos + 1) _ (by simp at hlen; omega) hz']
    funext v
    split_ifs with hv
    · rw [sval_cons]
      congr 1
      unfold stepF
      by_cases h : pos < M ∧ g.a < pos ∧ g.b < pos
      · rw [dif_pos h, if_pos ⟨h.2.1, h.2.2⟩, toN_update]
        congr 1
        have hzp : z ⟨pos, hpos⟩ = false := hz _ le_rfl
        rw [hzp, Bool.false_xor]
        simp only [toN, dif_pos (show g.a < M by omega), dif_pos (show g.b < M by omega)]
      · have h' : ¬ (g.a < pos ∧ g.b < pos) := fun h' => h ⟨hpos, h'⟩
        rw [dif_neg h, if_neg h']
        funext x
        by_cases hx : x = pos
        · subst hx; simp [toN, hpos, hz ⟨x, hpos⟩ le_rfl]
        · rw [Function.update_of_ne hx]
    · rfl

/-- Final semantics: on states whose wires at or above `B` are zero. -/
theorem compile_sem (M B : ℕ) (P : List Instr) (hM : B + P.length ≤ M) (z : Qubits M)
    (hz : ∀ v : Fin M, B ≤ v.val → z v = false) (v : Fin M) :
    runP M P B z v = sval B P (toN z) v := by
  have := congrFun (run_correct M P B z hM hz) v
  simp only [toN, v.isLt, dif_pos, if_true] at this
  simpa using this

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

theorem allGates_compile (M : ℕ) (P : List Instr) (pos : ℕ) :
    AllGates (compileAux M P pos : OracleCircuit G12 ar M) := by
  induction P generalizing pos with
  | nil => exact AllGates.nil
  | cons g gs ih => exact (allGates_instr M g pos).append (ih _)

theorem length_compile (M : ℕ) (P : List Instr) (pos : ℕ) :
    (compileAux M P pos : OracleCircuit G12 ar M).length ≤ 10 * P.length := by
  induction P generalizing pos with
  | nil => simp [compileAux]
  | cons g gs ih =>
    simp only [compileAux, List.length_append, List.length_cons]
    have := length_instr (ar := ar) M g pos
    have := ih (pos + 1)
    omega

end Compile

end LTFC

-- ===== module MedMath =====

namespace LTFC

/-- Most-significant-bit-first value with accumulator. -/
def msb : ℕ → List Bool → ℕ
  | acc, [] => acc
  | acc, b :: bs => msb (2 * acc + b.toNat) bs

theorem card_eq_sum_toNat {k : ℕ} (Q : Fin k → Prop) [DecidablePred Q] :
    (Finset.univ.filter Q).card = ∑ j, (decide (Q j)).toNat := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : Q j <;> simp [h]

theorem inv_step (k s : ℕ) (pre : Fin k → ℕ) (P : ℕ) (bt : Fin k → Bool) (Mt : Bool)
    (h1 : (Finset.univ.filter fun j => pre j < P).card ≤ s)
    (h2 : s + 1 ≤ (Finset.univ.filter fun j => pre j ≤ P).card)
    (hM : Mt = !decide (s < ∑ j, (decide (pre j < P) || (!decide (P < pre j) && !bt j)).toNat)) :
    (∀ j, (decide (pre j < P) || ((!decide (P < pre j) && !bt j) && Mt)) =
          decide (2 * pre j + (bt j).toNat < 2 * P + Mt.toNat) ∧
        (decide (P < pre j) || ((!decide (pre j < P) && bt j) && !Mt)) =
          decide (2 * P + Mt.toNat < 2 * pre j + (bt j).toNat)) ∧
    (Finset.univ.filter fun j => 2 * pre j + (bt j).toNat < 2 * P + Mt.toNat).card ≤ s ∧
    s + 1 ≤ (Finset.univ.filter fun j => 2 * pre j + (bt j).toNat ≤ 2 * P + Mt.toNat).card := by
  have hx : ∀ j, (decide (pre j < P) || (!decide (P < pre j) && !bt j)) =
      decide (2 * pre j + (bt j).toNat ≤ 2 * P) := by
    intro j
    cases bt j <;> by_cases ha : pre j < P <;> by_cases hb : P < pre j <;> simp [ha, hb] <;> omega
  simp only [hx] at hM
  rw [← card_eq_sum_toNat] at hM
  set C := (Finset.univ.filter fun j => 2 * pre j + (bt j).toNat ≤ 2 * P).card with hC
  refine ⟨?_, ?_⟩
  · intro j
    cases hMt : Mt <;> cases bt j <;> by_cases ha : pre j < P <;> by_cases hb : P < pre j <;>
      simp [ha, hb] <;> omega
  by_cases hsC : s < C
  · have hMf : Mt = false := by rw [hM]; simp [hsC]
    subst hMf
    simp only [Bool.toNat_false, Nat.add_zero]
    constructor
    · calc (Finset.univ.filter fun j => 2 * pre j + (bt j).toNat < 2 * P).card
          = (Finset.univ.filter fun j => pre j < P).card := by
            congr 1; apply Finset.filter_congr; intro j _
            cases bt j <;> simp <;> omega
        _ ≤ s := h1
    · omega
  · have hMt : Mt = true := by rw [hM]; simp [hsC]
    subst hMt
    simp only [Bool.toNat_true]
    constructor
    · calc (Finset.univ.filter fun j => 2 * pre j + (bt j).toNat < 2 * P + 1).card
          = C := by
            rw [hC]; congr 1; apply Finset.filter_congr; intro j _; omega
        _ ≤ s := by omega
    · calc s + 1 ≤ (Finset.univ.filter fun j => pre j ≤ P).card := h2
        _ = (Finset.univ.filter fun j => 2 * pre j + (bt j).toNat ≤ 2 * P + 1).card := by
            congr 1; apply Finset.filter_congr; intro j _
            cases bt j <;> simp <;> omega

/-- The rank-`(s+1)` element is close whenever more than half of the values are close. -/
theorem median_close (k s : ℕ) (hk : k = 2 * s + 1) (V : Fin k → ℕ) (Mv : ℕ) (φ : ℕ → ℝ)
    (hφ : StrictMono φ) (g δ : ℝ) (Good : Finset (Fin k))
    (hgood : ∀ j ∈ Good, |φ (V j) - g| ≤ δ) (hcard : s + 1 ≤ Good.card)
    (h1 : (Finset.univ.filter fun j => V j < Mv).card ≤ s)
    (h2 : s + 1 ≤ (Finset.univ.filter fun j => V j ≤ Mv).card) : |φ Mv - g| ≤ δ := by
  rw [abs_le]
  by_contra hcon
  rw [not_and_or] at hcon
  rcases hcon with hlo | hhi
  · push Not at hlo
    have hsub : (Finset.univ.filter fun j => V j ≤ Mv) ⊆ Goodᶜ := by
      intro j hj
      rw [Finset.mem_compl]
      intro hjG
      have := abs_le.1 (hgood j hjG)
      have hlt : φ Mv < φ (V j) := by linarith
      have := hφ.lt_iff_lt.1 hlt
      simp at hj; omega
    have := Finset.card_le_card hsub
    rw [Finset.card_compl, Fintype.card_fin] at this
    omega
  · push Not at hhi
    have hsub : Good ⊆ (Finset.univ.filter fun j => V j < Mv) := by
      intro j hjG
      have := abs_le.1 (hgood j hjG)
      have hlt : φ (V j) < φ Mv := by linarith
      simpa using hφ.lt_iff_lt.1 hlt
    have := Finset.card_le_card hsub
    omega

/-- Majority amplification tail bound. -/
theorem tail_bound (k : ℕ) {X : Type} [Fintype X] (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) (G : X → Prop) [DecidablePred G]
    (hG : 3 / 4 ≤ ∑ x ∈ Finset.univ.filter G, p x) :
    1 - (7 / 8 : ℝ) ^ k ≤ ∑ x : Fin k → X, (∏ j, p (x j)) *
      (if k < 2 * (Finset.univ.filter fun j => G (x j)).card then 1 else 0) := by
  set w : X → ℝ := fun y => if G y then 1 else 4 with hw
  have htot : ∑ x : Fin k → X, ∏ j, p (x j) = 1 := by
    rw [← Fintype.prod_sum (fun _ : Fin k => p)]
    simp [hsum]
  have hW : ∑ x : Fin k → X, ∏ j, (p (x j) * w (x j)) = (∑ y, p y * w y) ^ k := by
    rw [← Fintype.prod_sum (fun _ : Fin k => fun y => p y * w y)]
    simp
  have hpw : ∑ y, p y * w y ≤ 7 / 4 := by
    have e1 : ∀ y, p y * w y = p y + 3 * (if G y then 0 else p y) := by
      intro y; simp only [hw]; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun y _ => e1 y), Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    have e2 : ∑ y, (if G y then 0 else p y) = ∑ y ∈ Finset.univ.filter (fun y => ¬ G y), p y := by
      rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro y _; by_cases h : G y <;> simp [h]
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ G p
    rw [e2]
    linarith
  have hpoint : ∀ x : Fin k → X, (∏ j, p (x j)) *
      (if 2 * (Finset.univ.filter fun j => G (x j)).card ≤ k then 1 else 0) ≤
      (∏ j, (p (x j) * w (x j))) / 2 ^ k := by
    intro x
    have hP : 0 ≤ ∏ j, p (x j) := Finset.prod_nonneg (fun j _ => hp _)
    rw [Finset.prod_mul_distrib]
    have hwprod : ∏ j, w (x j) = 4 ^ (Finset.univ.filter fun j => ¬ G (x j)).card := by
      simp only [hw]
      rw [Finset.prod_ite]
      simp
    rw [hwprod]
    split_ifs with h
    · rw [mul_one, mul_div_assoc]
      have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun j => G (x j))
      rw [Finset.card_univ, Fintype.card_fin] at hc
      have h4 : (2 : ℝ) ^ k ≤ 4 ^ (Finset.univ.filter fun j => ¬ G (x j)).card := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have : 1 ≤ (4 : ℝ) ^ (Finset.univ.filter fun j => ¬ G (x j)).card / 2 ^ k := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith
    · rw [mul_zero]; positivity
  have hbad : ∑ x : Fin k → X, (∏ j, p (x j)) *
      (if 2 * (Finset.univ.filter fun j => G (x j)).card ≤ k then 1 else 0) ≤ (7 / 8) ^ k := by
    calc _ ≤ ∑ x : Fin k → X, (∏ j, (p (x j) * w (x j))) / 2 ^ k := Finset.sum_le_sum (fun x _ => hpoint x)
      _ = (∑ y, p y * w y) ^ k / 2 ^ k := by rw [← Finset.sum_div, hW]
      _ ≤ (7 / 4) ^ k / 2 ^ k := by
          have h0 : 0 ≤ ∑ y, p y * w y := Finset.sum_nonneg (fun y _ => mul_nonneg (hp y)
            (by simp only [hw]; split_ifs <;> norm_num))
          gcongr
      _ = (7 / 8) ^ k := by rw [← div_pow]; norm_num
  have hsplit : ∀ x : Fin k → X, (∏ j, p (x j)) =
      (∏ j, p (x j)) * (if k < 2 * (Finset.univ.filter fun j => G (x j)).card then 1 else 0) +
      (∏ j, p (x j)) * (if 2 * (Finset.univ.filter fun j => G (x j)).card ≤ k then 1 else 0) := by
    intro x
    by_cases h : k < 2 * (Finset.univ.filter fun j => G (x j)).card
    · rw [if_pos h, if_neg (by omega)]; ring
    · rw [if_neg h, if_pos (by omega)]; ring
  have := Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hsplit x)
  rw [Finset.sum_add_distrib, htot] at this
  linarith

end LTFC

-- ===== module Build =====

namespace LTFC

def numVal (σ : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | x :: xs => (σ x).toNat + 2 * numVal σ xs

theorem holds_list (B : ℕ) (p gs : List Instr)
    (hg : ∀ i (hi : i < gs.length), gs[i].a < B + p.length + i ∧ gs[i].b < B + p.length + i) :
    Holds B (p ++ gs) (fun σ => ∀ i (hi : i < gs.length),
      σ (B + p.length + i) = gs[i].f (σ gs[i].a) (σ gs[i].b)) := by
  intro q inp i hi
  have hi' : p.length + i < (p ++ gs ++ q).length := by simp; omega
  have hget : (p ++ gs ++ q)[p.length + i] = gs[i] := by
    rw [List.getElem_append_left (by simp only [List.length_append]; omega)]
    rw [List.getElem_append_right (by omega)]
    simp
  have := sval_at B (p ++ gs ++ q) inp (p.length + i) hi'
    (by rw [hget]; have := (hg i hi).1; omega) (by rw [hget]; have := (hg i hi).2; omega)
  rw [hget] at this
  rw [← this, Nat.add_assoc]

section Build

variable (B : ℕ)

abbrev Bld (α : Type) := List Instr → α × List Instr

def emit (f : Bool → Bool → Bool) (a b : ℕ) : Bld ℕ :=
  fun p => (B + p.length, p ++ [⟨f, a, b⟩])

def zipE {k : ℕ} (f : Bool → Bool → Bool) (as bs : Fin k → ℕ) : Bld (Fin k → ℕ) :=
  fun p => (fun j => B + p.length + j, p ++ List.ofFn (fun j => (⟨f, as j, bs j⟩ : Instr)))

theorem emit_spec (f : Bool → Bool → Bool) (a b : ℕ) (p : List Instr)
    (ha : a < B + p.length) (hb : b < B + p.length) :
    Ext p (emit B f a b p).2 ∧ (emit B f a b p).2.length = p.length + 1 ∧
    (emit B f a b p).1 < B + (emit B f a b p).2.length ∧
    Holds B (emit B f a b p).2 (fun σ => σ (emit B f a b p).1 = f (σ a) (σ b)) := by
  refine ⟨Ext.app _ _, by simp [emit], by simp [emit], ?_⟩
  exact holds_single B p ⟨f, a, b⟩ ha hb

theorem zipE_spec {k : ℕ} (f : Bool → Bool → Bool) (as bs : Fin k → ℕ) (p : List Instr)
    (ha : ∀ j, as j < B + p.length) (hb : ∀ j, bs j < B + p.length) :
    Ext p (zipE B f as bs p).2 ∧ (zipE B f as bs p).2.length = p.length + k ∧
    (∀ j, (zipE B f as bs p).1 j < B + (zipE B f as bs p).2.length) ∧
    Holds B (zipE B f as bs p).2
      (fun σ => ∀ j, σ ((zipE B f as bs p).1 j) = f (σ (as j)) (σ (bs j))) := by
  refine ⟨Ext.app _ _, by simp [zipE], fun j => by simp [zipE]; omega, ?_⟩
  exact holds_block B p (fun j => (⟨f, as j, bs j⟩ : Instr)) (fun j => ⟨ha j, hb j⟩)

/-! ### Ripple-carry adder (LSB first) -/

def addc : List ℕ → List ℕ → ℕ → Bld (List ℕ)
  | x :: xs, y :: ys, c => fun p =>
      let n := B + p.length
      let r := addc xs ys (n + 4) (p ++ [⟨xor, x, y⟩, ⟨xor, n, c⟩, ⟨(· && ·), x, y⟩,
        ⟨(· && ·), c, n⟩, ⟨(· || ·), n + 2, n + 3⟩])
      ((n + 1) :: r.1, r.2)
  | _, _, c => fun p => ([c], p)

theorem full_adder (a b c : Bool) :
    a.toNat + b.toNat + c.toNat =
      (xor (xor a b) c).toNat + 2 * ((a && b) || (c && xor a b)).toNat := by
  cases a <;> cases b <;> cases c <;> rfl

theorem addc_spec : ∀ (xs ys : List ℕ) (c : ℕ) (p : List Instr), xs.length = ys.length →
    (∀ v ∈ xs, v < B + p.length) → (∀ v ∈ ys, v < B + p.length) → c < B + p.length →
    Ext p (addc B xs ys c p).2 ∧ (addc B xs ys c p).2.length = p.length + 5 * xs.length ∧
    (addc B xs ys c p).1.length = xs.length + 1 ∧
    (∀ v ∈ (addc B xs ys c p).1, v < B + (addc B xs ys c p).2.length) ∧
    Holds B (addc B xs ys c p).2
      (fun σ => numVal σ (addc B xs ys c p).1 = numVal σ xs + numVal σ ys + (σ c).toNat) := by
  intro xs
  induction xs with
  | nil =>
    intro ys c p hl _ _ hc
    have : ys = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
    subst this
    refine ⟨Ext.refl _, by simp [addc], by simp [addc], ?_, ?_⟩
    · intro v hv; simp only [addc, List.mem_singleton] at hv ⊢; omega
    · intro q inp; simp [addc, numVal]
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
    have hp1 : (p ++ blk).length = p.length + 5 := by simp [hblk]
    obtain ⟨e1, l1, o1, v1, h1⟩ := ih ys (n + 4) (p ++ blk) hl
      (fun v hv => by have := hx v (List.mem_cons_of_mem _ hv); rw [hp1]; omega)
      (fun v hv => by have := hy v (List.mem_cons_of_mem _ hv); rw [hp1]; omega)
      (by rw [hp1]; omega)
    have hb := holds_list B p blk (by
      intro i hi
      simp only [hblk, List.length_cons, List.length_nil] at hi
      interval_cases i <;> simp [hblk] <;> omega)
    have hext : Ext p (addc B xs ys (n + 4) (p ++ blk)).2 := (Ext.app p blk).trans e1
    change Ext p (addc B xs ys (n + 4) (p ++ blk)).2 ∧
      (addc B xs ys (n + 4) (p ++ blk)).2.length = p.length + 5 * (xs.length + 1) ∧
      ((n + 1) :: (addc B xs ys (n + 4) (p ++ blk)).1).length = xs.length + 1 + 1 ∧
      (∀ v ∈ (n + 1) :: (addc B xs ys (n + 4) (p ++ blk)).1,
        v < B + (addc B xs ys (n + 4) (p ++ blk)).2.length) ∧
      Holds B (addc B xs ys (n + 4) (p ++ blk)).2 (fun σ =>
        numVal σ ((n + 1) :: (addc B xs ys (n + 4) (p ++ blk)).1) =
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

/-! ### Counting tree -/

def cnt : ℕ → List ℕ → ℕ → Bld (List ℕ)
  | 0, xs, _ => fun p => (xs, p)
  | d + 1, xs, z => fun p =>
      let r1 := cnt d (xs.take (2 ^ d)) z p
      let r2 := cnt d (xs.drop (2 ^ d)) z r1.2
      addc B r1.1 r2.1 z r2.2

def cntCost : ℕ → ℕ
  | 0 => 0
  | d + 1 => 2 * cntCost d + 5 * (d + 1)

theorem cntCost_le (d : ℕ) : cntCost d + 5 * (d + 2) ≤ 5 * 2 ^ (d + 1) := by
  induction d with
  | zero => simp [cntCost]
  | succ d ih =>
    simp only [cntCost]
    rw [pow_succ]
    omega

theorem cnt_spec : ∀ (d : ℕ) (xs : List ℕ) (z : ℕ) (p : List Instr), xs.length = 2 ^ d →
    (∀ v ∈ xs, v < B + p.length) → z < B + p.length → Holds B p (fun σ => σ z = false) →
    Ext p (cnt B d xs z p).2 ∧ (cnt B d xs z p).2.length = p.length + cntCost d ∧
    (cnt B d xs z p).1.length = d + 1 ∧
    (∀ v ∈ (cnt B d xs z p).1, v < B + (cnt B d xs z p).2.length) ∧
    Holds B (cnt B d xs z p).2
      (fun σ => numVal σ (cnt B d xs z p).1 = (xs.map fun v => (σ v).toNat).sum) := by
  intro d
  induction d with
  | zero =>
    intro xs z p hl hx _ _
    simp only [pow_zero] at hl
    obtain ⟨x, rfl⟩ : ∃ x, xs = [x] := List.length_eq_one_iff.1 hl
    refine ⟨Ext.refl _, by simp [cnt, cntCost], by simp [cnt], fun v hv => hx v hv, ?_⟩
    intro q inp; simp [cnt, numVal]
  | succ d ih =>
    intro xs z p hl hx hz hz0
    have hlt : (xs.take (2 ^ d)).length = 2 ^ d := by simp [hl, pow_succ]
    have hld : (xs.drop (2 ^ d)).length = 2 ^ d := by simp [hl, pow_succ]; omega
    obtain ⟨e1, l1, o1, v1, h1⟩ := ih (xs.take (2 ^ d)) z p hlt
      (fun v hv => hx v (List.mem_of_mem_take hv)) hz hz0
    obtain ⟨e2, l2, o2, v2, h2⟩ := ih (xs.drop (2 ^ d)) z (cnt B d (xs.take (2 ^ d)) z p).2 hld
      (fun v hv => by have := hx v (List.mem_of_mem_drop hv); have := e1.length_le; omega)
      (by have := e1.length_le; omega) (hz0.mono e1)
    have hle2 := e2.length_le
    obtain ⟨e3, l3, o3, v3, h3⟩ := addc_spec B (cnt B d (xs.take (2 ^ d)) z p).1
      (cnt B d (xs.drop (2 ^ d)) z (cnt B d (xs.take (2 ^ d)) z p).2).1 z
      (cnt B d (xs.drop (2 ^ d)) z (cnt B d (xs.take (2 ^ d)) z p).2).2 (by rw [o1, o2])
      (fun v hv => by have := v1 v hv; omega) v2 (by have := e1.length_le; omega)
    refine ⟨e1.trans (e2.trans e3), ?_, ?_, v3, ?_⟩
    · show (addc B _ _ z _).2.length = _
      rw [l3, l2, l1, o1]; simp only [cntCost]; ring
    · show (addc B _ _ z _).1.length = _
      rw [o3, o1]
    · refine (((h1.mono (e2.trans e3)).and (h2.mono e3)).and ((hz0.mono (e1.trans e2)).mono e3)
        |>.and h3).imp ?_
      rintro σ ⟨⟨⟨h1, h2⟩, hz⟩, h3⟩
      show numVal σ (addc B _ _ z _).1 = _
      rw [h3, h1, h2, hz]
      rw [← List.sum_take_add_sum_drop (xs.map fun v => (σ v).toNat) (2 ^ d), List.map_take,
        List.map_drop]
      simp

/-! ### Comparison with a constant -/

def cmp : List ℕ → ℕ → ℕ → Bld ℕ
  | [], _, g => fun p => (g, p)
  | x :: xs, s, g => fun p =>
      cmp xs (s / 2) (B + p.length)
        (p ++ [⟨if s % 2 = 1 then (· && ·) else (· || ·), x, g⟩])

theorem cmp_arith (xb gb : Bool) (N₁ s : ℕ) :
    (if N₁ ≠ s / 2 then decide (s / 2 < N₁)
      else (if s % 2 = 1 then (· && ·) else (· || ·) : Bool → Bool → Bool) xb gb) =
    (if xb.toNat + 2 * N₁ ≠ s then decide (s < xb.toNat + 2 * N₁) else gb) := by
  have hs := Nat.div_add_mod s 2
  have hm := Nat.mod_lt s (show 2 > 0 by norm_num)
  by_cases h1 : N₁ = s / 2
  · rw [if_neg (not_not.2 h1)]
    by_cases h2 : s % 2 = 1
    · rw [if_pos h2]
      cases xb <;> cases gb <;> simp <;> omega
    · rw [if_neg h2]
      cases xb <;> cases gb <;> simp <;> omega
  · rw [if_pos h1]
    have : xb.toNat + 2 * N₁ ≠ s := by cases xb <;> simp <;> omega
    rw [if_pos this]
    cases xb <;> simp <;> omega

theorem cmp_spec : ∀ (xs : List ℕ) (s g : ℕ) (p : List Instr), s < 2 ^ xs.length →
    (∀ v ∈ xs, v < B + p.length) → g < B + p.length →
    Ext p (cmp B xs s g p).2 ∧ (cmp B xs s g p).2.length = p.length + xs.length ∧
    (cmp B xs s g p).1 < B + (cmp B xs s g p).2.length ∧
    Holds B (cmp B xs s g p).2 (fun σ => σ (cmp B xs s g p).1 =
      if numVal σ xs ≠ s then decide (s < numVal σ xs) else σ g) := by
  intro xs
  induction xs with
  | nil =>
    intro s g p hs _ hg
    simp only [List.length_nil, pow_zero] at hs
    refine ⟨Ext.refl _, by simp [cmp], by simpa [cmp] using hg, ?_⟩
    intro q inp
    simp [cmp, numVal]; omega
  | cons x xs ih =>
    intro s g p hs hx hg
    have hxv := hx x List.mem_cons_self
    set f : Bool → Bool → Bool := if s % 2 = 1 then (· && ·) else (· || ·) with hf
    have hp1 : (p ++ [(⟨f, x, g⟩ : Instr)]).length = p.length + 1 := by simp
    obtain ⟨e1, l1, o1, h1⟩ := ih (s / 2) (B + p.length) (p ++ [⟨f, x, g⟩])
      (by simp only [List.length_cons, pow_succ] at hs; omega)
      (fun v hv => by have := hx v (List.mem_cons_of_mem _ hv); rw [hp1]; omega)
      (by rw [hp1]; omega)
    have hs1 := holds_single B p ⟨f, x, g⟩ hxv hg
    refine ⟨(Ext.app _ _).trans e1, ?_, o1, ?_⟩
    · show (cmp B xs (s / 2) (B + p.length) (p ++ [⟨f, x, g⟩])).2.length = _
      rw [l1, hp1]; simp; ring
    · refine ((hs1.mono e1).and h1).imp ?_
      rintro σ ⟨hs1, h1⟩
      show σ (cmp B xs (s / 2) (B + p.length) (p ++ [⟨f, x, g⟩])).1 = _
      rw [h1, hs1]
      simp only at hs1 ⊢
      have := cmp_arith (σ x) (σ g) (numVal σ xs) s
      exact this

/-! ### Threshold -/

def thr (d : ℕ) (xs : List ℕ) (s z : ℕ) : Bld ℕ := fun p =>
  cmp B (cnt B d xs z p).1 s z (cnt B d xs z p).2

theorem thr_spec (d : ℕ) (xs : List ℕ) (s z : ℕ) (p : List Instr) (hl : xs.length = 2 ^ d)
    (hs : s < 2 ^ (d + 1)) (hx : ∀ v ∈ xs, v < B + p.length) (hz : z < B + p.length)
    (hz0 : Holds B p (fun σ => σ z = false)) :
    Ext p (thr B d xs s z p).2 ∧ (thr B d xs s z p).2.length = p.length + cntCost d + (d + 1) ∧
    (thr B d xs s z p).1 < B + (thr B d xs s z p).2.length ∧
    Holds B (thr B d xs s z p).2 (fun σ => σ (thr B d xs s z p).1 =
      decide (s < (xs.map fun v => (σ v).toNat).sum)) := by
  obtain ⟨e1, l1, o1, v1, h1⟩ := cnt_spec B d xs z p hl hx hz hz0
  obtain ⟨e2, l2, o2, h2⟩ := cmp_spec B (cnt B d xs z p).1 s z (cnt B d xs z p).2
    (by rw [o1]; exact hs) v1 (by have := e1.length_le; omega)
  refine ⟨e1.trans e2, by unfold thr; rw [l2, l1, o1], o2, ?_⟩
  refine (((h1.mono e2).and h2).and (hz0.mono (e1.trans e2))).imp ?_
  rintro σ ⟨⟨h1, h2⟩, hz⟩
  unfold thr
  rw [h2, h1, hz]
  split_ifs with h
  · rfl
  · simp only [ne_eq, Decidable.not_not] at h; simp [h]

end Build

end LTFC

-- ===== module Median =====

namespace LTFC

section Median

variable (B : ℕ)

theorem lt_of_ext {p p' : List Instr} (h : Ext p p') {v : ℕ} (hv : v < B + p.length) :
    v < B + p'.length := by
  have := h.length_le; omega

def step (k d s z : ℕ) (lt gt bs : Fin k → ℕ) : Bld (ℕ × (Fin k → ℕ) × (Fin k → ℕ)) := fun p =>
  let r1 := zipE B (fun g b => !g && !b) gt bs p
  let r2 := zipE B (· || ·) lt r1.1 r1.2
  let r3 := thr B d (List.ofFn r2.1 ++ List.replicate (2 ^ d - k) z) s z r2.2
  let r4 := emit B (fun a _ => !a) r3.1 r3.1 r3.2
  let r5 := zipE B (· && ·) r1.1 (fun _ => r4.1) r4.2
  let r6 := zipE B (· || ·) lt r5.1 r5.2
  let r7 := zipE B (fun l b => !l && b) lt bs r6.2
  let r8 := zipE B (fun v m => v && !m) r7.1 (fun _ => r4.1) r7.2
  let r9 := zipE B (· || ·) gt r8.1 r8.2
  ((r4.1, r6.1, r9.1), r9.2)

def stepCost (k d : ℕ) : ℕ := 7 * k + cntCost d + (d + 1) + 1

theorem step_spec (k d s z : ℕ) (lt gt bs : Fin k → ℕ) (p : List Instr)
    (hk : k ≤ 2 ^ d) (hs : s < 2 ^ (d + 1))
    (hlt : ∀ j, lt j < B + p.length) (hgt : ∀ j, gt j < B + p.length)
    (hbs : ∀ j, bs j < B + p.length) (hz : z < B + p.length)
    (hz0 : Holds B p (fun σ => σ z = false)) :
    Ext p (step B k d s z lt gt bs p).2 ∧
    (step B k d s z lt gt bs p).2.length = p.length + stepCost k d ∧
    (step B k d s z lt gt bs p).1.1 < B + (step B k d s z lt gt bs p).2.length ∧
    (∀ j, (step B k d s z lt gt bs p).1.2.1 j < B + (step B k d s z lt gt bs p).2.length) ∧
    (∀ j, (step B k d s z lt gt bs p).1.2.2 j < B + (step B k d s z lt gt bs p).2.length) ∧
    Holds B (step B k d s z lt gt bs p).2 (fun σ =>
      σ (step B k d s z lt gt bs p).1.1 =
        !decide (s < ∑ j, (σ (lt j) || (!σ (gt j) && !σ (bs j))).toNat) ∧
      ∀ j, σ ((step B k d s z lt gt bs p).1.2.1 j) =
          (σ (lt j) || ((!σ (gt j) && !σ (bs j)) && σ (step B k d s z lt gt bs p).1.1)) ∧
        σ ((step B k d s z lt gt bs p).1.2.2 j) =
          (σ (gt j) || ((!σ (lt j) && σ (bs j)) && !σ (step B k d s z lt gt bs p).1.1))) := by
  unfold step
  dsimp only
  obtain ⟨e1, l1, v1, h1⟩ := zipE_spec B (fun g b => !g && !b) gt bs p hgt hbs
  set r1 := zipE B (fun g b => !g && !b) gt bs p with hr1
  obtain ⟨e2, l2, v2, h2⟩ := zipE_spec B (· || ·) lt r1.1 r1.2
    (fun j => lt_of_ext B e1 (hlt j)) v1
  set r2 := zipE B (· || ·) lt r1.1 r1.2 with hr2
  have hlen3 : (List.ofFn r2.1 ++ List.replicate (2 ^ d - k) z).length = 2 ^ d := by
    simp; omega
  obtain ⟨e3, l3, v3, h3⟩ := thr_spec B d (List.ofFn r2.1 ++ List.replicate (2 ^ d - k) z) s z
    r2.2 hlen3 hs (by
      intro v hv
      rcases List.mem_append.1 hv with h | h
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 h; exact v2 j
      · rw [List.eq_of_mem_replicate h]; exact lt_of_ext B (e1.trans e2) hz)
    (lt_of_ext B (e1.trans e2) hz) (hz0.mono (e1.trans e2))
  set r3 := thr B d (List.ofFn r2.1 ++ List.replicate (2 ^ d - k) z) s z r2.2 with hr3
  obtain ⟨e4, l4, v4, h4⟩ := emit_spec B (fun a _ => !a) r3.1 r3.1 r3.2 v3 v3
  set r4 := emit B (fun a _ => !a) r3.1 r3.1 r3.2 with hr4
  obtain ⟨e5, l5, v5, h5⟩ := zipE_spec B (· && ·) r1.1 (fun _ => r4.1) r4.2
    (fun j => lt_of_ext B (e2.trans (e3.trans e4)) (v1 j)) (fun _ => v4)
  set r5 := zipE B (· && ·) r1.1 (fun _ => r4.1) r4.2 with hr5
  obtain ⟨e6, l6, v6, h6⟩ := zipE_spec B (· || ·) lt r5.1 r5.2
    (fun j => lt_of_ext B (e1.trans (e2.trans (e3.trans (e4.trans e5)))) (hlt j)) v5
  set r6 := zipE B (· || ·) lt r5.1 r5.2 with hr6
  have e16 := e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))
  obtain ⟨e7, l7, v7, h7⟩ := zipE_spec B (fun l b => !l && b) lt bs r6.2
    (fun j => lt_of_ext B e16 (hlt j)) (fun j => lt_of_ext B e16 (hbs j))
  set r7 := zipE B (fun l b => !l && b) lt bs r6.2 with hr7
  obtain ⟨e8, l8, v8, h8⟩ := zipE_spec B (fun v m => v && !m) r7.1 (fun _ => r4.1) r7.2
    v7 (fun _ => lt_of_ext B (e5.trans (e6.trans e7)) v4)
  set r8 := zipE B (fun v m => v && !m) r7.1 (fun _ => r4.1) r7.2 with hr8
  obtain ⟨e9, l9, v9, h9⟩ := zipE_spec B (· || ·) gt r8.1 r8.2
    (fun j => lt_of_ext B (e16.trans (e7.trans e8)) (hgt j)) v8
  set r9 := zipE B (· || ·) gt r8.1 r8.2 with hr9
  have e49 : Ext r4.2 r9.2 := e5.trans (e6.trans (e7.trans (e8.trans e9)))
  refine ⟨e16.trans (e7.trans (e8.trans e9)), ?_, lt_of_ext B e49 v4,
    fun j => lt_of_ext B (e7.trans (e8.trans e9)) (v6 j), v9, ?_⟩
  · rw [l9, l8, l7, l6, l5, l4, l3, l2, l1, stepCost]; ring
  · have H := (((h1.mono (e2.trans (e3.trans (e4.trans e49)))).and
      (h2.mono (e3.trans (e4.trans e49)))).and
      ((h3.mono (e4.trans e49)).and (h4.mono e49))).and
      ((((h5.mono (e6.trans (e7.trans (e8.trans e9)))).and (h6.mono (e7.trans (e8.trans e9)))).and
      ((h7.mono (e8.trans e9)).and (h8.mono e9))).and h9)
    have Hz := hz0.mono (e16.trans (e7.trans (e8.trans e9)))
    refine (H.and Hz).imp ?_
    rintro σ ⟨⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩, h9⟩, hz⟩
    refine ⟨?_, fun j => ⟨?_, ?_⟩⟩
    · have hsum : (List.map (fun v => (σ v).toNat)
          (List.ofFn r2.1 ++ List.replicate (2 ^ d - k) z)).sum =
          ∑ j, (σ (lt j) || (!σ (gt j) && !σ (bs j))).toNat := by
        simp only [List.map_append, List.map_ofFn, List.sum_append, List.sum_ofFn,
          List.map_replicate, List.sum_replicate, hz, Bool.toNat_false, smul_zero, add_zero,
          Function.comp_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [h2 j, h1 j]
      rw [h4, h3, hsum]
    · rw [h6 j, h5 j, h1 j]
    · rw [h9 j, h8 j, h7 j]

/-! ### The bit loop -/

def medLoop (k d s z : ℕ) : (Fin k → ℕ) → (Fin k → ℕ) → List (Fin k → ℕ) → Bld (List ℕ)
  | _, _, [] => fun p => ([], p)
  | lt, gt, bs :: rest => fun p =>
      let r1 := step B k d s z lt gt bs p
      let r2 := medLoop k d s z r1.1.2.1 r1.1.2.2 rest r1.2
      (r1.1.1 :: r2.1, r2.2)

def MInv {k : ℕ} (s : ℕ) (σ : ℕ → Bool) (pre : Fin k → ℕ) (P : ℕ) (lt gt : Fin k → ℕ) : Prop :=
  (∀ j, σ (lt j) = decide (pre j < P) ∧ σ (gt j) = decide (P < pre j)) ∧
  (Finset.univ.filter fun j => pre j < P).card ≤ s ∧
  s + 1 ≤ (Finset.univ.filter fun j => pre j ≤ P).card

def MFin {k : ℕ} (s : ℕ) (σ : ℕ → Bool) (pre : Fin k → ℕ) (P : ℕ) (L : List (Fin k → ℕ))
    (out : List ℕ) : Prop :=
  (Finset.univ.filter fun j => msb (pre j) (L.map fun bs => σ (bs j)) < msb P (out.map σ)).card
    ≤ s ∧
  s + 1 ≤
    (Finset.univ.filter fun j => msb (pre j) (L.map fun bs => σ (bs j)) ≤ msb P (out.map σ)).card

theorem medLoop_spec (k d s z : ℕ) (hk : k ≤ 2 ^ d) (hs : s < 2 ^ (d + 1)) :
    ∀ (L : List (Fin k → ℕ)) (lt gt : Fin k → ℕ) (p : List Instr),
    (∀ j, lt j < B + p.length) → (∀ j, gt j < B + p.length) →
    (∀ bs ∈ L, ∀ j, bs j < B + p.length) → z < B + p.length →
    Holds B p (fun σ => σ z = false) →
    Ext p (medLoop B k d s z lt gt L p).2 ∧
    (medLoop B k d s z lt gt L p).2.length = p.length + L.length * stepCost k d ∧
    (medLoop B k d s z lt gt L p).1.length = L.length ∧
    (∀ v ∈ (medLoop B k d s z lt gt L p).1, v < B + (medLoop B k d s z lt gt L p).2.length) ∧
    Holds B (medLoop B k d s z lt gt L p).2 (fun σ => ∀ pre P, MInv s σ pre P lt gt →
      MFin s σ pre P L (medLoop B k d s z lt gt L p).1) := by
  intro L
  induction L with
  | nil =>
    intro lt gt p _ _ _ _ _
    refine ⟨Ext.refl _, by simp [medLoop], by simp [medLoop], by simp [medLoop], ?_⟩
    intro q inp pre P hI
    simpa [MFin, medLoop, msb] using hI.2
  | cons bs rest ih =>
    intro lt gt p hlt hgt hbs hz hz0
    obtain ⟨e1, l1, vM, vlt, vgt, h1⟩ := step_spec B k d s z lt gt bs p hk hs hlt hgt
      (hbs bs List.mem_cons_self) hz hz0
    set r1 := step B k d s z lt gt bs p with hr1
    obtain ⟨e2, l2, o2, v2, h2⟩ := ih r1.1.2.1 r1.1.2.2 r1.2 vlt vgt
      (fun bs' hbs' j => lt_of_ext B e1 (hbs bs' (List.mem_cons_of_mem _ hbs') j))
      (lt_of_ext B e1 hz) (hz0.mono e1)
    set r2 := medLoop B k d s z r1.1.2.1 r1.1.2.2 rest r1.2 with hr2
    change Ext p r2.2 ∧ r2.2.length = p.length + (rest.length + 1) * stepCost k d ∧
      (r1.1.1 :: r2.1).length = rest.length + 1 ∧ (∀ v ∈ r1.1.1 :: r2.1, v < B + r2.2.length) ∧
      Holds B r2.2 (fun σ => ∀ pre P, MInv s σ pre P lt gt → MFin s σ pre P (bs :: rest)
        (r1.1.1 :: r2.1))
    refine ⟨e1.trans e2, by rw [l2, l1]; ring, by simp [o2], ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.1 hv with h | h
      · rw [h]; exact lt_of_ext B e2 vM
      · exact v2 v h
    · refine ((h1.mono e2).and h2).imp ?_
      rintro σ ⟨⟨hM, hj⟩, h2⟩ pre P hI
      obtain ⟨hIj, hc1, hc2⟩ := hI
      have hM' : σ r1.1.1 = !decide (s < ∑ j, (decide (pre j < P) ||
          (!decide (P < pre j) && !σ (bs j))).toNat) := by
        rw [hM]
        congr 3
        apply Finset.sum_congr rfl
        intro j _
        rw [(hIj j).1, (hIj j).2]
      obtain ⟨hst, hc1', hc2'⟩ := inv_step k s pre P (fun j => σ (bs j)) (σ r1.1.1) hc1 hc2 hM'
      have hI' : MInv s σ (fun j => 2 * pre j + (σ (bs j)).toNat) (2 * P + (σ r1.1.1).toNat)
          r1.1.2.1 r1.1.2.2 := by
        refine ⟨fun j => ⟨?_, ?_⟩, hc1', hc2'⟩
        · rw [(hj j).1, (hIj j).1, (hIj j).2]; exact (hst j).1
        · rw [(hj j).2, (hIj j).1, (hIj j).2]; exact (hst j).2
      have := h2 _ _ hI'
      simpa [MFin, msb] using this

/-! ### All coordinates -/

def medAll (k d s z : ℕ) : List (List (Fin k → ℕ)) → Bld (List (List ℕ))
  | [] => fun p => ([], p)
  | L :: Ls => fun p =>
      let r1 := medLoop B k d s z (fun _ => z) (fun _ => z) L p
      let r2 := medAll k d s z Ls r1.2
      (r1.1 :: r2.1, r2.2)

theorem medAll_spec (k d s z : ℕ) (hk : k ≤ 2 ^ d) (hs : s < 2 ^ (d + 1)) (hsk : s + 1 ≤ k) :
    ∀ (Ls : List (List (Fin k → ℕ))) (p : List Instr),
    (∀ L ∈ Ls, ∀ bs ∈ L, ∀ j, bs j < B + p.length) → z < B + p.length →
    Holds B p (fun σ => σ z = false) →
    Ext p (medAll B k d s z Ls p).2 ∧
    (medAll B k d s z Ls p).2.length = p.length + (Ls.map List.length).sum * stepCost k d ∧
    List.Forall₂ (fun L o => o.length = L.length ∧
      (∀ v ∈ o, v < B + (medAll B k d s z Ls p).2.length) ∧
      Holds B (medAll B k d s z Ls p).2 (fun σ => MFin s σ (fun _ => 0) 0 L o))
      Ls (medAll B k d s z Ls p).1 := by
  intro Ls
  induction Ls with
  | nil =>
    intro p _ _ _
    exact ⟨Ext.refl _, by simp [medAll], by simp [medAll]⟩
  | cons L Ls ih =>
    intro p hin hz hz0
    obtain ⟨e1, l1, o1, v1, h1⟩ := medLoop_spec B k d s z hk hs L (fun _ => z) (fun _ => z) p
      (fun _ => hz) (fun _ => hz) (hin L List.mem_cons_self) hz hz0
    set r1 := medLoop B k d s z (fun _ => z) (fun _ => z) L p with hr1
    obtain ⟨e2, l2, f2⟩ := ih r1.2
      (fun L' hL' bs hbs j => lt_of_ext B e1 (hin L' (List.mem_cons_of_mem _ hL') bs hbs j))
      (lt_of_ext B e1 hz) (hz0.mono e1)
    set r2 := medAll B k d s z Ls r1.2 with hr2
    change Ext p r2.2 ∧ r2.2.length = p.length + ((L :: Ls).map List.length).sum * stepCost k d ∧
      List.Forall₂ (fun L o => o.length = L.length ∧ (∀ v ∈ o, v < B + r2.2.length) ∧
        Holds B r2.2 (fun σ => MFin s σ (fun _ => 0) 0 L o)) (L :: Ls) (r1.1 :: r2.1)
    refine ⟨e1.trans e2, by rw [l2, l1]; simp; ring, List.Forall₂.cons ⟨o1, ?_, ?_⟩ f2⟩
    · intro v hv; exact lt_of_ext B e2 (v1 v hv)
    · refine ((h1.mono e2).and (hz0.mono (e1.trans e2))).imp ?_
      rintro σ ⟨h1, hz⟩
      apply h1
      refine ⟨fun j => ⟨by simp [hz], by simp [hz]⟩, by simp, by simpa using hsk⟩

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

def zeroI : Instr := ⟨fun _ _ => false, 0, 0⟩

theorem zero_holds (B : ℕ) : Holds B [zeroI] (fun σ => σ B = false) := by
  intro q inp
  by_cases h : 0 < B
  · have := sval_at B ([zeroI] ++ q) inp 0 (by simp) (by simp [zeroI]; omega)
      (by simp [zeroI]; omega)
    simpa [zeroI] using this
  · have := sval_at_invalid B ([zeroI] ++ q) inp 0 (by simp) (by simp [zeroI]; omega)
    simpa using this

section Prog

variable (k m n ℓo : ℕ) (oa : Fin n → (Fin ℓo ↪ Fin m))

def theD : ℕ := Nat.log 2 k + 1

def Lsof : List (List (Fin k → ℕ)) :=
  List.ofFn (fun i : Fin n => List.ofFn (fun t : Fin ℓo => fun j : Fin k => j.val * m + (oa i t).val))

def medRes : List (List ℕ) × List Instr :=
  medAll (k * m) k (theD k) (k / 2) (k * m) (Lsof k m n ℓo oa) [zeroI]

def srcIdx (q : ℕ) : ℕ := (((medRes k m n ℓo oa).1.getD (q / ℓo) []).getD (q % ℓo) 0)

def prog : List Instr :=
  (medRes k m n ℓo oa).2 ++
    List.ofFn (fun q : Fin (n * ℓo) =>
      (⟨fun a _ => a, srcIdx k m n ℓo oa q, srcIdx k m n ℓo oa q⟩ : Instr))

def outIdx (i : Fin n) (t : Fin ℓo) : ℕ :=
  k * m + (medRes k m n ℓo oa).2.length + (i.val * ℓo + t.val)

theorem theD_spec (hk : 1 ≤ k) : k < 2 ^ theD k ∧ 2 ^ theD k ≤ 2 * k := by
  unfold theD
  refine ⟨Nat.lt_pow_succ_log_self (by norm_num) k, ?_⟩
  rw [pow_succ]
  have := Nat.pow_log_le_self 2 (show k ≠ 0 by omega)
  omega

theorem medRes_spec (hk : 1 ≤ k) :
    Ext [zeroI] (medRes k m n ℓo oa).2 ∧
    (medRes k m n ℓo oa).2.length = 1 + n * ℓo * stepCost k (theD k) ∧
    List.Forall₂ (fun L o => o.length = L.length ∧
      (∀ v ∈ o, v < k * m + (medRes k m n ℓo oa).2.length) ∧
      Holds (k * m) (medRes k m n ℓo oa).2
        (fun σ => MFin (k / 2) σ (fun _ => 0) 0 L o))
      (Lsof k m n ℓo oa) (medRes k m n ℓo oa).1 := by
  have hd := theD_spec k hk
  obtain ⟨e, l, f⟩ := medAll_spec (k * m) k (theD k) (k / 2) (k * m) (by omega)
    (by rw [pow_succ]; omega) (by omega) (Lsof k m n ℓo oa) [zeroI]
    (by
      intro L hL bs hbs j
      simp only [Lsof, List.mem_ofFn] at hL
      obtain ⟨i, rfl⟩ := hL
      simp only [List.mem_ofFn] at hbs
      obtain ⟨t, rfl⟩ := hbs
      simp only [List.length_singleton]
      have h1 := (oa i t).isLt
      have h2 := j.isLt
      have : (j.val + 1) * m ≤ k * m := Nat.mul_le_mul_right m (by omega)
      rw [Nat.add_mul, one_mul] at this
      omega)
    (by simp) (zero_holds _)
  refine ⟨e, ?_, f⟩
  rw [medRes, l]
  simp [Lsof, List.map_ofFn, Function.comp_def, List.sum_ofFn]

theorem prog_length (hk : 1 ≤ k) :
    (prog k m n ℓo oa).length = 1 + n * ℓo * stepCost k (theD k) + n * ℓo := by
  rw [prog, List.length_append, (medRes_spec k m n ℓo oa hk).2.1, List.length_ofFn]

theorem prog_spec (hk : 1 ≤ k) (inp : ℕ → Bool) (i : Fin n) :
    (Finset.univ.filter fun j : Fin k =>
      bitsToNat (fun t : Fin ℓo => inp (j.val * m + (oa i t).val)) <
      bitsToNat (fun t : Fin ℓo => sval (k * m) (prog k m n ℓo oa) inp (outIdx k m n ℓo oa i t))).card
      ≤ k / 2 ∧
    k / 2 + 1 ≤ (Finset.univ.filter fun j : Fin k =>
      bitsToNat (fun t : Fin ℓo => inp (j.val * m + (oa i t).val)) ≤
      bitsToNat (fun t : Fin ℓo =>
        sval (k * m) (prog k m n ℓo oa) inp (outIdx k m n ℓo oa i t))).card := by
  obtain ⟨e, _, f⟩ := medRes_spec k m n ℓo oa hk
  have hlen := e.length_le
  simp only [List.length_singleton] at hlen
  set R := medRes k m n ℓo oa with hR
  have hf := List.forall₂_iff_get.1 f
  have hLs : (Lsof k m n ℓo oa).length = n := by simp [Lsof]
  have hi1 : i.val < (Lsof k m n ℓo oa).length := by rw [hLs]; exact i.isLt
  have hi2 : i.val < R.1.length := by rw [← hf.1]; exact hi1
  obtain ⟨ho, hv, hh⟩ := hf.2 i.val hi1 hi2
  have hget : (Lsof k m n ℓo oa).get ⟨i.val, hi1⟩ =
      List.ofFn (fun t : Fin ℓo => fun j : Fin k => j.val * m + (oa i t).val) := by
    simp [Lsof]
  rw [hget] at ho hh
  simp only [List.length_ofFn] at ho
  set o := R.1.get ⟨i.val, hi2⟩ with hodef
  set σ := sval (k * m) (prog k m n ℓo oa) inp with hσ
  have hM := hh ((List.ofFn (fun q : Fin (n * ℓo) =>
      (⟨fun a _ => a, srcIdx k m n ℓo oa q, srcIdx k m n ℓo oa q⟩ : Instr)))) inp
  -- copy block
  have hcopy := holds_block (k * m) R.2 (fun q : Fin (n * ℓo) =>
      (⟨fun a _ => a, srcIdx k m n ℓo oa q, srcIdx k m n ℓo oa q⟩ : Instr)) (by
    intro q
    have : srcIdx k m n ℓo oa q < k * m + R.2.length := by
      unfold srcIdx
      rw [← hR]
      rw [List.getD_eq_getElem?_getD]
      cases h : (R.1.getD (q / ℓo) [])[q % ℓo]? with
      | none => simp; omega
      | some v =>
        simp only [Option.getD_some]
        have hmem : v ∈ R.1.getD (q / ℓo) [] := List.mem_of_getElem? h
        rw [List.getD_eq_getElem?_getD] at hmem
        cases h2 : R.1[q / ℓo]? with
        | none => rw [h2] at hmem; simp at hmem
        | some o' =>
          rw [h2] at hmem
          simp only [Option.getD_some] at hmem
          obtain ⟨hidx, hget2⟩ := List.getElem?_eq_some_iff.1 h2
          have hidx' : q / ℓo < (Lsof k m n ℓo oa).length := by rw [hf.1]; exact hidx
          exact (hf.2 (q / ℓo) hidx' hidx).2.1 v (by rw [List.get_eq_getElem, hget2]; exact hmem)
    exact ⟨this, this⟩) [] inp
  simp only [List.append_nil] at hcopy
  have hσo : ∀ t : Fin ℓo, σ (outIdx k m n ℓo oa i t) = σ (o.get ⟨t.val, by rw [ho]; exact t.isLt⟩) := by
    intro t
    have hq : i.val * ℓo + t.val < n * ℓo := by
      have := i.isLt
      have : (i.val + 1) * ℓo ≤ n * ℓo := Nat.mul_le_mul_right ℓo (by omega)
      rw [Nat.add_mul, one_mul] at this
      have := t.isLt
      omega
    have := hcopy ⟨i.val * ℓo + t.val, hq⟩
    simp only at this
    rw [hσ, prog, outIdx, ← hR, this]
    congr 1
    unfold srcIdx
    rw [← hR]
    have ht := t.isLt
    have e1 : (i.val * ℓo + t.val) / ℓo = i.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, zero_add]
    have e2 : (i.val * ℓo + t.val) % ℓo = t.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
    have hgo : R.1.getD i.val [] = o := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]; rfl
    have hto : t.val < o.length := by rw [ho]; exact ht
    rw [e1, e2, hgo, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hto, Option.getD_some]
    rfl
  have hmapo : o.map σ = List.ofFn (fun t : Fin ℓo => σ (outIdx k m n ℓo oa i t)) := by
    apply List.ext_get
    · simp [ho]
    · intro t h1 h2
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_ofFn]
      rw [hσo ⟨t, by simpa using h2⟩]
      rfl
  have hmapL : ∀ j : Fin k, (List.ofFn (fun t : Fin ℓo => fun j : Fin k => j.val * m + (oa i t).val)).map
      (fun bs => σ (bs j)) = List.ofFn (fun t : Fin ℓo => inp (j.val * m + (oa i t).val)) := by
    intro j
    rw [List.map_ofFn]
    congr 1
    funext t
    simp only [Function.comp_apply]
    rw [hσ, sval_lt]
    have h1 := (oa i t).isLt
    have h2 := j.isLt
    have : (j.val + 1) * m ≤ k * m := Nat.mul_le_mul_right m (by omega)
    rw [Nat.add_mul, one_mul] at this
    omega
  have hM' : MFin (k / 2) σ (fun _ => 0) 0
      (List.ofFn (fun t : Fin ℓo => fun j : Fin k => j.val * m + (oa i t).val)) o := hM
  unfold MFin at hM'
  simp only [hmapL, hmapo, msb_ofFn] at hM'
  exact hM'

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

/-- Permutation circuits: the outcome distribution is pushed forward. -/
theorem perm_prob {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (F : Qubits n → Qubits n)
    (hF : Function.Injective F) (hU : ∀ z, U.mulVec (bv z) = bv (F z)) (φ : Qubits n → ℂ)
    (E : Qubits n → Prop) [DecidablePred E] :
    ∑ y ∈ Finset.univ.filter E, ‖(U.mulVec φ) y‖ ^ 2 =
      ∑ z ∈ Finset.univ.filter (fun z => E (F z)), ‖φ z‖ ^ 2 := by
  have hφ : φ = ∑ z, φ z • bv z := by
    funext y; simp [bv, Finset.sum_apply, Pi.single_apply]
  have hUφ : ∀ z, (U.mulVec φ) (F z) = φ z := by
    intro z
    conv_lhs => rw [hφ]
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hU, Finset.sum_apply, Pi.smul_apply, bv, Pi.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single z]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (hF h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  have hbij := hF.bijective_of_finite
  let e := Equiv.ofBijective F hbij
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro z _
  simp only [e, Equiv.ofBijective_apply, hUφ]

/-! ### Repeated copies -/

section Copies

variable {r : ℕ} {ar : Fin r → ℕ}

def embJ (m M j : ℕ) (h : (j + 1) * m ≤ M) : Fin m ↪ Fin M :=
  ⟨fun u => ⟨j * m + u, by have := u.isLt; rw [Nat.add_mul, one_mul] at h; omega⟩, by
    intro u v huv; simp at huv; exact Fin.ext huv⟩

@[simp] theorem embJ_val (m M j : ℕ) (h : (j + 1) * m ≤ M) (u : Fin m) :
    (embJ m M j h u).val = j * m + u.val := rfl

def copies {m : ℕ} (c₀ : OracleCircuit G12 ar m) (M : ℕ) :
    (J : ℕ) → J * m ≤ M → OracleCircuit G12 ar M
  | 0, _ => []
  | J + 1, h => copies c₀ M J (le_trans (Nat.mul_le_mul_right m (Nat.le_succ J)) h) ++
      relabel c₀ (embJ m M J h)

def blk {m M : ℕ} (y : Qubits M) (j : ℕ) : Qubits m :=
  fun u => if h : j * m + u.val < M then y ⟨j * m + u.val, h⟩ else false

noncomputable def Phi {m M : ℕ} (U₀ : Matrix (Qubits m) (Qubits m) ℂ) (J : ℕ) (y : Qubits M) : ℂ :=
  (∏ j ∈ Finset.range J, U₀ (blk y j) (fun _ => false)) *
    (if ∀ v : Fin M, J * m ≤ v.val → y v = false then 1 else 0)

theorem comp_embJ {m M j : ℕ} (h : (j + 1) * m ≤ M) (y : Qubits M) :
    y ∘ (embJ m M j h) = blk y j := by
  funext u
  have hu : j * m + u.val < M := by have := u.isLt; rw [Nat.add_mul, one_mul] at h; omega
  simp only [Function.comp_apply, blk, dif_pos hu]
  rfl

theorem copies_state {m : ℕ} (c₀ : OracleCircuit G12 ar m) (hc : QuantumLTF.Membership.Uncontrolled c₀)
    (M : ℕ) (orc : (k : Fin r) → Matrix (Qubits (ar k)) (Qubits (ar k)) ℂ) :
    ∀ (J : ℕ) (hJ : J * m ≤ M),
      ((copies c₀ M J hJ).unitary orc).mulVec (bv (fun _ => false)) =
        Phi (c₀.unitary orc) J := by
  intro J
  induction J with
  | zero =>
    intro hJ
    funext y
    simp only [copies, unitary_nil, Matrix.one_mulVec, Phi, Finset.range_zero,
      Finset.prod_empty, one_mul, zero_mul, Nat.zero_mul, zero_le, true_implies, bv,
      Pi.single_apply]
    by_cases hy : y = fun _ => false
    · subst hy; simp
    · rw [if_neg hy, if_neg]; intro h; exact hy (funext h)
  | succ J ih =>
    intro hJ
    have hJ' : J * m ≤ M := le_trans (Nat.mul_le_mul_right m (Nat.le_succ J)) hJ
    rw [copies, unitary_append, ← Matrix.mulVec_mulVec, ih hJ', relabel_unitary _ _ hc]
    set e := embJ m M J hJ with he
    set U₀ := c₀.unitary orc with hU₀
    funext y
    rw [Matrix.mulVec, dotProduct]
    have hrange : ∀ v : Fin M, v ∈ Set.range e ↔ J * m ≤ v.val ∧ v.val < (J + 1) * m := by
      intro v
      constructor
      · rintro ⟨u, rfl⟩
        rw [he, embJ_val]
        have := u.isLt; rw [Nat.add_mul, one_mul]; omega
      · rintro ⟨h1, h2⟩
        refine ⟨⟨v.val - J * m, by rw [Nat.add_mul, one_mul] at h2; omega⟩, ?_⟩
        apply Fin.ext
        rw [he, embJ_val]
        simp only
        omega
    set z₀ := setPart y e (fun _ => false) with hz₀
    rw [Finset.sum_eq_single z₀]
    · rw [embedOp_of_agree _ e (agreeOff_symm (agreeOff_setPart y e _)), hz₀, setPart_comp,
        comp_embJ]
      unfold Phi
      rw [Finset.prod_range_succ]
      have hprod : ∏ j ∈ Finset.range J, U₀ (blk (setPart y e (fun _ => false)) j) (fun _ => false)
          = ∏ j ∈ Finset.range J, U₀ (blk y j) (fun _ => false) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        congr 1
        funext u
        simp only [blk]
        split_ifs with hu
        · apply setPart_off
          rw [hrange]
          simp only
          intro ⟨h1, _⟩
          have : (j + 1) * m ≤ J * m := Nat.mul_le_mul_right m hj
          rw [Nat.add_mul, one_mul] at this
          have := u.isLt
          omega
        · rfl
      rw [hprod]
      have hind : (∀ v : Fin M, J * m ≤ v.val → setPart y e (fun _ => false) v = false) ↔
          (∀ v : Fin M, (J + 1) * m ≤ v.val → y v = false) := by
        constructor
        · intro h v hv
          have hv' : v ∉ Set.range e := by rw [hrange]; omega
          rw [← setPart_off y e (fun _ => false) hv']
          exact h v (by rw [Nat.add_mul, one_mul] at hv; omega)
        · intro h v hv
          by_cases hv' : v ∈ Set.range e
          · obtain ⟨u, rfl⟩ := hv'
            rw [setPart_emb]
          · rw [setPart_off y e _ hv']
            rw [hrange] at hv'
            exact h v (by omega)
      rw [if_congr hind rfl rfl]
      ring
    · intro z _ hz
      by_cases hag : AgreeOff e y z
      · have hne : ¬ ∀ v : Fin M, J * m ≤ v.val → z v = false := by
          intro hall
          apply hz
          rw [hz₀, eq_setPart_iff]
          refine ⟨?_, agreeOff_symm hag⟩
          funext u
          simp only [Function.comp_apply]
          apply hall
          have := (hrange (e u)).1 ⟨u, rfl⟩
          exact this.1
        unfold Phi
        rw [if_neg hne, mul_zero, mul_zero]
      · rw [embedOp_of_not_agree _ e hag, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

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

theorem runP_injective (M : ℕ) (P : List Instr) (pos : ℕ) : Function.Injective (runP M P pos) := by
  induction P generalizing pos with
  | nil => exact Function.injective_id
  | cons g gs ih =>
    exact (ih (pos + 1)).comp (Function.LeftInverse.injective (stepF_invol M g pos))

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

theorem copies_counts {m : ℕ} (c₀ : OracleCircuit G12 ar m) (M : ℕ) (k : Fin r) :
    ∀ (J : ℕ) (hJ : J * m ≤ M),
      (copies c₀ M J hJ).queryCount k = J * c₀.queryCount k ∧
      (copies c₀ M J hJ).gateCount = J * c₀.gateCount ∧
      QuantumLTF.Membership.Uncontrolled (copies c₀ M J hJ) := by
  intro J
  induction J with
  | zero => intro hJ; refine ⟨by simp [copies, OracleCircuit.queryCount],
      by simp [copies, OracleCircuit.gateCount], fun st hst => by simp [copies] at hst⟩
  | succ J ih =>
    intro hJ
    obtain ⟨h1, h2, h3⟩ := ih (le_trans (Nat.mul_le_mul_right m (Nat.le_succ J)) hJ)
    refine ⟨?_, ?_, ?_⟩
    · rw [copies, queryCount_append, h1, relabel_queryCount]; ring
    · rw [copies, gateCount_append, h2, relabel_gateCount]; ring
    · exact uncontrolled_append h3 (relabel_uncontrolled _ _)

end Counts

/-! ### Spreading `k` blocks into a register -/

theorem pos_of_lt_mul {k m v : ℕ} (h : v < k * m) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · simp [h0] at h
  · exact h0

def spread (k m M : ℕ) (x : Fin k → Qubits m) : Qubits M := fun v =>
  if h : v.val < k * m then
    x ⟨v.val / m, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h)⟩
      ⟨v.val % m, Nat.mod_lt _ (pos_of_lt_mul h)⟩
  else false

theorem jm_lt {k m : ℕ} (j : Fin k) (u : Fin m) : j.val * m + u.val < k * m := by
  have h1 := j.isLt
  have h2 := u.isLt
  have : (j.val + 1) * m ≤ k * m := Nat.mul_le_mul_right m h1
  rw [Nat.add_mul, one_mul] at this
  omega

theorem spread_apply {k m M : ℕ} (x : Fin k → Qubits m) (j : Fin k) (u : Fin m)
    (h : j.val * m + u.val < M) : spread k m M x ⟨j.val * m + u.val, h⟩ = x j u := by
  unfold spread
  have hm : 0 < m := pos_of_lt_mul (jm_lt j u)
  rw [dif_pos (jm_lt j u)]
  have e1 : (j.val * m + u.val) / m = j.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt u.isLt, zero_add]
  have e2 : (j.val * m + u.val) % m = u.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt u.isLt]
  congr 1
  · exact Fin.ext e1
  · exact Fin.ext e2

theorem spread_injective (k m M : ℕ) (hM : k * m ≤ M) : Function.Injective (spread k m M) := by
  intro x y hxy
  funext j u
  have h := jm_lt j u
  rw [← spread_apply (M := M) x j u (by omega), ← spread_apply (M := M) y j u (by omega), hxy]

theorem spread_high {k m M : ℕ} (x : Fin k → Qubits m) (v : Fin M) (hv : k * m ≤ v.val) :
    spread k m M x v = false := by
  unfold spread; rw [dif_neg (by omega)]

theorem blk_spread {k m M : ℕ} (hM : k * m ≤ M) (x : Fin k → Qubits m) (j : Fin k) :
    blk (spread k m M x) j.val = x j := by
  funext u
  have h := jm_lt j u
  unfold blk
  rw [dif_pos (by omega), spread_apply]

theorem toN_spread {k m M : ℕ} (hM : k * m ≤ M) (x : Fin k → Qubits m) (j : Fin k) (u : Fin m) :
    toN (spread k m M x) (j.val * m + u.val) = x j u := by
  have h := jm_lt j u
  unfold toN
  rw [dif_pos (by omega), spread_apply]

theorem Phi_spread {k m M : ℕ} (hM : k * m ≤ M) (U₀ : Matrix (Qubits m) (Qubits m) ℂ)
    (x : Fin k → Qubits m) :
    Phi U₀ k (spread k m M x) = ∏ j : Fin k, U₀ (x j) (fun _ => false) := by
  unfold Phi
  rw [if_pos (fun v hv => spread_high x v hv), mul_one]
  rw [← Fin.prod_univ_eq_prod_range (fun j => U₀ (blk (spread k m M x) j) (fun _ => false)) k]
  apply Finset.prod_congr rfl
  intro j _
  rw [blk_spread hM]

/-! ### The amplified circuit -/

section Amp

variable (a k m n ℓo : ℕ) (oa : Fin n → (Fin ℓo ↪ Fin m))

abbrev Mreg : ℕ := k * m + (prog k m n ℓo oa).length

noncomputable def ampCirc (c₀ : OracleCircuit G12 (fun _ : Fin 1 => a) m) :
    OracleCircuit G12 (fun _ : Fin 1 => a) (Mreg k m n ℓo oa) :=
  copies c₀ (Mreg k m n ℓo oa) k (by simp) ++
    compileAux (Mreg k m n ℓo oa) (prog k m n ℓo oa) (k * m)

theorem outIdx_lt (hk : 1 ≤ k) (i : Fin n) (t : Fin ℓo) :
    outIdx k m n ℓo oa i t < Mreg k m n ℓo oa := by
  unfold outIdx Mreg
  rw [prog, List.length_append, List.length_ofFn]
  have h1 := i.isLt
  have h2 := t.isLt
  have : (i.val + 1) * ℓo ≤ n * ℓo := Nat.mul_le_mul_right ℓo h1
  rw [Nat.add_mul, one_mul] at this
  omega

def outE (hk : 1 ≤ k) (i : Fin n) : Fin ℓo ↪ Fin (Mreg k m n ℓo oa) :=
  ⟨fun t => ⟨outIdx k m n ℓo oa i t, outIdx_lt k m n ℓo oa hk i t⟩, by
    intro t t' h
    simp only [Fin.mk.injEq, outIdx] at h
    exact Fin.ext (by omega)⟩

theorem fpVal_eq (ℓ f : ℕ) (b : Qubits ℓ) :
    QuantumLTF.Membership.fpVal ℓ f b = ((bitsToNat b : ℝ) - (2 : ℝ) ^ ℓ / 2) / (2 : ℝ) ^ f := rfl

theorem fp_strictMono (ℓ f : ℕ) :
    StrictMono (fun N : ℕ => ((N : ℝ) - (2 : ℝ) ^ ℓ / 2) / (2 : ℝ) ^ f) := by
  intro x y hxy
  simp only
  apply div_lt_div_of_pos_right _ (by positivity)
  have : (x : ℝ) < y := by exact_mod_cast hxy
  linarith

theorem amp_prob (s : ℕ) (hks : k = 2 * s + 1) (fo : ℕ)
    (c₀ : OracleCircuit G12 (fun _ : Fin 1 => a) m) (hc : QuantumLTF.Membership.Uncontrolled c₀)
    (OH : Matrix (Qubits a) (Qubits a) ℂ) (hOH : OH ∈ Matrix.unitaryGroup (Qubits a) ℂ)
    (g : Fin n → ℝ) (δ : ℝ)
    (G : Qubits m → Prop) [DecidablePred G]
    (hGdef : ∀ z, G z ↔ ∀ i, |QuantumLTF.Membership.readFp (oa i) fo z - g i| ≤ δ)
    (hyp : (3 / 4 : ℝ) ≤ probEvent (act (c₀.unitary fun _ => OH) (zeroKet m)) G)
    (E : Qubits (Mreg k m n ℓo oa) → Prop) [DecidablePred E]
    (hEdef : ∀ z, E z ↔ ∀ i, |QuantumLTF.Membership.readFp
      (outE k m n ℓo oa (by omega) i) fo z - g i| ≤ δ) :
    1 - (7 / 8 : ℝ) ^ k ≤
      probEvent (act ((ampCirc a k m n ℓo oa c₀).unitary fun _ => OH)
        (zeroKet (Mreg k m n ℓo oa))) E := by
  have hk1 : 1 ≤ k := by omega
  have hBM : k * m ≤ Mreg k m n ℓo oa := by simp
  set orc : (j : Fin 1) → Matrix (Qubits ((fun _ : Fin 1 => a) j))
    (Qubits ((fun _ : Fin 1 => a) j)) ℂ := fun _ => OH with horc
  set U₀ := c₀.unitary orc with hU₀
  have hU₀u : U₀ ∈ Matrix.unitaryGroup (Qubits m) ℂ := circuit_unitary c₀ hc orc (fun _ => hOH)
  set p : Qubits m → ℝ := fun u => ‖U₀ u (fun _ => false)‖ ^ 2 with hp
  have hsum : ∑ u, p u = 1 := colsum_one hU₀u _
  have hG : 3 / 4 ≤ ∑ u ∈ Finset.univ.filter G, p u := by
    rw [probEvent_zero] at hyp
    simpa [hp, hU₀, Matrix.mulVec_single_one, bv] using hyp
  have htail := tail_bound k p (fun _ => sq_nonneg _) hsum G hG
  set P := prog k m n ℓo oa with hP
  set F := runP (Mreg k m n ℓo oa) P (k * m) with hF
  have hFinj : Function.Injective F := runP_injective _ _ _
  have himpl := impl_compile (ar := fun _ : Fin 1 => a) (Mreg k m n ℓo oa) P (k * m)
  rw [probEvent_zero, ampCirc, unitary_append, ← Matrix.mulVec_mulVec,
    copies_state c₀ hc (Mreg k m n ℓo oa) orc k hBM]
  rw [perm_prob _ F hFinj (himpl orc) (Phi U₀ k) E]
  have hs2 : k / 2 = s := by omega
  -- majority implies the event
  have hmaj : ∀ x : Fin k → Qubits m, k < 2 * (Finset.univ.filter fun j => G (x j)).card →
      E (F (spread k m (Mreg k m n ℓo oa) x)) := by
    intro x hx
    rw [hEdef]
    intro i
    set inp := toN (spread k m (Mreg k m n ℓo oa) x) with hinp
    have hspec := prog_spec k m n ℓo oa hk1 inp i
    rw [hs2] at hspec
    have hcomp : ∀ t : Fin ℓo, F (spread k m (Mreg k m n ℓo oa) x) (outE k m n ℓo oa (by omega) i t) =
        sval (k * m) P inp (outIdx k m n ℓo oa i t) := by
      intro t
      exact compile_sem (Mreg k m n ℓo oa) (k * m) P le_rfl (spread k m (Mreg k m n ℓo oa) x)
        (fun v hv => spread_high x v hv) _
    have hinpx : ∀ (j : Fin k) (t : Fin ℓo), inp (j.val * m + (oa i t).val) = x j (oa i t) :=
      fun j t => toN_spread hBM x j (oa i t)
    unfold QuantumLTF.Membership.readFp
    rw [fpVal_eq]
    have hout : (F (spread k m (Mreg k m n ℓo oa) x) ∘ (outE k m n ℓo oa (by omega) i)) =
        fun t => sval (k * m) P inp (outIdx k m n ℓo oa i t) := funext hcomp
    rw [hout]
    refine median_close k s hks
      (fun j => bitsToNat (fun t : Fin ℓo => inp (j.val * m + (oa i t).val)))
      (bitsToNat (fun t : Fin ℓo => sval (k * m) P inp (outIdx k m n ℓo oa i t)))
      (fun N : ℕ => ((N : ℝ) - (2 : ℝ) ^ ℓo / 2) / (2 : ℝ) ^ fo) (fp_strictMono ℓo fo) (g i) δ
      (Finset.univ.filter fun j => G (x j)) ?_ (by omega) hspec.1 hspec.2
    intro j hj
    rw [Finset.mem_filter] at hj
    have := (hGdef (x j)).1 hj.2 i
    unfold QuantumLTF.Membership.readFp at this
    rw [fpVal_eq] at this
    simp only [hinpx]
    exact this
  calc 1 - (7 / 8 : ℝ) ^ k
      ≤ ∑ x : Fin k → Qubits m, (∏ j, p (x j)) *
          (if k < 2 * (Finset.univ.filter fun j => G (x j)).card then 1 else 0) := htail
    _ ≤ ∑ x : Fin k → Qubits m,
          (if E (F (spread k m (Mreg k m n ℓo oa) x)) then ‖Phi U₀ k (spread k m (Mreg k m n ℓo oa) x)‖ ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro x _
        split_ifs with h1 h2
        · rw [mul_one, Phi_spread hBM, norm_prod, Finset.prod_pow]
        · exact absurd (hmaj x h1) h2
        · rw [mul_zero]; positivity
        · rw [mul_zero]
    _ = ∑ z ∈ Finset.univ.image (spread k m (Mreg k m n ℓo oa)),
          (if E (F z) then ‖Phi U₀ k z‖ ^ 2 else 0) := by
        rw [Finset.sum_image (fun x _ y _ h => spread_injective k m (Mreg k m n ℓo oa) hBM h)]
    _ ≤ ∑ z, (if E (F z) then ‖Phi U₀ k z‖ ^ 2 else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro z _ _
        split_ifs <;> positivity
    _ = ∑ z ∈ Finset.univ.filter (fun z => E (F z)), ‖Phi U₀ k z‖ ^ 2 := by
        rw [Finset.sum_filter]

theorem amp_counts (c₀ : OracleCircuit G12 (fun _ : Fin 1 => a) m)
    (hc : QuantumLTF.Membership.Uncontrolled c₀) :
    QuantumLTF.Membership.Uncontrolled (ampCirc a k m n ℓo oa c₀) ∧
    (ampCirc a k m n ℓo oa c₀).queryCount 0 = k * c₀.queryCount 0 ∧
    (ampCirc a k m n ℓo oa c₀).gateCount ≤ k * c₀.gateCount + 10 * (prog k m n ℓo oa).length := by
  obtain ⟨h1, h2, h3⟩ := copies_counts c₀ (Mreg k m n ℓo oa) 0 k (by simp)
  have hall := allGates_compile (ar := fun _ : Fin 1 => a) (Mreg k m n ℓo oa)
    (prog k m n ℓo oa) (k * m)
  refine ⟨uncontrolled_append h3 hall.uncontrolled, ?_, ?_⟩
  · rw [ampCirc, queryCount_append, h1, hall.queryCount]; ring
  · rw [ampCirc, gateCount_append, h2, hall.gateCount]
    have := length_compile (ar := fun _ : Fin 1 => a) (Mreg k m n ℓo oa) (prog k m n ℓo oa) (k * m)
    omega

theorem prog_length_le (hk : 1 ≤ k) :
    (prog k m n ℓo oa).length ≤ 28 * k * (n * ℓo + 1) := by
  rw [prog_length k m n ℓo oa hk]
  have hd := theD_spec k hk
  have hc := cntCost_le (theD k)
  have hstep : stepCost k (theD k) ≤ 27 * k := by
    unfold stepCost
    rw [pow_succ] at hc
    omega
  have : n * ℓo * stepCost k (theD k) ≤ n * ℓo * (27 * k) := Nat.mul_le_mul_left _ hstep
  have e : 28 * k * (n * ℓo + 1) = 27 * (k * (n * ℓo)) + k * (n * ℓo) + 28 * k := by ring
  have e2 : n * ℓo * (27 * k) = 27 * (k * (n * ℓo)) := by ring
  have h2 : n * ℓo ≤ k * (n * ℓo) := Nat.le_mul_of_pos_left _ (by omega)
  omega

end Amp

end LTFC

-- ===== module Final1 =====

open QAlgorithms

namespace LTFC

theorem pow78_le (γ : ℝ) (hγ0 : 0 < γ) (k : ℕ) (hk : 8 * Real.log (1 / γ) ≤ k) :
    (7 / 8 : ℝ) ^ k ≤ γ := by
  have h1 : Real.log (7 / 8) ≤ -(1 / 8) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num)
    linarith
  have h2 : Real.log ((7 / 8 : ℝ) ^ k) ≤ Real.log γ := by
    rw [Real.log_pow]
    have hL : Real.log (1 / γ) = - Real.log γ := by rw [one_div, Real.log_inv]
    rw [hL] at hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  exact (Real.log_le_log_iff (by positivity) hγ0).1 h2

end LTFC

open LTFC in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n a m ℓo fo : ℕ)
      (c₀ : OracleCircuit QuantumLTF.Membership.gates12 (fun _ : Fin 1 => a) m)
      (oa : Fin n → (Fin ℓo ↪ Fin m)), QuantumLTF.Membership.Uncontrolled c₀ →
      ∀ γ : ℝ, 0 < γ → γ ≤ 1 / 2 →
      ∃ (m' : ℕ) (c : OracleCircuit QuantumLTF.Membership.gates12 (fun _ : Fin 1 => a) m')
        (out : Fin n → (Fin ℓo ↪ Fin m')),
        QuantumLTF.Membership.Uncontrolled c ∧
        (c.queryCount 0 : ℝ) ≤ C * (c₀.queryCount 0 + 1) * Real.log (1 / γ) ∧
        (c.gateCount : ℝ) ≤ C * (c₀.gateCount + n * ℓo + 1) * Real.log (1 / γ) ∧
        ∀ OH : Matrix (Qubits a) (Qubits a) ℂ,
          OH ∈ Matrix.unitaryGroup (Qubits a) ℂ →
          ∀ (g : Fin n → ℝ) (δ : ℝ),
            (3 / 4 : ℝ) ≤ probEvent (act (c₀.unitary fun _ => OH) (zeroKet m))
              (fun z => ∀ i, |QuantumLTF.Membership.readFp (oa i) fo z - g i| ≤ δ) →
            open Classical in
            probEvent (act (c.unitary fun _ => OH) (zeroKet m'))
              (fun z => ∀ i, |QuantumLTF.Membership.readFp (out i) fo z - g i| ≤ δ) ≥ 1 - γ := by
  refine ⟨4000, by norm_num, ?_⟩
  intro n a m ℓo fo c₀ oa hc γ hγ0 hγ1
  set L := Real.log (1 / γ) with hLdef
  have hL : Real.log 2 ≤ L := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hγ0]; linarith
  have hL0 : (0.69 : ℝ) < L := by have := Real.log_two_gt_d9; linarith
  set s := ⌈4 * L⌉₊ with hs
  set k := 2 * s + 1 with hk
  have hs1 : 4 * L ≤ (s : ℝ) := Nat.le_ceil _
  have hs2 : (s : ℝ) < 4 * L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hkR : (k : ℝ) = 2 * s + 1 := by rw [hk]; push_cast; ring
  have hk13 : (k : ℝ) ≤ 13 * L := by rw [hkR]; linarith
  have hk8 : 8 * L ≤ (k : ℝ) := by rw [hkR]; linarith
  refine ⟨Mreg k m n ℓo oa, ampCirc a k m n ℓo oa c₀, outE k m n ℓo oa (by omega), ?_⟩
  obtain ⟨hu, hq, hg⟩ := amp_counts a k m n ℓo oa c₀ hc
  have hP := prog_length_le k m n ℓo oa (by omega)
  refine ⟨hu, ?_, ?_, ?_⟩
  · rw [hq]
    push_cast
    have hq0 : (0 : ℝ) ≤ (c₀.queryCount 0 : ℝ) := Nat.cast_nonneg _
    nlinarith
  · have hgN : (ampCirc a k m n ℓo oa c₀).gateCount ≤ 280 * k * (c₀.gateCount + n * ℓo + 1) := by
      have e : 280 * k * (c₀.gateCount + n * ℓo + 1) =
          280 * (k * c₀.gateCount) + 10 * (28 * k * (n * ℓo + 1)) := by ring
      have : k * c₀.gateCount ≤ 280 * (k * c₀.gateCount) := by omega
      omega
    have hgR : ((ampCirc a k m n ℓo oa c₀).gateCount : ℝ) ≤
        280 * (k : ℝ) * ((c₀.gateCount : ℝ) + n * ℓo + 1) := by exact_mod_cast hgN
    have hX : (0 : ℝ) ≤ (c₀.gateCount : ℝ) + n * ℓo + 1 := by positivity
    calc ((ampCirc a k m n ℓo oa c₀).gateCount : ℝ)
        ≤ 280 * (k : ℝ) * ((c₀.gateCount : ℝ) + n * ℓo + 1) := hgR
      _ ≤ 280 * (13 * L) * ((c₀.gateCount : ℝ) + n * ℓo + 1) := by gcongr
      _ ≤ 4000 * ((c₀.gateCount : ℝ) + n * ℓo + 1) * L := by nlinarith
  · intro OH hOH g δ hyp
    have hamp := amp_prob a k m n ℓo oa s rfl fo c₀ hc OH hOH g δ
      (fun z => ∀ i, |QuantumLTF.Membership.readFp (oa i) fo z - g i| ≤ δ) (fun z => Iff.rfl) hyp
      (fun z => ∀ i, |QuantumLTF.Membership.readFp (outE k m n ℓo oa (by omega) i) fo z - g i| ≤ δ)
      (fun z => Iff.rfl)
    have h78 := pow78_le γ hγ0 k hk8
    rw [ge_iff_le]
    refine le_trans (by linarith) (le_of_le_of_eq hamp ?_)
    congr 1
