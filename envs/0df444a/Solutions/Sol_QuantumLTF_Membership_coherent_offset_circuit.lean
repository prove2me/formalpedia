-- Prove2me | solution 1 for QuantumLTF.Membership.coherent_offset_circuit
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T23:15:51.391536+00:00
-- url     : https://prove2.me/submissions/84ce94ad-6a73-4761-a180-2ffa3ec9f1d1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_addrOf
import Definitions.Def_QuantumLTF_Membership_boundarySearchTreeStrict
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_readFp

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

theorem queryCount_append {n : ℕ} (c₁ c₂ : OracleCircuit S a n) (k : Fin r) :
    (c₁ ++ c₂).queryCount k = c₁.queryCount k + c₂.queryCount k := by
  simp [OracleCircuit.queryCount, List.countP_append]

theorem gateCount_append {n : ℕ} (c₁ c₂ : OracleCircuit S a n) :
    (c₁ ++ c₂).gateCount = c₁.gateCount + c₂.gateCount := by
  simp [OracleCircuit.gateCount, List.countP_append]

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

/-! ### Probabilities -/

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

end Prep

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

-- ===== module H2Final =====

open QAlgorithms

namespace LTFC

theorem coherent_offset_main :
    ∀ (n ℓ₁ f₁ m q ℓ f : ℕ), f₁ + q + 1 ≤ f → f + m + ℓ₁ + 2 ≤ ℓ →
      ∃ (M : ℕ) (c : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
          (fun _ : Fin 1 => n * ℓ + 1) M)
        (pin : Fin (n * ℓ₁) ↪ Fin M) (sw : Fin M) (hw : Fin (m + q + 2) ↪ Fin M),
        QuantumLTF.Membership.Uncontrolled c ∧
        c.queryCount 0 ≤ 2 * (q + 2) ∧
        c.gateCount ≤ 1200 * (n * ℓ + m + q + 2) * (q + 2) ∧
        (∀ i, pin i ≠ sw) ∧ (∀ i j, pin i ≠ hw j) ∧ (∀ j, hw j ≠ sw) ∧
        ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (z : QAlgorithms.Qubits M),
          (∀ v, v ∉ Set.range pin → z v = false) →
          ∃ z' : QAlgorithms.Qubits M,
            (c.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ).mulVec
                (Pi.single z 1) = Pi.single z' 1 ∧
            (∀ v, v ≠ sw → v ∉ Set.range hw → z' v = z v) ∧
            z' sw = decide (((QuantumLTF.Membership.boundarySearchTreeStrict
              (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (z ∘ pin)) ((2 : ℝ) ^ m) q).run
              (QuantumLTF.Membership.ltf w θ)).1 = 1) ∧
            QuantumLTF.Membership.fpVal (m + q + 2) (q + 1) (z' ∘ hw) =
              ((QuantumLTF.Membership.boundarySearchTreeStrict
                (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (z ∘ pin)) ((2 : ℝ) ^ m) q).run
                (QuantumLTF.Membership.ltf w θ)).2 := by
  intro n ℓ₁ f₁ m q ℓ f hf hℓ
  obtain ⟨hu, hq, hg, hsem⟩ := offset_circuit n ℓ₁ f₁ m q ℓ f hf hℓ
  refine ⟨_, offCirc n ℓ₁ f₁ m q ℓ f hf hℓ, offPin n ℓ₁ f₁ m q ℓ f, offSw n ℓ₁ f₁ m q ℓ f,
    offHw n ℓ₁ f₁ m q ℓ f, hu, hq, hg, ?_, ?_, ?_, ?_⟩
  · intro i h; have := congrArg Fin.val h; rw [offPin_val, offSw_val] at this; have := i.isLt; omega
  · intro i j h; have := congrArg Fin.val h; rw [offPin_val, offHw_val] at this; have := i.isLt
    omega
  · intro j h; have := congrArg Fin.val h; rw [offHw_val, offSw_val] at this; omega
  · intro w θ z hz
    obtain ⟨z', h1, h2, h3, h4⟩ := hsem w θ z (fun v hv => hz v (by
      rintro ⟨i, rfl⟩; rw [offPin_val] at hv; have := i.isLt; omega))
    exact ⟨z', h1, h2, h3, h4⟩

end LTFC

-- ===== final =====
theorem solution :
    ∀ (n ℓ₁ f₁ m q ℓ f : ℕ), f₁ + q + 1 ≤ f → f + m + ℓ₁ + 2 ≤ ℓ →
      ∃ (M : ℕ) (c : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
          (fun _ : Fin 1 => n * ℓ + 1) M)
        (pin : Fin (n * ℓ₁) ↪ Fin M) (sw : Fin M) (hw : Fin (m + q + 2) ↪ Fin M),
        QuantumLTF.Membership.Uncontrolled c ∧
        c.queryCount 0 ≤ 2 * (q + 2) ∧
        c.gateCount ≤ 1200 * (n * ℓ + m + q + 2) * (q + 2) ∧
        (∀ i, pin i ≠ sw) ∧ (∀ i j, pin i ≠ hw j) ∧ (∀ j, hw j ≠ sw) ∧
        ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (z : QAlgorithms.Qubits M),
          (∀ v, v ∉ Set.range pin → z v = false) →
          ∃ z' : QAlgorithms.Qubits M,
            (c.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ).mulVec
                (Pi.single z 1) = Pi.single z' 1 ∧
            (∀ v, v ≠ sw → v ∉ Set.range hw → z' v = z v) ∧
            z' sw = decide (((QuantumLTF.Membership.boundarySearchTreeStrict
              (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (z ∘ pin)) ((2 : ℝ) ^ m) q).run
              (QuantumLTF.Membership.ltf w θ)).1 = 1) ∧
            QuantumLTF.Membership.fpVal (m + q + 2) (q + 1) (z' ∘ hw) =
              ((QuantumLTF.Membership.boundarySearchTreeStrict
                (QuantumLTF.Membership.addrOf n ℓ₁ f₁ (z ∘ pin)) ((2 : ℝ) ^ m) q).run
                (QuantumLTF.Membership.ltf w θ)).2 :=
  LTFC.coherent_offset_main
