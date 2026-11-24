-- Prove2me | solution 1 for QuantumLTF.Membership.uniform_height_circuit
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T23:00:11.502961+00:00
-- url     : https://prove2.me/submissions/2a48ebda-e29b-4e35-9932-cc0dfc139588

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_addrOf
import Definitions.Def_QuantumLTF_Membership_regBasis
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Definitions.Def_QuantumLTF_Membership_sgn
import Theorems.Thm_QuantumLTF_Membership_local_bisection_parameters
import Theorems.Thm_QuantumLTF_Membership_localizedAffineBisect_error

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

-- ===== module U1 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

noncomputable def permMat {k : ℕ} (g : Qubits k → Qubits k) : Matrix (Qubits k) (Qubits k) ℂ :=
  Matrix.of fun y z => if y = g z then 1 else 0

theorem act_ket_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (z z' : ι)
    (h : ∀ y, A y z = if y = z' then 1 else 0) : act A (ket z) = ket z' := by
  ext y
  simp [act, ket, PiLp.single_apply, h]

theorem act_embed_perm {k N : ℕ} (g : Qubits k → Qubits k) (w : Fin k ↪ Fin N) (z z' : Qubits N)
    (h1 : ∀ a, a ∉ Set.range w → z' a = z a) (h2 : ∀ j, z' (w j) = g (z ∘ w) j) :
    act (embedOp (permMat g) w) (ket z) = ket z' := by
  apply act_ket_eq
  intro y
  simp only [embedOp, permMat, Matrix.of_apply]
  by_cases hy : y = z'
  · subst hy
    have e : y ∘ w = g (z ∘ w) := funext h2
    rw [if_pos h1, if_pos e, if_pos rfl]
  · rw [if_neg hy]
    split_ifs with hA hB
    · exfalso; apply hy; funext a
      by_cases ha : a ∈ Set.range w
      · obtain ⟨j, rfl⟩ := ha; rw [h2]; exact congrFun hB j
      · rw [hA a ha, h1 a ha]
    all_goals rfl

/-! ### Instructions -/

inductive Ins
  | not (t : ℕ)
  | cnot (a t : ℕ)
  | tof (a b t : ℕ)
  | qry (base : ℕ)

def Ins.tgt (A : ℕ) : Ins → ℕ
  | .not t => t
  | .cnot _ t => t
  | .tof _ _ t => t
  | .qry base => base + A

def Ins.fn (A : ℕ) (O : Qubits A → Bool) : Ins → (ℕ → Bool) → Bool
  | .not _, _ => true
  | .cnot a _, Z => Z a
  | .tof a b _, Z => Z a && Z b
  | .qry base, Z => O (fun j => Z (base + j))

def Ins.src (A : ℕ) : Ins → ℕ → Prop
  | .not _ => fun _ => False
  | .cnot a _ => fun s => s = a
  | .tof a b _ => fun s => s = a ∨ s = b
  | .qry base => fun s => base ≤ s ∧ s < base + A

def Ins.isQ : Ins → Bool
  | .qry _ => true
  | _ => false

def Ins.eval (A : ℕ) (O : Qubits A → Bool) (I : Ins) (Z : ℕ → Bool) : ℕ → Bool :=
  Function.update Z (I.tgt A) (xor (Z (I.tgt A)) (I.fn A O Z))

def evalP (A : ℕ) (O : Qubits A → Bool) (P : List Ins) (Z : ℕ → Bool) : ℕ → Bool :=
  P.foldl (fun Z I => I.eval A O Z) Z

theorem evalP_nil (A : ℕ) (O : Qubits A → Bool) (Z : ℕ → Bool) : evalP A O [] Z = Z := rfl

theorem evalP_cons (A : ℕ) (O : Qubits A → Bool) (I : Ins) (P : List Ins) (Z : ℕ → Bool) :
    evalP A O (I :: P) Z = evalP A O P (I.eval A O Z) := rfl

theorem evalP_append (A : ℕ) (O : Qubits A → Bool) (P Q : List Ins) (Z : ℕ → Bool) :
    evalP A O (P ++ Q) Z = evalP A O Q (evalP A O P Z) := by
  simp [evalP, List.foldl_append]

theorem Ins.fn_congr (A : ℕ) (O : Qubits A → Bool) (I : Ins) (Z Z' : ℕ → Bool)
    (h : ∀ s, I.src A s → Z s = Z' s) : I.fn A O Z = I.fn A O Z' := by
  cases I with
  | not t => rfl
  | cnot a t => simp only [Ins.fn]; exact h a rfl
  | tof a b t => simp only [Ins.fn]; rw [h a (Or.inl rfl), h b (Or.inr rfl)]
  | qry base =>
    simp only [Ins.fn]; congr 1; funext j
    exact h _ ⟨by omega, by omega⟩

/-- The target is not a source. -/
def Ins.NS (A : ℕ) (I : Ins) : Prop := ¬ I.src A (I.tgt A)

theorem Ins.eval_eval (A : ℕ) (O : Qubits A → Bool) (I : Ins) (hI : I.NS A) (Z : ℕ → Bool) :
    I.eval A O (I.eval A O Z) = Z := by
  have hfn : I.fn A O (I.eval A O Z) = I.fn A O Z := by
    apply Ins.fn_congr
    intro s hs
    have : s ≠ I.tgt A := by rintro rfl; exact hI hs
    simp [Ins.eval, Function.update_of_ne this]
  funext w
  rw [show I.eval A O (I.eval A O Z) = Function.update (I.eval A O Z) (I.tgt A)
    (xor (I.eval A O Z (I.tgt A)) (I.fn A O (I.eval A O Z))) from rfl, hfn]
  by_cases hw : w = I.tgt A
  · subst hw; simp [Ins.eval]
  · simp [Ins.eval, Function.update_of_ne hw]

theorem evalP_reverse (A : ℕ) (O : Qubits A → Bool) (P : List Ins) (hP : ∀ I ∈ P, I.NS A)
    (Z : ℕ → Bool) : evalP A O P.reverse (evalP A O P Z) = Z := by
  induction P generalizing Z with
  | nil => rfl
  | cons I P ih =>
    rw [evalP_cons, List.reverse_cons, evalP_append, ih (fun J hJ => hP J (by simp [hJ]))]
    simp only [evalP, List.foldl_cons, List.foldl_nil]
    exact Ins.eval_eval A O I (hP I (by simp)) Z

/-- Frame property: a program none of whose wires lies in `V`. -/
theorem evalP_frame (A : ℕ) (O : Qubits A → Bool) (V : ℕ → Prop) (P : List Ins)
    (hP : ∀ I ∈ P, ¬ V (I.tgt A) ∧ ∀ s, I.src A s → ¬ V s) (Z Z' : ℕ → Bool)
    (hZ : ∀ w, ¬ V w → Z w = Z' w) :
    (∀ w, ¬ V w → evalP A O P Z w = evalP A O P Z' w) ∧ (∀ w, V w → evalP A O P Z w = Z w) := by
  induction P generalizing Z Z' with
  | nil => exact ⟨hZ, fun _ _ => rfl⟩
  | cons I P ih =>
    have hI := hP I (by simp)
    have hfn : I.fn A O Z = I.fn A O Z' :=
      Ins.fn_congr A O I Z Z' (fun s hs => hZ s (hI.2 s hs))
    have h1 : ∀ w, ¬ V w → I.eval A O Z w = I.eval A O Z' w := by
      intro w hw
      by_cases ht : w = I.tgt A
      · subst ht; simp [Ins.eval, hfn, hZ _ hw]
      · simp [Ins.eval, Function.update_of_ne ht, hZ _ hw]
    obtain ⟨ih1, ih2⟩ := ih (fun J hJ => hP J (by simp [hJ])) _ _ h1
    refine ⟨ih1, fun w hw => ?_⟩
    rw [evalP_cons, ih2 w hw]
    have : w ≠ I.tgt A := by rintro rfl; exact hI.1 hw
    simp [Ins.eval, Function.update_of_ne this]

/-! ### Translation to oracle circuits -/

def gX (z : Qubits 1) : Qubits 1 := fun _ => !(z 0)
def gC (z : Qubits 2) : Qubits 2 := ![z 0, xor (z 1) (z 0)]
def gT (z : Qubits 3) : Qubits 3 := ![z 0, z 1, xor (z 2) (z 0 && z 1)]

noncomputable def xGate : Gate := ⟨1, permMat gX⟩
noncomputable def cGate : Gate := ⟨2, permMat gC⟩
noncomputable def tGate : Gate := ⟨3, permMat gT⟩

theorem X_mat : pauliX.submatrix (fun b : Qubits 1 => b 0) (fun b => b 0) = permMat gX := by
  ext y z
  simp only [Matrix.submatrix_apply, pauliX, permMat, Matrix.of_apply, gX]
  have : (y = gX z) ↔ y 0 = !(z 0) := by
    constructor
    · rintro rfl; rfl
    · intro h; funext i; rw [Subsingleton.elim i 0]; exact h
  by_cases h : y 0 = z 0
  · rw [if_pos h, if_neg]; rw [this, h]; simp
  · rw [if_neg h, if_pos]; rw [this]; cases hy : y 0 <;> cases hz : z 0 <;> simp_all

theorem cnot_mat : cnot.submatrix (fun b : Qubits 2 => (b 0, b 1)) (fun b => (b 0, b 1)) =
    permMat gC := by
  ext y z
  simp only [Matrix.submatrix_apply, cnot, permMat, Matrix.of_apply, gC]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩; funext i; fin_cases i <;> simp [h1, h2]
  · intro h; subst h; simp

theorem X_mem : xGate ∈ gatesRev := by
  have : xGate = Gate.ofMatrix1 pauliX := by
    simp only [xGate, Gate.ofMatrix1, Gate.mk.injEq, heq_eq_eq, true_and]; exact X_mat.symm
  rw [this]; exact Set.mem_insert _ _
theorem cnot_mem : cGate ∈ gatesRev := by
  have : cGate = Gate.ofMatrix2 cnot := by
    simp only [cGate, Gate.ofMatrix2, Gate.mk.injEq, heq_eq_eq, true_and]; exact cnot_mat.symm
  rw [this]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
theorem tof_mem : tGate ∈ gatesRev := by
  have : tGate = ⟨3, Matrix.of fun y z =>
      if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) then 1 else 0⟩ := by
    simp only [tGate, Gate.mk.injEq, heq_eq_eq, true_and]
    ext y z
    simp only [permMat, Matrix.of_apply, gT]
    congr 1
    apply propext
    constructor
    · intro h; subst h; simp
    · rintro ⟨h1, h2, h3⟩; funext i; fin_cases i <;> simp [h1, h2, h3]
  rw [this]; exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

def emb1 {N : ℕ} (t : Fin N) : Fin 1 ↪ Fin N := ⟨fun _ => t, fun a b _ => Subsingleton.elim a b⟩

def emb2 {N : ℕ} (a t : Fin N) (h : a ≠ t) : Fin 2 ↪ Fin N :=
  ⟨![a, t], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

def emb3 {N : ℕ} (a b t : Fin N) (h1 : a ≠ b) (h2 : a ≠ t) (h3 : b ≠ t) : Fin 3 ↪ Fin N :=
  ⟨![a, b, t], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

def embQ {N : ℕ} (A base : ℕ) (h : base + A < N) : Fin (A + 1) ↪ Fin N :=
  ⟨fun j => ⟨base + j, by omega⟩, by
    intro i j hij
    simp only [Fin.mk.injEq] at hij
    exact Fin.ext (by omega)⟩

@[simp] theorem emb1_apply {N : ℕ} (t : Fin N) (j : Fin 1) : emb1 t j = t := rfl
@[simp] theorem emb2_apply0 {N : ℕ} (a t : Fin N) (h : a ≠ t) : emb2 a t h 0 = a := rfl
@[simp] theorem emb2_apply1 {N : ℕ} (a t : Fin N) (h : a ≠ t) : emb2 a t h 1 = t := rfl
@[simp] theorem emb3_apply0 {N : ℕ} (a b t : Fin N) (h1 : a ≠ b) (h2 : a ≠ t) (h3 : b ≠ t) :
    emb3 a b t h1 h2 h3 0 = a := rfl
@[simp] theorem emb3_apply1 {N : ℕ} (a b t : Fin N) (h1 : a ≠ b) (h2 : a ≠ t) (h3 : b ≠ t) :
    emb3 a b t h1 h2 h3 1 = b := rfl
@[simp] theorem emb3_apply2 {N : ℕ} (a b t : Fin N) (h1 : a ≠ b) (h2 : a ≠ t) (h3 : b ≠ t) :
    emb3 a b t h1 h2 h3 2 = t := rfl
@[simp] theorem embQ_apply {N : ℕ} (A base : ℕ) (h : base + A < N) (j : Fin (A + 1)) :
    ((embQ A base h j : Fin N) : ℕ) = base + j := rfl

def cnotC (N A : ℕ) (a t : ℕ) : OracleCircuit gatesRev (fun _ : Fin 1 => A + 1) N :=
  if h : a < N ∧ t < N ∧ a ≠ t then
    [.gate ⟨cGate, cnot_mem,
      emb2 ⟨a, h.1⟩ ⟨t, h.2.1⟩ (by simp [Fin.ext_iff]; exact h.2.2)⟩]
  else []

def Ins.toC (N A : ℕ) : Ins → OracleCircuit gatesRev (fun _ : Fin 1 => A + 1) N
  | .not t => if h : t < N then [.gate ⟨xGate, X_mem, emb1 ⟨t, h⟩⟩] else []
  | .cnot a t => cnotC N A a t
  | .tof a b t =>
      if a = b then cnotC N A a t
      else if h : a < N ∧ b < N ∧ t < N ∧ a ≠ b ∧ a ≠ t ∧ b ≠ t then
        [.gate ⟨tGate, tof_mem, emb3 ⟨a, h.1⟩ ⟨b, h.2.1⟩ ⟨t, h.2.2.1⟩
          (by simp [Fin.ext_iff]; exact h.2.2.2.1) (by simp [Fin.ext_iff]; exact h.2.2.2.2.1)
          (by simp [Fin.ext_iff]; exact h.2.2.2.2.2)⟩]
      else []
  | .qry base => if h : base + A < N then
      [.query 0 false none (embQ A base h) (by intro c hc; cases hc)] else []

def toCP (N A : ℕ) (P : List Ins) : OracleCircuit gatesRev (fun _ : Fin 1 => A + 1) N :=
  P.flatMap (Ins.toC N A)

def toQ (N : ℕ) (Z : ℕ → Bool) : Qubits N := fun i => Z i

/-- The oracle permutation. -/
def gO (A : ℕ) (O : Qubits A → Bool) (z : Qubits (A + 1)) : Qubits (A + 1) :=
  Fin.snoc (α := fun _ => Bool) (Fin.init z) (xor (z (Fin.last _)) (O (Fin.init z)))

/-- Well-formedness w.r.t. the register size. -/
def Ins.WF (N A : ℕ) (I : Ins) : Prop :=
  I.tgt A < N ∧ ∀ s, I.src A s → s < N ∧ s ≠ I.tgt A

theorem unitary_append {N A : ℕ} (c1 c2 : OracleCircuit gatesRev (fun _ : Fin 1 => A + 1) N)
    (orc : (k : Fin 1) → Matrix (Qubits (A + 1)) (Qubits (A + 1)) ℂ) :
    (c1 ++ c2).unitary orc = c2.unitary orc * c1.unitary orc := by
  simp [OracleCircuit.unitary, List.map_append, List.reverse_append, List.prod_append]

theorem act_mul' {ι : Type*} [Fintype ι] (M M' : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (M * M') v = act M (act M' v) := by
  simp [act, Matrix.mulVec_mulVec]

theorem unitary_single {N A : ℕ} (st : OracleStep gatesRev (fun _ : Fin 1 => A + 1) N)
    (orc : (k : Fin 1) → Matrix (Qubits (A + 1)) (Qubits (A + 1)) ℂ) :
    OracleCircuit.unitary [st] orc = st.mat orc := by
  simp [OracleCircuit.unitary]

theorem act_cnotC (N A : ℕ) (orc : (k : Fin 1) → Matrix (Qubits (A + 1)) (Qubits (A + 1)) ℂ)
    (a t : ℕ) (ha : a < N) (ht : t < N) (hat : a ≠ t) (Z : ℕ → Bool) :
    act ((cnotC N A a t).unitary orc) (ket (toQ N Z)) =
      ket (toQ N (Function.update Z t (xor (Z t) (Z a)))) := by
  have hh : a < N ∧ t < N ∧ a ≠ t := ⟨ha, ht, hat⟩
  simp only [cnotC, dif_pos hh, unitary_single, OracleStep.mat, cGate]
  apply act_embed_perm
  · intro x hx
    have hxt : (x : ℕ) ≠ t := by
      intro h; apply hx; exact ⟨1, by simp [Fin.ext_iff, h]⟩
    simp [toQ, Function.update_of_ne hxt]
  · intro j
    fin_cases j
    · simp [toQ, gC, Function.update_of_ne hat]
    · simp [toQ, gC]

theorem Ins.act_toC (N A : ℕ) (O : Qubits A → Bool)
    (orc : (k : Fin 1) → Matrix (Qubits (A + 1)) (Qubits (A + 1)) ℂ)
    (horc : orc 0 = permMat (gO A O)) (I : Ins) (hwf : I.WF N A) (Z : ℕ → Bool) :
    act ((I.toC N A).unitary orc) (ket (toQ N Z)) = ket (toQ N (I.eval A O Z)) := by
  obtain ⟨ht, hs⟩ := hwf
  cases I with
  | not t =>
    simp only [Ins.tgt] at ht
    simp only [Ins.toC, dif_pos ht, unitary_single, OracleStep.mat, xGate]
    apply act_embed_perm
    · intro x hx
      have hxt : (x : ℕ) ≠ t := by
        intro h; apply hx; exact ⟨0, by simp [Fin.ext_iff, h]⟩
      simp [toQ, Ins.eval, Ins.tgt, Function.update_of_ne hxt]
    · intro j
      simp [toQ, gX, Ins.eval, Ins.tgt, Ins.fn]
  | cnot a t =>
    simp only [Ins.tgt, Ins.src] at ht hs
    have h := hs a rfl
    simp only [Ins.toC]
    rw [act_cnotC N A orc a t h.1 ht h.2]
    rfl
  | tof a b t =>
    simp only [Ins.tgt, Ins.src] at ht hs
    have ha := hs a (Or.inl rfl)
    have hb := hs b (Or.inr rfl)
    simp only [Ins.toC]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, act_cnotC N A orc a t ha.1 ht ha.2]
      congr 2
      simp [Ins.eval, Ins.tgt, Ins.fn]
    · have hh : a < N ∧ b < N ∧ t < N ∧ a ≠ b ∧ a ≠ t ∧ b ≠ t :=
        ⟨ha.1, hb.1, ht, hab, ha.2, hb.2⟩
      rw [if_neg hab, dif_pos hh, unitary_single]
      simp only [OracleStep.mat, tGate]
      apply act_embed_perm
      · intro x hx
        have hxt : (x : ℕ) ≠ t := by
          intro h; apply hx; exact ⟨2, by simp [Fin.ext_iff, h]⟩
        simp [toQ, Ins.eval, Ins.tgt, Function.update_of_ne hxt]
      · intro j
        fin_cases j
        · simp [toQ, gT, Ins.eval, Ins.tgt, Function.update_of_ne ha.2]
        · simp [toQ, gT, Ins.eval, Ins.tgt, Function.update_of_ne hb.2]
        · simp [toQ, gT, Ins.eval, Ins.tgt, Ins.fn]
  | qry base =>
    simp only [Ins.tgt] at ht
    simp only [Ins.toC, dif_pos ht, unitary_single, OracleStep.mat]
    simp only [Bool.false_eq_true, ↓reduceIte, horc]
    apply act_embed_perm
    · intro x hx
      have hxt : (x : ℕ) ≠ base + A := by
        intro h; apply hx; exact ⟨Fin.last A, by simp [Fin.ext_iff, h]⟩
      simp [toQ, Ins.eval, Ins.tgt, Function.update_of_ne hxt]
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · have e : Fin.init (toQ N Z ∘ ⇑(embQ A base ht)) = fun j : Fin A => Z (base + j) := by
          funext j; simp [Fin.init, toQ]
        simp [toQ, Ins.eval, Ins.tgt, Ins.fn, gO, e]
      · have hne : base + (i : ℕ) ≠ base + A := by have := i.isLt; omega
        simp [toQ, Ins.eval, Ins.tgt, gO, Fin.init, Function.update_of_ne hne]

theorem act_toCP (N A : ℕ) (O : Qubits A → Bool)
    (orc : (k : Fin 1) → Matrix (Qubits (A + 1)) (Qubits (A + 1)) ℂ)
    (horc : orc 0 = permMat (gO A O)) (P : List Ins) (hwf : ∀ I ∈ P, I.WF N A)
    (Z : ℕ → Bool) :
    act ((toCP N A P).unitary orc) (ket (toQ N Z)) = ket (toQ N (evalP A O P Z)) := by
  induction P generalizing Z with
  | nil =>
    simp [toCP, OracleCircuit.unitary, evalP, act]
  | cons I P ih =>
    have e : toCP N A (I :: P) = I.toC N A ++ toCP N A P := by simp [toCP]
    rw [e, unitary_append, act_mul', Ins.act_toC N A O orc horc I (hwf I (by simp)),
      ih (fun J hJ => hwf J (by simp [hJ]))]
    rfl

theorem toC_length_le (N A : ℕ) (I : Ins) : (I.toC N A).length ≤ 1 := by
  cases I <;> simp only [Ins.toC, cnotC] <;> split_ifs <;> simp

theorem queryCount_toC (N A : ℕ) (I : Ins) :
    (I.toC N A).countP (OracleStep.IsQueryTo 0) ≤ if I.isQ then 1 else 0 := by
  cases I <;> simp only [Ins.toC, cnotC, Ins.isQ] <;> split_ifs <;>
    simp [OracleStep.IsQueryTo]

theorem queryCount_toCP (N A : ℕ) (P : List Ins) :
    (toCP N A P).queryCount 0 ≤ P.countP Ins.isQ := by
  induction P with
  | nil => simp [toCP, OracleCircuit.queryCount]
  | cons I P ih =>
    have e : toCP N A (I :: P) = I.toC N A ++ toCP N A P := by simp [toCP]
    simp only [OracleCircuit.queryCount] at ih ⊢
    rw [e, List.countP_append, List.countP_cons]
    have := queryCount_toC N A I
    split_ifs at this ⊢ <;> omega

theorem gateCount_toCP (N A : ℕ) (P : List Ins) :
    (toCP N A P).gateCount ≤ P.length := by
  have : (toCP N A P).gateCount ≤ (toCP N A P).length := List.countP_le_length
  refine this.trans ?_
  clear this
  induction P with
  | nil => simp [toCP]
  | cons I P ih =>
    have e : toCP N A (I :: P) = I.toC N A ++ toCP N A P := by simp [toCP]
    rw [e, List.length_append, List.length_cons]
    have := toC_length_le N A I
    omega

theorem uncontrolled_toCP (N A : ℕ) (P : List Ins) : Uncontrolled (toCP N A P) := by
  intro st hst
  simp only [toCP, List.mem_flatMap] at hst
  obtain ⟨I, _, hI⟩ := hst
  cases I <;> simp only [Ins.toC, cnotC] at hI <;> split_ifs at hI <;> simp at hI <;>
    subst hI <;> trivial

theorem memOracle_eq (n ℓ f : ℕ) (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    memOracle n ℓ f w θ =
      permMat (gO (n * ℓ) (fun y => decide (ltf w θ (addrOf n ℓ f y) = -1))) := rfl


/-! ### Arbitrary basis inputs -/

def ofQ {N : ℕ} (y : Qubits N) (w : ℕ) : Bool := if h : w < N then y ⟨w, h⟩ else false

theorem toQ_ofQ {N : ℕ} (y : Qubits N) : toQ N (ofQ y) = y := by
  funext ⟨w, hw⟩; simp [toQ, ofQ, hw]

theorem unitary_entry_ne_zero (N A : ℕ) (O : Qubits A → Bool)
    (orc : (k : Fin 1) → Matrix (Qubits (A + 1)) (Qubits (A + 1)) ℂ)
    (horc : orc 0 = permMat (gO A O)) (P : List Ins) (hwf : ∀ I ∈ P, I.WF N A)
    (y y' : Qubits N) (h : (toCP N A P).unitary orc y' y ≠ 0) :
    y' = toQ N (evalP A O P (ofQ y)) := by
  have e := act_toCP N A O orc horc P hwf (ofQ y)
  rw [toQ_ofQ] at e
  have e2 := congrArg (fun v : EuclideanSpace ℂ (Qubits N) => v y') e
  simp only [act, ket, Matrix.mulVec, dotProduct] at e2
  by_contra hne
  apply h
  have : ((EuclideanSpace.single (toQ N (evalP A O P (ofQ y))) (1 : ℂ)) : EuclideanSpace ℂ (Qubits N)) y' = 0 := by
    simp [EuclideanSpace.single_apply, Ne.symm hne, hne]
  rw [this] at e2
  simpa [EuclideanSpace.single_apply] using e2

end

end QuantumLTF.Membership.A2

-- ===== module U2 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

def Fresh (Z : ℕ → Bool) (c : ℕ) : Prop := ∀ w, c ≤ w → Z w = false

def valLE : List Bool → ℕ
  | [] => 0
  | b :: L => b.toNat + 2 * valLE L

@[simp] theorem valLE_nil : valLE [] = 0 := rfl
@[simp] theorem valLE_cons (b : Bool) (L : List Bool) : valLE (b :: L) = b.toNat + 2 * valLE L := rfl

theorem valLE_lt (L : List Bool) : valLE L < 2 ^ L.length := by
  induction L with
  | nil => simp
  | cons b L ih => cases b <;> simp [pow_succ] <;> omega

def Good (A : ℕ) (S : ℕ → Prop) (lo hi : ℕ) (I : Ins) : Prop :=
  lo ≤ I.tgt A ∧ I.tgt A < hi ∧ ∀ s, I.src A s → s < I.tgt A ∧ S s

theorem Good.mono {A : ℕ} {S : ℕ → Prop} {lo hi lo' hi' : ℕ} {I : Ins} (h : Good A S lo hi I)
    (h1 : lo' ≤ lo) (h2 : hi ≤ hi') : Good A S lo' hi' I :=
  ⟨le_trans h1 h.1, lt_of_lt_of_le h.2.1 h2, h.2.2⟩

section
variable (A : ℕ) (O : Qubits A → Bool)

@[simp] theorem eval_not (t : ℕ) (Z : ℕ → Bool) :
    (Ins.not t).eval A O Z = Function.update Z t (!Z t) := by
  simp [Ins.eval, Ins.tgt, Ins.fn]

@[simp] theorem eval_cnot (a t : ℕ) (Z : ℕ → Bool) :
    (Ins.cnot a t).eval A O Z = Function.update Z t (xor (Z t) (Z a)) := rfl

@[simp] theorem eval_tof (a b t : ℕ) (Z : ℕ → Bool) :
    (Ins.tof a b t).eval A O Z = Function.update Z t (xor (Z t) (Z a && Z b)) := rfl

/-! ### Fill (general specs: a constant XOR a list of AND terms) -/

abbrev Spec := Bool × List (ℕ × ℕ)

def xl (Z : ℕ → Bool) : List (ℕ × ℕ) → Bool
  | [] => false
  | t :: ts => xor (Z t.1 && Z t.2) (xl Z ts)

@[simp] theorem xl_nil (Z : ℕ → Bool) : xl Z [] = false := rfl
@[simp] theorem xl_cons (Z : ℕ → Bool) (t : ℕ × ℕ) (ts : List (ℕ × ℕ)) :
    xl Z (t :: ts) = xor (Z t.1 && Z t.2) (xl Z ts) := rfl

def specVal (Z : ℕ → Bool) (sp : Spec) : Bool := xor sp.1 (xl Z sp.2)

def tIns (t : ℕ) (ts : List (ℕ × ℕ)) : List Ins := ts.map fun ab => Ins.tof ab.1 ab.2 t

def specIns (t : ℕ) (sp : Spec) : List Ins :=
  (if sp.1 then [Ins.not t] else []) ++ tIns t sp.2

def fill : List Spec → ℕ → List Ins
  | [], _ => []
  | sp :: sps, c => specIns c sp ++ fill sps (c + 1)

/-- All wires mentioned by a spec. -/
def SpSrc (sp : Spec) (a : ℕ) : Prop := ∃ ab ∈ sp.2, a = ab.1 ∨ a = ab.2

def SrcLt (sps : List Spec) (c : ℕ) : Prop := ∀ sp ∈ sps, ∀ a, SpSrc sp a → a < c

theorem xl_congr (Z Z' : ℕ → Bool) (ts : List (ℕ × ℕ))
    (h : ∀ ab ∈ ts, Z ab.1 = Z' ab.1 ∧ Z ab.2 = Z' ab.2) : xl Z ts = xl Z' ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [xl_cons]
    rw [(h t (by simp)).1, (h t (by simp)).2, ih (fun ab hab => h ab (by simp [hab]))]

theorem specVal_congr (Z Z' : ℕ → Bool) (sp : Spec) (h : ∀ a, SpSrc sp a → Z a = Z' a) :
    specVal Z sp = specVal Z' sp := by
  simp only [specVal]
  rw [xl_congr Z Z' sp.2 (fun ab hab => ⟨h _ ⟨ab, hab, Or.inl rfl⟩, h _ ⟨ab, hab, Or.inr rfl⟩⟩)]

theorem tIns_sem (t : ℕ) (ts : List (ℕ × ℕ)) (Z : ℕ → Bool)
    (hs : ∀ ab ∈ ts, ab.1 ≠ t ∧ ab.2 ≠ t) :
    evalP A O (tIns t ts) Z = Function.update Z t (xor (Z t) (xl Z ts)) := by
  induction ts generalizing Z with
  | nil => simp [tIns, evalP]
  | cons ab ts ih =>
    have h1 := hs ab (by simp)
    simp only [tIns, List.map_cons, evalP_cons, eval_tof]
    have e := ih (Function.update Z t (xor (Z t) (Z ab.1 && Z ab.2))) (fun ab' h => hs ab' (by simp [h]))
    simp only [tIns] at e
    rw [e]
    have hc : xl (Function.update Z t (xor (Z t) (Z ab.1 && Z ab.2))) ts = xl Z ts :=
      xl_congr _ _ ts (fun ab' h => by
        have := hs ab' (by simp [h])
        exact ⟨Function.update_of_ne this.1 _ _, Function.update_of_ne this.2 _ _⟩)
    rw [hc]
    funext w
    by_cases hw : w = t
    · subst hw; simp [Bool.xor_assoc]
    · simp [Function.update_of_ne hw]

theorem specIns_sem (t : ℕ) (sp : Spec) (Z : ℕ → Bool) (hZ : Z t = false)
    (hs : ∀ a, SpSrc sp a → a ≠ t) :
    evalP A O (specIns t sp) Z = Function.update Z t (specVal Z sp) := by
  obtain ⟨k, ts⟩ := sp
  have hs' : ∀ ab ∈ ts, ab.1 ≠ t ∧ ab.2 ≠ t := fun ab h =>
    ⟨hs _ ⟨ab, h, Or.inl rfl⟩, hs _ ⟨ab, h, Or.inr rfl⟩⟩
  cases k
  · simp only [specIns, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rw [tIns_sem A O t ts Z hs', hZ]
    simp [specVal]
  · simp only [specIns, ↓reduceIte, List.singleton_append, evalP_cons, eval_not]
    rw [tIns_sem A O t ts _ hs']
    have hc : xl (Function.update Z t (!Z t)) ts = xl Z ts :=
      xl_congr _ _ ts (fun ab' h => ⟨Function.update_of_ne (hs' ab' h).1 _ _,
        Function.update_of_ne (hs' ab' h).2 _ _⟩)
    rw [hc, hZ]
    funext w
    by_cases hw : w = t
    · subst hw; simp [specVal]
    · simp [Function.update_of_ne hw]

theorem fill_sem (sps : List Spec) (c : ℕ) (Z : ℕ → Bool) (hF : Fresh Z c) (hs : SrcLt sps c) :
    (∀ w, w < c → evalP A O (fill sps c) Z w = Z w) ∧
    Fresh (evalP A O (fill sps c) Z) (c + sps.length) ∧
    ∀ m (hm : m < sps.length), evalP A O (fill sps c) Z (c + m) = specVal Z sps[m] := by
  induction sps generalizing c Z with
  | nil =>
    refine ⟨fun _ _ => rfl, by simpa [fill, evalP] using hF, fun m hm => by simp at hm⟩
  | cons sp sps ih =>
    have hsp : ∀ a, SpSrc sp a → a ≠ c := fun a ha => (hs sp (by simp) a ha).ne
    set Z1 := Function.update Z c (specVal Z sp) with hZ1
    have e1 : evalP A O (specIns c sp) Z = Z1 := specIns_sem A O c sp Z (hF c le_rfl) hsp
    have hF1 : Fresh Z1 (c + 1) := by
      intro w hw
      rw [hZ1, Function.update_of_ne (by omega)]; exact hF w (by omega)
    have hs1 : SrcLt sps (c + 1) := fun sp' h a ha => by
      have := hs sp' (by simp [h]) a ha; omega
    obtain ⟨ih1, ih2, ih3⟩ := ih (c + 1) Z1 hF1 hs1
    have hfill : fill (sp :: sps) c = specIns c sp ++ fill sps (c + 1) := rfl
    have hcongr : ∀ sp' ∈ sps, specVal Z1 sp' = specVal Z sp' := by
      intro sp' h
      apply specVal_congr
      intro a ha
      have := hs sp' (by simp [h]) a ha
      rw [hZ1, Function.update_of_ne this.ne]
    rw [hfill, evalP_append, e1]
    refine ⟨fun w hw => ?_, ?_, fun m hm => ?_⟩
    · rw [ih1 w (by omega), hZ1, Function.update_of_ne (by omega)]
    · simpa [Nat.add_assoc, Nat.add_comm 1] using ih2
    · cases m with
      | zero => simp only [Nat.add_zero, List.getElem_cons_zero]; rw [ih1 c (by omega)]; simp [hZ1]
      | succ m =>
        have hm' : m < sps.length := by simpa using hm
        rw [show c + (m + 1) = c + 1 + m by omega, ih3 m hm', hcongr _ (List.getElem_mem hm')]
        rfl

theorem fill_map (sps : List Spec) (c : ℕ) (Z : ℕ → Bool) (hF : Fresh Z c) (hs : SrcLt sps c) :
    (List.range' c sps.length).map (evalP A O (fill sps c) Z) = sps.map (specVal Z) := by
  obtain ⟨_, _, h3⟩ := fill_sem A O sps c Z hF hs
  apply List.ext_getElem (by simp)
  intro m h1 h2
  simp only [List.getElem_map, List.getElem_range']
  simp only [List.length_map, List.length_range'] at h1
  rw [show c + 1 * m = c + m by ring, h3 m h1]

theorem fill_length (sps : List Spec) (k : ℕ) (hk : ∀ sp ∈ sps, sp.2.length ≤ k) (c : ℕ) :
    (fill sps c).length ≤ (k + 1) * sps.length := by
  induction sps generalizing c with
  | nil => simp [fill]
  | cons sp sps ih =>
    have := ih (fun sp' h => hk sp' (by simp [h])) (c + 1)
    have h2 := hk sp (by simp)
    have h3 : (specIns c sp).length ≤ k + 1 := by
      simp only [specIns, tIns, List.length_append, List.length_map]
      split_ifs <;> simp <;> omega
    simp only [fill, List.length_append, List.length_cons]
    rw [Nat.mul_succ]; omega

theorem fill_noQ (sps : List Spec) (c : ℕ) : ∀ I ∈ fill sps c, I.isQ = false := by
  induction sps generalizing c with
  | nil => simp [fill]
  | cons sp sps ih =>
    intro I hI
    simp only [fill, specIns, tIns, List.mem_append, List.mem_map] at hI
    rcases hI with (hI | ⟨ab, _, rfl⟩) | hI
    · split_ifs at hI <;> simp at hI; subst hI; rfl
    · rfl
    · exact ih _ I hI

theorem fill_good (S : ℕ → Prop) (sps : List Spec) (c : ℕ)
    (hs : ∀ sp ∈ sps, ∀ a, SpSrc sp a → a < c ∧ S a) :
    ∀ I ∈ fill sps c, Good A S c (c + sps.length) I := by
  induction sps generalizing c with
  | nil => simp [fill]
  | cons sp sps ih =>
    intro I hI
    simp only [fill, specIns, tIns, List.mem_append, List.mem_map] at hI
    rcases hI with (hI | ⟨ab, hab, rfl⟩) | hI
    · split_ifs at hI <;> simp at hI; subst hI
      refine ⟨le_rfl, by simp [Ins.tgt], fun s hs => ?_⟩; simp [Ins.src] at hs
    · refine ⟨le_rfl, by simp [Ins.tgt], fun s hs' => ?_⟩
      simp only [Ins.src, Ins.tgt] at hs' ⊢
      rcases hs' with rfl | rfl
      · exact hs sp (by simp) _ ⟨ab, hab, Or.inl rfl⟩
      · exact hs sp (by simp) _ ⟨ab, hab, Or.inr rfl⟩
    · have := ih (c + 1) (fun sp' h a ha => by
        have := hs sp' (by simp [h]) a ha; exact ⟨by omega, this.2⟩) I hI
      refine this.mono (by omega) (by simp; omega)

/-! ### Ripple-carry adder (carries left as garbage) -/

def addBit (a b ci c : ℕ) : List Ins :=
  [.cnot a c, .cnot b c, .cnot ci c, .tof a b (c + 1), .tof a ci (c + 1), .tof b ci (c + 1)]

def adder : List ℕ → List ℕ → ℕ → ℕ → List Ins
  | a :: as, b :: bs, ci, c => addBit a b ci c ++ adder as bs (c + 1) (c + 2)
  | _, _, _, _ => []

def adderOut : List ℕ → ℕ → List ℕ
  | [], _ => []
  | _ :: as, c => c :: adderOut as (c + 2)

theorem full_add (a b c : Bool) :
    a.toNat + b.toNat + c.toNat =
      (xor (xor (xor false a) b) c).toNat +
        2 * (xor (xor (xor false (a && b)) (a && c)) (b && c)).toNat := by
  cases a <;> cases b <;> cases c <;> rfl

theorem mod_two_step (s X m : ℕ) (hs : s ≤ 1) :
    (s + 2 * X) % 2 ^ (m + 1) = s + 2 * (X % 2 ^ m) := by
  rw [pow_succ', Nat.mod_mul]
  have h1 : (s + 2 * X) % 2 = s := by omega
  have h2 : (s + 2 * X) / 2 = X := by omega
  rw [h1, h2]

theorem addBit_sem (a b ci c : ℕ) (Z : ℕ → Bool) (ha : a < c) (hb : b < c) (hci : ci < c)
    (h0 : Z c = false) (h1 : Z (c + 1) = false) :
    evalP A O (addBit a b ci c) Z =
      Function.update (Function.update Z c (xor (xor (xor false (Z a)) (Z b)) (Z ci))) (c + 1)
        (xor (xor (xor false (Z a && Z b)) (Z a && Z ci)) (Z b && Z ci)) := by
  have e1 : a ≠ c := by omega
  have e2 : b ≠ c := by omega
  have e3 : ci ≠ c := by omega
  have e4 : a ≠ c + 1 := by omega
  have e5 : b ≠ c + 1 := by omega
  have e6 : ci ≠ c + 1 := by omega
  have e7 : c + 1 ≠ c := by omega
  simp only [addBit, evalP, List.foldl_cons, List.foldl_nil, eval_cnot, eval_tof]
  funext w
  by_cases hw1 : w = c + 1
  · subst hw1
    simp [Function.update_apply, e1, e2, e3, e4, e5, e6, e7, h0, h1]
  · by_cases hw0 : w = c
    · subst hw0
      simp [Function.update_apply, e1, e2, e3, e4, e5, e6, e7, h0, h1]
    · simp [Function.update_apply, hw0, hw1]

theorem adder_sem (As Bs : List ℕ) (hl : Bs.length = As.length) (ci c : ℕ) (Z : ℕ → Bool)
    (hA : ∀ a ∈ As, a < c) (hB : ∀ b ∈ Bs, b < c) (hci : ci < c) (hF : Fresh Z c) :
    (∀ w, w < c → evalP A O (adder As Bs ci c) Z w = Z w) ∧
    Fresh (evalP A O (adder As Bs ci c) Z) (c + 2 * As.length) ∧
    valLE ((adderOut As c).map (evalP A O (adder As Bs ci c) Z)) =
      (valLE (As.map Z) + valLE (Bs.map Z) + (Z ci).toNat) % 2 ^ As.length := by
  induction As generalizing Bs ci c Z with
  | nil =>
    cases Bs with
    | nil => refine ⟨fun _ _ => rfl, by simpa [adder, evalP] using hF, by simp [adderOut, Nat.mod_one]⟩
    | cons _ _ => simp at hl
  | cons a as ih =>
    cases Bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have ha : a < c := hA a (by simp)
      have hb : b < c := hB b (by simp)
      set s := xor (xor (xor false (Z a)) (Z b)) (Z ci)
      set cy := xor (xor (xor false (Z a && Z b)) (Z a && Z ci)) (Z b && Z ci)
      set Z1 := Function.update (Function.update Z c s) (c + 1) cy with hZ1
      have e1 : evalP A O (addBit a b ci c) Z = Z1 :=
        addBit_sem A O a b ci c Z ha hb hci (hF c le_rfl) (hF (c + 1) (by omega))
      have hZ1lt : ∀ w, w < c → Z1 w = Z w := by
        intro w hw
        rw [hZ1, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hF1 : Fresh Z1 (c + 2) := by
        intro w hw
        rw [hZ1, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hF w (by omega)
      obtain ⟨P1, P2, P3⟩ := ih bs hl (c + 1) (c + 2) Z1
        (fun x hx => by have := hA x (by simp [hx]); omega)
        (fun x hx => by have := hB x (by simp [hx]); omega) (by omega) hF1
      have hadd : adder (a :: as) (b :: bs) ci c = addBit a b ci c ++ adder as bs (c + 1) (c + 2) :=
        rfl
      rw [hadd, evalP_append, e1]
      refine ⟨fun w hw => by rw [P1 w (by omega), hZ1lt w hw], ?_, ?_⟩
      · intro w hw; exact P2 w (by simp at hw; omega)
      · have hmapA : as.map Z1 = as.map Z :=
          List.map_congr_left (fun x hx => hZ1lt x (by have := hA x (by simp [hx]); omega))
        have hmapB : bs.map Z1 = bs.map Z :=
          List.map_congr_left (fun x hx => hZ1lt x (by have := hB x (by simp [hx]); omega))
        have hc : evalP A O (adder as bs (c + 1) (c + 2)) Z1 c = s := by
          rw [P1 c (by omega), hZ1, Function.update_of_ne (by omega)]; simp
        have hcy : Z1 (c + 1) = cy := by rw [hZ1]; simp
        simp only [adderOut, List.map_cons, valLE_cons, List.length_cons]
        rw [P3, hc, hmapA, hmapB, hcy]
        have hfa := full_add (Z a) (Z b) (Z ci)
        have hs1 : s.toNat ≤ 1 := Bool.toNat_le s
        rw [show (Z a).toNat + 2 * valLE (as.map Z) + ((Z b).toNat + 2 * valLE (bs.map Z)) +
            (Z ci).toNat = s.toNat + 2 * (valLE (as.map Z) + valLE (bs.map Z) + cy.toNat) by
          simp only [s, cy]; omega]
        exact (mod_two_step _ _ _ hs1).symm

theorem adder_length (As Bs : List ℕ) (ci c : ℕ) : (adder As Bs ci c).length ≤ 6 * As.length := by
  induction As generalizing Bs ci c with
  | nil => cases Bs <;> simp [adder]
  | cons a as ih =>
    cases Bs with
    | nil => simp [adder]
    | cons b bs =>
      have := ih bs (c + 1) (c + 2)
      simp only [adder, addBit, List.length_append, List.length_cons, List.length_nil] at this ⊢
      omega

theorem adder_noQ (As Bs : List ℕ) (ci c : ℕ) : ∀ I ∈ adder As Bs ci c, I.isQ = false := by
  induction As generalizing Bs ci c with
  | nil => cases Bs <;> simp [adder]
  | cons a as ih =>
    cases Bs with
    | nil => simp [adder]
    | cons b bs =>
      intro I hI
      simp only [adder, List.mem_append] at hI
      rcases hI with hI | hI
      · simp [addBit] at hI; rcases hI with h | h | h | h | h | h <;> subst h <;> rfl
      · exact ih bs _ _ I hI

theorem adder_good (S : ℕ → Prop) (As Bs : List ℕ) (ci c : ℕ)
    (hA : ∀ a ∈ As, a < c ∧ S a) (hB : ∀ b ∈ Bs, b < c ∧ S b) (hci : ci < c ∧ S ci)
    (hS : ∀ w, c ≤ w → S w) :
    ∀ I ∈ adder As Bs ci c, Good A S c (c + 2 * As.length) I := by
  induction As generalizing Bs ci c with
  | nil => cases Bs <;> simp [adder]
  | cons a as ih =>
    cases Bs with
    | nil => simp [adder]
    | cons b bs =>
      intro I hI
      have ha := hA a (by simp)
      have hb := hB b (by simp)
      simp only [adder, List.mem_append] at hI
      rcases hI with hI | hI
      · simp [addBit] at hI
        rcases hI with h | h | h | h | h | h <;> subst h <;>
          refine ⟨by simp [Ins.tgt], by simp only [Ins.tgt, List.length_cons]; omega, fun s hs => ?_⟩ <;>
          simp only [Ins.src, Ins.tgt] at hs ⊢ <;>
          first
          | (subst hs; first | exact ⟨by omega, ha.2⟩ | exact ⟨by omega, hb.2⟩ |
              exact ⟨by omega, hci.2⟩)
          | (rcases hs with hs | hs <;> subst hs <;>
              first | exact ⟨by omega, ha.2⟩ | exact ⟨by omega, hb.2⟩ | exact ⟨by omega, hci.2⟩)
      · have := ih bs (c + 1) (c + 2)
          (fun x hx => by have := hA x (by simp [hx]); exact ⟨by omega, this.2⟩)
          (fun x hx => by have := hB x (by simp [hx]); exact ⟨by omega, this.2⟩)
          ⟨by omega, hS _ (by omega)⟩ (fun w hw => hS w (by omega)) I hI
        exact this.mono (by omega) (by simp; omega)

theorem adderOut_length (As : List ℕ) (c : ℕ) : (adderOut As c).length = As.length := by
  induction As generalizing c with
  | nil => rfl
  | cons a as ih => simp [adderOut, ih]

theorem adderOut_bound (As : List ℕ) (c : ℕ) :
    ∀ w ∈ adderOut As c, c ≤ w ∧ w < c + 2 * As.length := by
  induction As generalizing c with
  | nil => simp [adderOut]
  | cons a as ih =>
    intro w hw
    simp only [adderOut, List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp
    · have := ih (c + 2) w hw; simp; omega

end

end

end QuantumLTF.Membership.A2

-- ===== module U3 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

/-! ### Basic spec lists and their values -/

def zSp : Spec := (false, [])
def oSp : Spec := (true, [])
def cpSp (a : ℕ) : Spec := (false, [(a, a)])
def ngSp (a : ℕ) : Spec := (true, [(a, a)])
def anSp (h a : ℕ) : Spec := (false, [(h, a)])
/-- XOR a wire into a spec. -/
def xorD (d : ℕ) (sp : Spec) : Spec := (sp.1, (d, d) :: sp.2)

@[simp] theorem specVal_zSp (Z : ℕ → Bool) : specVal Z zSp = false := rfl
@[simp] theorem specVal_oSp (Z : ℕ → Bool) : specVal Z oSp = true := rfl
@[simp] theorem specVal_cpSp (Z : ℕ → Bool) (a : ℕ) : specVal Z (cpSp a) = Z a := by
  simp [specVal, cpSp]
@[simp] theorem specVal_ngSp (Z : ℕ → Bool) (a : ℕ) : specVal Z (ngSp a) = !Z a := by
  simp [specVal, ngSp]
@[simp] theorem specVal_anSp (Z : ℕ → Bool) (h a : ℕ) : specVal Z (anSp h a) = (Z h && Z a) := by
  simp [specVal, anSp]
@[simp] theorem specVal_xorD (Z : ℕ → Bool) (d : ℕ) (sp : Spec) :
    specVal Z (xorD d sp) = xor (Z d) (specVal Z sp) := by
  obtain ⟨k, ts⟩ := sp
  simp only [specVal, xorD, xl_cons, Bool.and_self]
  cases k <;> cases Z d <;> simp

theorem SpSrc_zSp (a : ℕ) : ¬ SpSrc zSp a := by simp [SpSrc, zSp]
theorem SpSrc_oSp (a : ℕ) : ¬ SpSrc oSp a := by simp [SpSrc, oSp]
theorem SpSrc_cpSp (a b : ℕ) (h : SpSrc (cpSp a) b) : b = a := by
  obtain ⟨ab, hab, h⟩ := h; simp [cpSp] at hab; subst hab; simpa using h
theorem SpSrc_ngSp (a b : ℕ) (h : SpSrc (ngSp a) b) : b = a := by
  obtain ⟨ab, hab, h⟩ := h; simp [ngSp] at hab; subst hab; simpa using h
theorem SpSrc_anSp (h a b : ℕ) (hb : SpSrc (anSp h a) b) : b = h ∨ b = a := by
  obtain ⟨ab, hab, h⟩ := hb; simp [anSp] at hab; subst hab; simpa using h
theorem SpSrc_xorD (d : ℕ) (sp : Spec) (a : ℕ) (h : SpSrc (xorD d sp) a) : a = d ∨ SpSrc sp a := by
  obtain ⟨ab, hab, h⟩ := h
  simp only [xorD, List.mem_cons] at hab
  rcases hab with rfl | hab
  · left; simpa using h
  · right; exact ⟨ab, hab, h⟩

theorem len_zSp : zSp.2.length = 0 := rfl
theorem len_oSp : oSp.2.length = 0 := rfl
theorem len_cpSp (a : ℕ) : (cpSp a).2.length = 1 := rfl
theorem len_ngSp (a : ℕ) : (ngSp a).2.length = 1 := rfl
theorem len_anSp (h a : ℕ) : (anSp h a).2.length = 1 := rfl
theorem len_xorD (d : ℕ) (sp : Spec) : (xorD d sp).2.length = sp.2.length + 1 := by
  simp [xorD]

theorem valLE_append (L M : List Bool) : valLE (L ++ M) = valLE L + 2 ^ L.length * valLE M := by
  induction L with
  | nil => simp
  | cons b L ih => simp [ih, pow_succ]; ring

theorem valLE_replicate_false (k : ℕ) : valLE (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

theorem valLE_replicate_true (k : ℕ) : valLE (List.replicate k true) + 1 = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, pow_succ]; omega

theorem valLE_map_not (L : List Bool) : valLE (L.map (!·)) + valLE L + 1 = 2 ^ L.length := by
  induction L with
  | nil => rfl
  | cons b L ih => cases b <;> simp [pow_succ] <;> omega

theorem valLE_map_and (L : List Bool) (h : Bool) :
    valLE (L.map (h && ·)) = if h then valLE L else 0 := by
  cases h
  · simp only [Bool.false_and, if_false]
    rw [show L.map (fun _ => false) = List.replicate L.length false by
      simp [List.map_const']]
    exact valLE_replicate_false _
  · simp

theorem valLE_map_xor (L : List Bool) (d : Bool) :
    valLE (L.map (xor d)) + d.toNat + (if d then valLE L else 0) =
      (if d then 2 ^ L.length else valLE L) := by
  cases d
  · have e : L.map (xor false) = L := by
      induction L with
      | nil => rfl
      | cons b L ih => simp [ih]
    simp [e]
  · have e : L.map (xor true) = L.map (!·) := by
      apply List.map_congr_left; intro b _; cases b <;> rfl
    have := valLE_map_not L
    simp only [e, if_true, Bool.toNat_true]
    omega

/-! ### Register lists (least significant wire first) -/

/-- The wires `base, …, base + len - 1` of a register stored most significant first, listed
least significant first. -/
def regLE (base len : ℕ) : List ℕ := ((List.range len).map (fun j => j + base)).reverse

theorem regLE_length (base len : ℕ) : (regLE base len).length = len := by simp [regLE]

theorem regLE_mem (base len a : ℕ) (h : a ∈ regLE base len) : base ≤ a ∧ a < base + len := by
  simp only [regLE, List.mem_reverse, List.mem_map, List.mem_range] at h
  obtain ⟨j, hj, rfl⟩ := h; omega

theorem regLE_succ (base len : ℕ) : regLE base (len + 1) = regLE (base + 1) len ++ [base] := by
  simp only [regLE, List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons]
  congr 2
  all_goals (try simp)
  all_goals (intros; omega)

theorem valLE_regLE (base len : ℕ) (Z : ℕ → Bool) (q : Qubits len)
    (hq : ∀ j : Fin len, q j = Z (base + j)) :
    bitsToNat q = valLE ((regLE base len).map Z) := by
  induction len generalizing base with
  | zero => simp [bitsToNat, regLE]
  | succ len ih =>
    have e1 : bitsToNat q = (q 0).toNat * 2 ^ len + bitsToNat (fun j : Fin len => q j.succ) := by
      unfold bitsToNat
      rw [Fin.sum_univ_succ]
      congr 1
      · simp only [Fin.val_zero]; cases q 0 <;> simp
      · apply Finset.sum_congr rfl; intro j _; simp only [Fin.val_succ]
        congr 2; omega
    rw [e1, ih (base + 1) (fun j => q j.succ) (fun j => by rw [hq]; simp; ring_nf), regLE_succ,
      List.map_append, valLE_append]
    simp only [List.map_append, List.map_cons, List.map_nil, valLE_cons, valLE_nil, mul_zero,
      add_zero, List.length_map, regLE_length, hq 0, Fin.val_zero]
    ring

/-! ### Spec families -/

def constSpecs : ℕ → ℕ → List Spec
  | _, 0 => []
  | K, len + 1 => (decide (K % 2 = 1), []) :: constSpecs (K / 2) len

theorem constSpecs_length (K len : ℕ) : (constSpecs K len).length = len := by
  induction len generalizing K with
  | zero => rfl
  | succ len ih => simp [constSpecs, ih]

theorem constSpecs_val (Z : ℕ → Bool) (K len : ℕ) :
    valLE ((constSpecs K len).map (specVal Z)) = K % 2 ^ len := by
  induction len generalizing K with
  | zero => simp [constSpecs, Nat.mod_one]
  | succ len ih =>
    simp only [constSpecs, List.map_cons, valLE_cons, ih]
    rw [pow_succ', Nat.mod_mul]
    congr 1
    simp only [specVal, xl_nil, Bool.xor_false]
    rcases Nat.mod_two_eq_zero_or_one K with h | h <;> simp [h]

theorem constSpecs_src (K len : ℕ) : ∀ sp ∈ constSpecs K len, ∀ a, ¬ SpSrc sp a := by
  induction len generalizing K with
  | zero => simp [constSpecs]
  | succ len ih =>
    intro sp hsp a ha
    simp only [constSpecs, List.mem_cons] at hsp
    rcases hsp with rfl | h
    · obtain ⟨ab, hab, _⟩ := ha; simp at hab
    · exact ih _ sp h a ha

theorem constSpecs_terms (K len : ℕ) : ∀ sp ∈ constSpecs K len, sp.2.length = 0 := by
  induction len generalizing K with
  | zero => simp [constSpecs]
  | succ len ih =>
    intro sp hsp
    simp only [constSpecs, List.mem_cons] at hsp
    rcases hsp with rfl | h
    · rfl
    · exact ih _ sp h

def copySpecs (R : List ℕ) : List Spec := R.map cpSp
def notSpecs (R : List ℕ) : List Spec := R.map ngSp
def andSpecs (h : ℕ) (R : List ℕ) : List Spec := R.map (anSp h)

theorem copySpecs_map (Z : ℕ → Bool) (R : List ℕ) : (copySpecs R).map (specVal Z) = R.map Z := by
  simp [copySpecs, Function.comp_def]

theorem notSpecs_val (Z : ℕ → Bool) (R : List ℕ) :
    valLE ((notSpecs R).map (specVal Z)) + valLE (R.map Z) + 1 = 2 ^ R.length := by
  have := valLE_map_not (R.map Z)
  simp only [List.length_map, List.map_map] at this
  simpa [notSpecs, Function.comp_def] using this

theorem andSpecs_val (Z : ℕ → Bool) (h : ℕ) (R : List ℕ) :
    valLE ((andSpecs h R).map (specVal Z)) = if Z h then valLE (R.map Z) else 0 := by
  have := valLE_map_and (R.map Z) (Z h)
  simp only [List.map_map] at this
  simpa [andSpecs, Function.comp_def] using this

/-- Shift a spec list up by `o` positions inside a register of `w` bits (zero padding). -/
def shiftSp (o w : ℕ) (sps : List Spec) : List Spec :=
  List.replicate o zSp ++ sps ++ List.replicate (w - o - sps.length) zSp

theorem shiftSp_length (o w : ℕ) (sps : List Spec) (h : o + sps.length ≤ w) :
    (shiftSp o w sps).length = w := by
  simp [shiftSp]; omega

theorem shiftSp_val (Z : ℕ → Bool) (o w : ℕ) (sps : List Spec) :
    valLE ((shiftSp o w sps).map (specVal Z)) = 2 ^ o * valLE (sps.map (specVal Z)) := by
  simp only [shiftSp, List.map_append, List.map_replicate, specVal_zSp]
  rw [valLE_append, valLE_append, valLE_replicate_false, valLE_replicate_false]
  simp

theorem shiftSp_src (o w : ℕ) (sps : List Spec) (a : ℕ) (sp : Spec) (hsp : sp ∈ shiftSp o w sps)
    (ha : SpSrc sp a) : ∃ sp' ∈ sps, SpSrc sp' a := by
  simp only [shiftSp, List.mem_append, List.mem_replicate] at hsp
  rcases hsp with (⟨_, rfl⟩ | h) | ⟨_, rfl⟩
  · exact absurd ha (SpSrc_zSp a)
  · exact ⟨sp, h, ha⟩
  · exact absurd ha (SpSrc_zSp a)

theorem shiftSp_terms (o w k : ℕ) (sps : List Spec) (h : ∀ sp ∈ sps, sp.2.length ≤ k) :
    ∀ sp ∈ shiftSp o w sps, sp.2.length ≤ k := by
  intro sp hsp
  simp only [shiftSp, List.mem_append, List.mem_replicate] at hsp
  rcases hsp with (⟨_, rfl⟩ | h') | ⟨_, rfl⟩
  · simp [zSp]
  · exact h sp h'
  · simp [zSp]

/-- Two's complement (in `w` bits) of `2^e · (2N - 2^len)`, where `N` is the value of the
register `R` (listed least significant first, `len = R.length`). Requires `e + len + 1 ≤ w`. -/
def sgnSpecs (R : List ℕ) (e w : ℕ) : List Spec :=
  if h : R = [] then List.replicate e zSp ++ List.replicate (w - e) oSp
  else List.replicate e zSp ++ (zSp :: copySpecs R.dropLast) ++
    List.replicate (w - e - R.length) (ngSp (R.getLast h))

theorem sgnSpecs_length (R : List ℕ) (e w : ℕ) (h : e + R.length + 1 ≤ w) :
    (sgnSpecs R e w).length = w := by
  unfold sgnSpecs
  split_ifs with hR
  · simp; omega
  · simp [copySpecs]
    have : R.length ≠ 0 := by simpa using hR
    omega

theorem sgnSpecs_val (Z : ℕ → Bool) (R : List ℕ) (e w : ℕ) (h : e + R.length + 1 ≤ w) :
    ((valLE ((sgnSpecs R e w).map (specVal Z)) : ℕ) : ℤ) ≡
      2 ^ e * (2 * (valLE (R.map Z) : ℤ) - 2 ^ R.length) [ZMOD 2 ^ w] := by
  unfold sgnSpecs
  split_ifs with hR
  · subst hR
    simp only [List.map_append, List.map_replicate, specVal_zSp, specVal_oSp, List.map_nil,
      valLE_nil, List.length_nil, pow_zero]
    rw [valLE_append, valLE_replicate_false, List.length_replicate]
    have h1 := valLE_replicate_true (w - e)
    have h2 : (2 : ℤ) ^ w = 2 ^ e * 2 ^ (w - e) := by rw [← pow_add]; congr 1; omega
    apply Int.ModEq.symm
    rw [Int.modEq_iff_dvd]
    refine ⟨1, ?_⟩
    have h1' : ((valLE (List.replicate (w - e) true) : ℕ) : ℤ) = 2 ^ (w - e) - 1 := by
      have : ((valLE (List.replicate (w - e) true) + 1 : ℕ) : ℤ) = ((2 ^ (w - e) : ℕ) : ℤ) := by
        rw [h1]
      push_cast at this; linarith
    push_cast
    rw [h1', h2]; ring
  · obtain ⟨L, m, rfl⟩ : ∃ L m, R = L ++ [m] := ⟨R.dropLast, R.getLast hR,
      (List.dropLast_append_getLast hR).symm⟩
    simp only [List.length_append, List.length_singleton] at h
    simp only [List.dropLast_concat, List.getLast_append_singleton]
    simp only [List.map_append, List.map_replicate, List.map_cons, specVal_zSp, specVal_ngSp,
      copySpecs_map, List.length_append, List.length_singleton, List.map_nil]
    simp only [valLE_append, valLE_cons, valLE_nil, valLE_replicate_false, List.length_append,
      List.length_replicate, List.length_cons, List.length_map, Bool.toNat_false, zero_add,
      mul_zero, add_zero]
    set k := w - e - (L.length + 1) with hk
    have hw : w = e + (L.length + 1) + k := by omega
    cases hm : Z m
    · simp only [Bool.not_false]
      have h1 := valLE_replicate_true k
      have h1' : ((valLE (List.replicate k true) : ℕ) : ℤ) = 2 ^ k - 1 := by
        have : ((valLE (List.replicate k true) + 1 : ℕ) : ℤ) = ((2 ^ k : ℕ) : ℤ) := by rw [h1]
        push_cast at this; linarith
      apply Int.ModEq.symm
      rw [Int.modEq_iff_dvd]
      refine ⟨1, ?_⟩
      push_cast
      rw [h1', hw]
      simp only [Bool.toNat_false, Nat.cast_zero, pow_add, pow_succ]
      ring
    · simp only [Bool.not_true, valLE_replicate_false]
      apply Int.ModEq.symm
      rw [Int.modEq_iff_dvd]
      refine ⟨0, ?_⟩
      push_cast
      simp only [Bool.toNat_true, Nat.cast_one, pow_add, pow_succ]
      ring

theorem sgnSpecs_src (R : List ℕ) (e w : ℕ) :
    ∀ sp ∈ sgnSpecs R e w, ∀ a, SpSrc sp a → a ∈ R := by
  intro sp hsp a ha
  unfold sgnSpecs at hsp
  split_ifs at hsp with hR
  · simp only [List.mem_append, List.mem_replicate] at hsp
    rcases hsp with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact absurd ha (SpSrc_zSp a)
    · exact absurd ha (SpSrc_oSp a)
  · simp only [List.mem_append, List.mem_replicate, List.mem_cons, copySpecs, List.mem_map]
      at hsp
    rcases hsp with (⟨_, rfl⟩ | rfl | ⟨b, hb, rfl⟩) | ⟨_, rfl⟩
    · exact absurd ha (SpSrc_zSp a)
    · exact absurd ha (SpSrc_zSp a)
    · rw [SpSrc_cpSp _ _ ha]; exact List.mem_of_mem_dropLast hb
    · rw [SpSrc_ngSp _ _ ha]; exact List.getLast_mem hR

theorem sgnSpecs_terms (R : List ℕ) (e w : ℕ) : ∀ sp ∈ sgnSpecs R e w, sp.2.length ≤ 1 := by
  intro sp hsp
  unfold sgnSpecs at hsp
  split_ifs at hsp with hR
  · simp only [List.mem_append, List.mem_replicate] at hsp
    rcases hsp with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [zSp, oSp]
  · simp only [List.mem_append, List.mem_replicate, List.mem_cons, copySpecs, List.mem_map]
      at hsp
    rcases hsp with (⟨_, rfl⟩ | rfl | ⟨b, hb, rfl⟩) | ⟨_, rfl⟩ <;> simp [zSp, cpSp, ngSp]

/-! ### Adding a spec register to a register -/

section
variable (A : ℕ) (O : Qubits A → Bool)

/-- `R + sps + ci` (carry-in wire `ci`), result on the wires `addOutC R c`. -/
def addSpecCi (R : List ℕ) (sps : List Spec) (ci c : ℕ) : List Ins :=
  fill sps c ++ adder R (List.range' c R.length) ci (c + R.length)

def addOutC (R : List ℕ) (c : ℕ) : List ℕ := adderOut R (c + R.length)

theorem addSpecCi_sem (R : List ℕ) (sps : List Spec) (ci c : ℕ) (Z : ℕ → Bool)
    (hl : sps.length = R.length) (hR : ∀ a ∈ R, a < c) (hci : ci < c) (hs : SrcLt sps c)
    (hF : Fresh Z c) :
    (∀ w, w < c → evalP A O (addSpecCi R sps ci c) Z w = Z w) ∧
    Fresh (evalP A O (addSpecCi R sps ci c) Z) (c + 3 * R.length) ∧
    valLE ((addOutC R c).map (evalP A O (addSpecCi R sps ci c) Z)) =
      (valLE (R.map Z) + valLE (sps.map (specVal Z)) + (Z ci).toNat) % 2 ^ R.length := by
  obtain ⟨F1, F2, _⟩ := fill_sem A O sps c Z hF hs
  have Fm := fill_map A O sps c Z hF hs
  rw [hl] at F2 Fm
  set Z1 := evalP A O (fill sps c) Z
  obtain ⟨G1, G2, G3⟩ := adder_sem A O R (List.range' c R.length) (by simp) ci
    (c + R.length) Z1 (fun a ha => by have := hR a ha; omega)
    (fun b hb => by simp [List.mem_range'] at hb; omega) (by omega)
    (fun w hw => F2 w (by omega))
  simp only [addSpecCi, evalP_append]
  refine ⟨fun w hw => by rw [G1 w (by omega), F1 w hw], fun w hw => G2 w (by omega), ?_⟩
  rw [addOutC, G3, Fm, F1 ci hci]
  have : R.map Z1 = R.map Z := List.map_congr_left (fun a ha => F1 a (hR a ha))
  rw [this]

theorem addSpecCi_good (S : ℕ → Prop) (R : List ℕ) (sps : List Spec) (ci c : ℕ)
    (hl : sps.length = R.length) (hR : ∀ a ∈ R, a < c ∧ S a) (hci : ci < c ∧ S ci)
    (hs : ∀ sp ∈ sps, ∀ a, SpSrc sp a → a < c ∧ S a) (hS : ∀ w, c ≤ w → S w) :
    ∀ I ∈ addSpecCi R sps ci c, Good A S c (c + 3 * R.length) I := by
  intro I hI
  simp only [addSpecCi, List.mem_append] at hI
  rcases hI with hI | hI
  · exact (fill_good A S sps c hs I hI).mono le_rfl (by omega)
  · have := adder_good A S R (List.range' c R.length) ci (c + R.length)
      (fun a ha => by have := hR a ha; exact ⟨by omega, this.2⟩)
      (fun b hb => by simp [List.mem_range'] at hb; exact ⟨by omega, hS b (by omega)⟩)
      ⟨by omega, hci.2⟩ (fun w hw => hS w (by omega)) I hI
    exact this.mono (by omega) (by omega)

theorem addSpecCi_noQ (R : List ℕ) (sps : List Spec) (ci c : ℕ) :
    ∀ I ∈ addSpecCi R sps ci c, I.isQ = false := by
  intro I hI
  simp only [addSpecCi, List.mem_append] at hI
  rcases hI with hI | hI
  · exact fill_noQ sps c I hI
  · exact adder_noQ R _ _ _ I hI

theorem addSpecCi_length (R : List ℕ) (sps : List Spec) (ci c k : ℕ)
    (hl : sps.length = R.length) (hk : ∀ sp ∈ sps, sp.2.length ≤ k) :
    (addSpecCi R sps ci c).length ≤ (k + 7) * R.length := by
  have h1 := fill_length sps k hk c
  have h2 := adder_length R (List.range' c R.length) ci (c + R.length)
  rw [hl] at h1
  simp only [addSpecCi, List.length_append]; nlinarith

theorem addOutC_length (R : List ℕ) (c : ℕ) : (addOutC R c).length = R.length :=
  adderOut_length _ _

theorem addOutC_bound (R : List ℕ) (c : ℕ) :
    ∀ w ∈ addOutC R c, c ≤ w ∧ w < c + 3 * R.length := by
  intro w hw
  have := adderOut_bound R _ w hw
  omega

/-! ### Accumulating a list of spec terms onto a constant -/

/-- Starting from the register `R`, add the spec registers `ts` one by one (zero carry-in: the
carry-in wire is the reserved fresh wire `c`). -/
def accP : List ℕ → List (List Spec) → ℕ → List Ins
  | _, [], _ => []
  | R, t :: ts, c => addSpecCi R t c (c + 1) ++
      accP (addOutC R (c + 1)) ts (c + 1 + 3 * R.length)

def accOut : List ℕ → List (List Spec) → ℕ → List ℕ
  | R, [], _ => R
  | R, _ :: ts, c => accOut (addOutC R (c + 1)) ts (c + 1 + 3 * R.length)

theorem accOut_length (R : List ℕ) (ts : List (List Spec)) (c : ℕ) :
    (accOut R ts c).length = R.length := by
  induction ts generalizing R c with
  | nil => rfl
  | cons t ts ih => simp only [accOut]; rw [ih, addOutC_length]

theorem accOut_bound (R : List ℕ) (ts : List (List Spec)) (c : ℕ) :
    ∀ a ∈ accOut R ts c, a ∈ R ∨ (c ≤ a ∧ a < c + ts.length * (3 * R.length + 1)) := by
  induction ts generalizing R c with
  | nil => intro a ha; exact Or.inl ha
  | cons t ts ih =>
    intro a ha
    simp only [accOut] at ha
    rcases ih _ _ a ha with h | h
    · have := addOutC_bound R (c + 1) a h; right
      simp only [List.length_cons]; constructor
      · omega
      · nlinarith
    · rw [addOutC_length] at h; right
      simp only [List.length_cons]; constructor
      · omega
      · nlinarith

def sumV (Z : ℕ → Bool) : List (List Spec) → ℕ
  | [] => 0
  | t :: ts => valLE (t.map (specVal Z)) + sumV Z ts

theorem accP_sem (Z0 : ℕ → Bool) (c0 : ℕ) (R : List ℕ) (ts : List (List Spec)) (c : ℕ)
    (Z : ℕ → Bool) (hc : c0 ≤ c)
    (hl : ∀ t ∈ ts, t.length = R.length) (hR : ∀ a ∈ R, a < c)
    (hs : ∀ t ∈ ts, SrcLt t c0) (hZ : ∀ w, w < c0 → Z w = Z0 w) (hF : Fresh Z c) :
    (∀ w, w < c → evalP A O (accP R ts c) Z w = Z w) ∧
    Fresh (evalP A O (accP R ts c) Z) (c + ts.length * (3 * R.length + 1)) ∧
    valLE ((accOut R ts c).map (evalP A O (accP R ts c) Z)) =
      (valLE (R.map Z) + sumV Z0 ts) % 2 ^ R.length := by
  induction ts generalizing R c Z with
  | nil =>
    refine ⟨fun _ _ => rfl, by simp only [List.length_nil, zero_mul, add_zero]; exact hF, ?_⟩
    simp only [accOut, accP, evalP_nil, sumV, add_zero]
    symm; apply Nat.mod_eq_of_lt
    have := valLE_lt (R.map Z); simpa using this
  | cons t ts ih =>
    have ht := hl t (by simp)
    have hst : SrcLt t (c + 1) := fun sp hsp a ha => by
      have := hs t (by simp) sp hsp a ha; omega
    obtain ⟨A1, A2, A3⟩ := addSpecCi_sem A O R t c (c + 1) Z ht
      (fun a ha => by have := hR a ha; omega) (by omega) hst (fun w hw => hF w (by omega))
    set Z1 := evalP A O (addSpecCi R t c (c + 1)) Z
    have hZ1 : ∀ w, w < c0 → Z1 w = Z0 w := fun w hw => by rw [A1 w (by omega), hZ w hw]
    obtain ⟨B1, B2, B3⟩ := ih (addOutC R (c + 1)) (c + 1 + 3 * R.length) Z1 (by omega)
      (fun t' h => by rw [addOutC_length]; exact hl t' (by simp [h]))
      (fun a ha => by have := addOutC_bound R (c + 1) a ha; omega)
      (fun t' h => hs t' (by simp [h])) hZ1 A2
    simp only [accP, accOut, evalP_append]
    refine ⟨fun w hw => by rw [B1 w (by omega), A1 w (by omega)], ?_, ?_⟩
    · intro w hw; apply B2; simp only [List.length_cons, addOutC_length] at hw ⊢; nlinarith
    · rw [B3, addOutC_length]
      have hmap : (addOutC R (c + 1)).map Z1 = (addOutC R (c + 1)).map Z1 := rfl
      rw [A3, hF c le_rfl]
      have hv : valLE (t.map (specVal Z)) = valLE (t.map (specVal Z0)) := by
        congr 1; apply List.map_congr_left; intro sp hsp
        apply specVal_congr; intro a ha; exact hZ a (hs t (by simp) sp hsp a ha)
      simp only [sumV, hv, Bool.toNat_false, add_zero, Nat.mod_add_mod]
      ring_nf

theorem accP_good (S : ℕ → Prop) (R : List ℕ) (ts : List (List Spec)) (c : ℕ)
    (hl : ∀ t ∈ ts, t.length = R.length) (hR : ∀ a ∈ R, a < c ∧ S a)
    (hs : ∀ t ∈ ts, ∀ sp ∈ t, ∀ a, SpSrc sp a → a < c ∧ S a) (hS : ∀ w, c ≤ w → S w) :
    ∀ I ∈ accP R ts c, Good A S c (c + ts.length * (3 * R.length + 1)) I := by
  induction ts generalizing R c with
  | nil => simp [accP]
  | cons t ts ih =>
    intro I hI
    simp only [accP, List.mem_append] at hI
    rcases hI with hI | hI
    · have := addSpecCi_good A S R t c (c + 1) (hl t (by simp))
        (fun a ha => by have := hR a ha; exact ⟨by omega, this.2⟩) ⟨by omega, hS c le_rfl⟩
        (fun sp hsp a ha => by have := hs t (by simp) sp hsp a ha; exact ⟨by omega, this.2⟩)
        (fun w hw => hS w (by omega)) I hI
      refine this.mono (by omega) ?_
      simp only [List.length_cons]; nlinarith
    · have := ih (addOutC R (c + 1)) (c + 1 + 3 * R.length)
        (fun t' h => by rw [addOutC_length]; exact hl t' (by simp [h]))
        (fun a ha => by have := addOutC_bound R (c + 1) a ha; exact ⟨by omega, hS a (by omega)⟩)
        (fun t' h sp hsp a ha => by
          have := hs t' (by simp [h]) sp hsp a ha; exact ⟨by omega, this.2⟩)
        (fun w hw => hS w (by omega)) I hI
      rw [addOutC_length] at this
      refine this.mono (by omega) ?_
      simp only [List.length_cons]; nlinarith

theorem accP_noQ (R : List ℕ) (ts : List (List Spec)) (c : ℕ) :
    ∀ I ∈ accP R ts c, I.isQ = false := by
  induction ts generalizing R c with
  | nil => simp [accP]
  | cons t ts ih =>
    intro I hI
    simp only [accP, List.mem_append] at hI
    rcases hI with hI | hI
    · exact addSpecCi_noQ R t _ _ I hI
    · exact ih _ _ I hI

theorem accP_length (R : List ℕ) (ts : List (List Spec)) (c k : ℕ)
    (hl : ∀ t ∈ ts, t.length = R.length) (hk : ∀ t ∈ ts, ∀ sp ∈ t, sp.2.length ≤ k) :
    (accP R ts c).length ≤ ts.length * ((k + 7) * R.length) := by
  induction ts generalizing R c with
  | nil => simp [accP]
  | cons t ts ih =>
    have h1 := addSpecCi_length R t c (c + 1) k (hl t (by simp)) (hk t (by simp))
    have h2 := ih (addOutC R (c + 1)) (c + 1 + 3 * R.length)
      (fun t' h => by rw [addOutC_length]; exact hl t' (by simp [h]))
      (fun t' h => hk t' (by simp [h]))
    rw [addOutC_length] at h2
    simp only [accP, List.length_append, List.length_cons]
    nlinarith

end

end

end QuantumLTF.Membership.A2

-- ===== module U4 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

theorem copySpecs_src' (R : List ℕ) : ∀ sp ∈ copySpecs R, ∀ a, SpSrc sp a → a ∈ R := by
  intro sp hsp a ha
  simp only [copySpecs, List.mem_map] at hsp
  obtain ⟨b, hb, rfl⟩ := hsp
  rw [SpSrc_cpSp _ _ ha]; exact hb

theorem valLE_replicate_append (o : ℕ) (L : List Bool) :
    valLE (List.replicate o false ++ L) = 2 ^ o * valLE L := by
  rw [valLE_append, valLE_replicate_false]; simp

section
variable (A : ℕ) (O : Qubits A → Bool)

/-! ### Copying registers (most significant bit first) into a block -/

def copyRegs : List (List ℕ) → ℕ → List Ins
  | [], _ => []
  | R :: Rs, c => fill (copySpecs R.reverse) c ++ copyRegs Rs (c + R.length)

theorem copyRegs_sem (ℓ : ℕ) (Rs : List (List ℕ)) (hl : ∀ R ∈ Rs, R.length = ℓ) (c : ℕ)
    (Z : ℕ → Bool) (hR : ∀ R ∈ Rs, ∀ a ∈ R, a < c) (hF : Fresh Z c) :
    (∀ w, w < c → evalP A O (copyRegs Rs c) Z w = Z w) ∧
    Fresh (evalP A O (copyRegs Rs c) Z) (c + ℓ * Rs.length) ∧
    ∀ i, i < Rs.length → ∀ m, m < ℓ →
      evalP A O (copyRegs Rs c) Z (c + ℓ * i + m) = Z ((Rs.getD i []).reverse.getD m 0) := by
  induction Rs generalizing c Z with
  | nil => exact ⟨fun _ _ => rfl, by simpa [copyRegs, evalP] using hF, fun i hi => by simp at hi⟩
  | cons R Rs ih =>
    have hRl : R.length = ℓ := hl R (by simp)
    have hs : SrcLt (copySpecs R.reverse) c := by
      intro sp hsp a ha
      have := copySpecs_src' R.reverse sp hsp a ha
      exact hR R (by simp) a (List.mem_reverse.mp this)
    simp only [copyRegs, evalP_append]
    rw [hRl]
    obtain ⟨F1, F2, F3⟩ := fill_sem A O (copySpecs R.reverse) c Z hF hs
    have hlen : (copySpecs R.reverse).length = ℓ := by simp [copySpecs, hRl]
    rw [hlen] at F2
    set Z1 := evalP A O (fill (copySpecs R.reverse) c) Z
    obtain ⟨G1, G2, G3⟩ := ih (fun R' h => hl R' (by simp [h])) (c + ℓ) Z1
      (fun R' h a ha => by have := hR R' (by simp [h]) a ha; omega)
      (fun w hw => F2 w (by omega))
    refine ⟨fun w hw => by rw [G1 w (by omega), F1 w hw], fun w hw => G2 w (by
      simp at hw; rw [mul_add] at hw; omega), ?_⟩
    intro i hi m hm
    cases i with
    | zero =>
      rw [G1 _ (by omega)]
      simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero]
      rw [F3 m (by rw [hlen]; exact hm)]
      have hm' : m < R.reverse.length := by simp [hRl, hm]
      rw [List.getD_eq_getElem _ _ hm']
      simp [copySpecs]
    | succ i =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      rw [show c + ℓ * (i + 1) + m = c + ℓ + ℓ * i + m by ring, G3 i hi m hm]
      simp only [List.getD_cons_succ]
      apply F1
      have hmem : (Rs.getD i []) ∈ Rs := by
        rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      have hm2 : m < ((Rs.getD i []).reverse).length := by
        rw [List.length_reverse, hl _ (List.mem_cons_of_mem _ hmem)]; exact hm
      rw [List.getD_eq_getElem _ _ hm2]
      exact hR _ (List.mem_cons_of_mem _ hmem) _ (List.mem_reverse.mp (List.getElem_mem hm2))

theorem copyRegs_good (S : ℕ → Prop) (ℓ : ℕ) (Rs : List (List ℕ))
    (hl : ∀ R ∈ Rs, R.length = ℓ) (c : ℕ) (hR : ∀ R ∈ Rs, ∀ a ∈ R, a < c ∧ S a) :
    ∀ I ∈ copyRegs Rs c, Good A S c (c + ℓ * Rs.length) I := by
  induction Rs generalizing c with
  | nil => simp [copyRegs]
  | cons R Rs ih =>
    have hRl : R.length = ℓ := hl R (by simp)
    intro I hI
    simp only [copyRegs, List.mem_append] at hI
    rcases hI with hI | hI
    · have := fill_good A S (copySpecs R.reverse) c (fun sp hsp a ha =>
        hR R (by simp) a (List.mem_reverse.mp (copySpecs_src' R.reverse sp hsp a ha))) I hI
      refine this.mono le_rfl ?_
      simp [copySpecs, hRl, mul_add]
    · have := ih (fun R' h => hl R' (by simp [h])) (c + R.length)
        (fun R' h a ha => by have := hR R' (by simp [h]) a ha; exact ⟨by omega, this.2⟩) I hI
      refine this.mono (by omega) ?_
      simp [hRl, mul_add]; omega

theorem copyRegs_noQ (Rs : List (List ℕ)) (c : ℕ) : ∀ I ∈ copyRegs Rs c, I.isQ = false := by
  induction Rs generalizing c with
  | nil => simp [copyRegs]
  | cons R Rs ih =>
    intro I hI
    simp only [copyRegs, List.mem_append] at hI
    rcases hI with hI | hI
    · exact fill_noQ _ _ I hI
    · exact ih _ I hI

theorem copyRegs_length (ℓ : ℕ) (Rs : List (List ℕ)) (hl : ∀ R ∈ Rs, R.length = ℓ) (c : ℕ) :
    (copyRegs Rs c).length ≤ 2 * ℓ * Rs.length := by
  induction Rs generalizing c with
  | nil => simp [copyRegs]
  | cons R Rs ih =>
    have := ih (fun R' h => hl R' (by simp [h])) (c + R.length)
    have h2 := fill_length (copySpecs R.reverse) 1 (fun sp hsp => by
      simp only [copySpecs, List.mem_map] at hsp; obtain ⟨b, _, rfl⟩ := hsp; simp [cpSp]) c
    have h3 : (copySpecs R.reverse).length = ℓ := by simp [copySpecs, hl R (by simp)]
    rw [h3] at h2
    simp only [copyRegs, List.length_append, List.length_cons]
    rw [mul_add]; omega

/-! ### Updating all tracks by `± δ` (carry-in and XOR mask from the answer wire `d`) -/

def updP (d : ℕ) (δ : ℕ → ℕ → List Spec) (m : ℕ) : ℕ → List (List ℕ) → ℕ → List Ins
  | _, [], _ => []
  | j, R :: Rs, c => addSpecCi R ((δ j m).map (xorD d)) d c ++
      updP d δ m (j + 1) Rs (c + 3 * R.length)

def updT : List (List ℕ) → ℕ → List (List ℕ)
  | [], _ => []
  | R :: Rs, c => addOutC R c :: updT Rs (c + 3 * R.length)

def updE : List (List ℕ) → ℕ → ℕ
  | [], c => c
  | R :: Rs, c => updE Rs (c + 3 * R.length)

theorem updE_ge (Rs : List (List ℕ)) (c : ℕ) : c ≤ updE Rs c := by
  induction Rs generalizing c with
  | nil => exact le_rfl
  | cons R Rs ih => exact le_trans (by omega) (ih _)

theorem updT_length (Rs : List (List ℕ)) (c : ℕ) : (updT Rs c).length = Rs.length := by
  induction Rs generalizing c with
  | nil => rfl
  | cons R Rs ih => simp [updT, ih]

theorem updT_getD_length (Rs : List (List ℕ)) (c t : ℕ) :
    ((updT Rs c).getD t []).length = (Rs.getD t []).length := by
  induction Rs generalizing c t with
  | nil => simp [updT]
  | cons R Rs ih =>
    cases t with
    | zero => simp [updT, addOutC_length]
    | succ t => simp only [updT, List.getD_cons_succ]; exact ih _ _

theorem updT_bound (Rs : List (List ℕ)) (c : ℕ) :
    ∀ R ∈ updT Rs c, ∀ w ∈ R, c ≤ w ∧ w < updE Rs c := by
  induction Rs generalizing c with
  | nil => simp [updT]
  | cons R Rs ih =>
    intro R' hR' w hw
    simp only [updT, List.mem_cons] at hR'
    rcases hR' with rfl | h
    · have := addOutC_bound R c w hw
      have := updE_ge Rs (c + 3 * R.length)
      simp only [updE]; omega
    · have := ih _ R' h w hw
      simp only [updE]; omega

theorem updT_len (Rs : List (List ℕ)) (c : ℕ) :
    ∀ R ∈ updT Rs c, ∃ R0 ∈ Rs, R.length = R0.length := by
  induction Rs generalizing c with
  | nil => simp [updT]
  | cons R Rs ih =>
    intro R' hR'
    simp only [updT, List.mem_cons] at hR'
    rcases hR' with rfl | h
    · exact ⟨R, by simp, addOutC_length _ _⟩
    · obtain ⟨R0, h0, e⟩ := ih _ R' h
      exact ⟨R0, by simp [h0], e⟩

theorem updT_take (n : ℕ) (Rs : List (List ℕ)) (c : ℕ) :
    ∀ R ∈ (updT Rs c).take n, ∃ R0 ∈ Rs.take n, R.length = R0.length := by
  induction Rs generalizing c n with
  | nil => simp [updT]
  | cons R Rs ih =>
    intro R' hR'
    cases n with
    | zero => simp at hR'
    | succ n =>
      simp only [updT, List.take_succ_cons, List.mem_cons] at hR'
      rcases hR' with rfl | h
      · exact ⟨R, by simp, addOutC_length _ _⟩
      · obtain ⟨R0, h0, e⟩ := ih n _ R' h
        exact ⟨R0, by simp [h0], e⟩

theorem updE_le (Lm : ℕ) (Rs : List (List ℕ)) (hl : ∀ R ∈ Rs, R.length ≤ Lm) (c : ℕ) :
    updE Rs c ≤ c + 3 * Lm * Rs.length := by
  induction Rs generalizing c with
  | nil => simp [updE]
  | cons R Rs ih =>
    have := ih (fun R' h => hl R' (by simp [h])) (c + 3 * R.length)
    have h2 := hl R (by simp)
    simp only [updE, List.length_cons]
    nlinarith

theorem updP_sem (d : ℕ) (δ : ℕ → ℕ → List Spec) (m j : ℕ) (Rs : List (List ℕ)) (c : ℕ)
    (Z : ℕ → Bool) (hd : d < c) (hR : ∀ R ∈ Rs, ∀ a ∈ R, a < c) (hF : Fresh Z c)
    (hδl : ∀ t, t < Rs.length → (δ (j + t) m).length = (Rs.getD t []).length)
    (hδs : ∀ t, SrcLt (δ t m) c) :
    (∀ w, w < c → evalP A O (updP d δ m j Rs c) Z w = Z w) ∧
    Fresh (evalP A O (updP d δ m j Rs c) Z) (updE Rs c) ∧
    ∀ t, t < Rs.length →
      valLE (((updT Rs c).getD t []).map (evalP A O (updP d δ m j Rs c) Z)) =
        (valLE ((Rs.getD t []).map Z) +
          valLE (((δ (j + t) m).map (specVal Z)).map (xor (Z d))) + (Z d).toNat) %
          2 ^ (Rs.getD t []).length := by
  induction Rs generalizing j c Z with
  | nil => exact ⟨fun _ _ => rfl, by simpa [updP, updE, evalP] using hF, fun t ht => by simp at ht⟩
  | cons R Rs ih =>
    set sps := (δ j m).map (xorD d)
    have hs : SrcLt sps c := fun sp hsp a ha => by
      simp only [sps, List.mem_map] at hsp
      obtain ⟨sp0, h0, rfl⟩ := hsp
      rcases SpSrc_xorD d sp0 a ha with rfl | h
      · exact hd
      · exact hδs j sp0 h0 a h
    have hl : sps.length = R.length := by
      simp only [sps, List.length_map]; simpa using hδl 0 (by simp)
    obtain ⟨F1, F2, F3⟩ := addSpecCi_sem A O R sps d c Z hl (hR R (by simp)) hd hs hF
    set Z1 := evalP A O (addSpecCi R sps d c) Z
    obtain ⟨G1, G2, G3⟩ := ih (j + 1) (c + 3 * R.length) Z1 (by omega)
      (fun R' h a ha => by have := hR R' (by simp [h]) a ha; omega) F2
      (fun t ht => by
        have := hδl (t + 1) (by simp; omega)
        rw [show j + 1 + t = j + (t + 1) by ring]; simpa using this)
      (fun t sp hsp a ha => by have := hδs t sp hsp a ha; omega)
    simp only [updP, evalP_append]
    refine ⟨fun w hw => by rw [G1 w (by omega), F1 w hw], G2, ?_⟩
    intro t ht
    cases t with
    | zero =>
      simp only [updT, List.getD_cons_zero, Nat.add_zero]
      have : (addOutC R c).map (evalP A O (updP d δ m (j + 1) Rs (c + 3 * R.length)) Z1) =
          (addOutC R c).map Z1 :=
        List.map_congr_left (fun w hw => G1 w (by have := addOutC_bound R c w hw; omega))
      rw [this, F3]
      simp only [sps, List.map_map]
      have e : (δ j m).map (specVal Z ∘ xorD d) = (δ j m).map ((Z d).xor ∘ specVal Z) :=
        List.map_congr_left (by intro sp _; simp)
      rw [e]
    | succ t =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at ht
      simp only [updT, List.getD_cons_succ]
      rw [G3 t ht, show j + 1 + t = j + (t + 1) by ring, F1 d hd]
      have hmem : (Rs.getD t []) ∈ Rs := by
        rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
      have h1 : (Rs.getD t []).map Z1 = (Rs.getD t []).map Z :=
        List.map_congr_left (fun w hw => F1 w (hR _ (List.mem_cons_of_mem _ hmem) w hw))
      have h2 : (δ (j + (t + 1)) m).map (specVal Z1) = (δ (j + (t + 1)) m).map (specVal Z) :=
        List.map_congr_left (fun sp hsp => specVal_congr _ _ _ (fun a ha =>
          F1 a (hδs _ sp hsp a ha)))
      rw [h1, h2]

theorem updP_good (S : ℕ → Prop) (d : ℕ) (δ : ℕ → ℕ → List Spec) (m j : ℕ)
    (Rs : List (List ℕ)) (c : ℕ)
    (hd : d < c ∧ S d) (hR : ∀ R ∈ Rs, ∀ a ∈ R, a < c ∧ S a)
    (hδl : ∀ t, t < Rs.length → (δ (j + t) m).length = (Rs.getD t []).length)
    (hδs : ∀ t, ∀ sp ∈ δ t m, ∀ a, SpSrc sp a → a < c ∧ S a)
    (hS : ∀ w, c ≤ w → S w) :
    ∀ I ∈ updP d δ m j Rs c, Good A S c (updE Rs c) I := by
  induction Rs generalizing j c with
  | nil => simp [updP]
  | cons R Rs ih =>
    intro I hI
    simp only [updP, List.mem_append] at hI
    rcases hI with hI | hI
    · have := addSpecCi_good A S R ((δ j m).map (xorD d)) d c
        (by simp only [List.length_map]; simpa using hδl 0 (by simp)) (hR R (by simp)) hd
        (fun sp hsp a ha => by
          simp only [List.mem_map] at hsp
          obtain ⟨sp0, h0, rfl⟩ := hsp
          rcases SpSrc_xorD d sp0 a ha with rfl | h
          · exact hd
          · exact hδs j sp0 h0 a h) hS I hI
      exact this.mono le_rfl (by simp only [updE]; exact updE_ge _ _)
    · have := ih (j + 1) (c + 3 * R.length) ⟨by omega, hd.2⟩
        (fun R' h a ha => by have := hR R' (by simp [h]) a ha; exact ⟨by omega, this.2⟩)
        (fun t ht => by
          have := hδl (t + 1) (by simp; omega)
          rw [show j + 1 + t = j + (t + 1) by ring]; simpa using this)
        (fun t sp hsp a ha => by have := hδs t sp hsp a ha; exact ⟨by omega, this.2⟩)
        (fun w hw => hS w (by omega)) I hI
      exact this.mono (by omega) (by simp [updE])

theorem updP_noQ (d : ℕ) (δ : ℕ → ℕ → List Spec) (m j : ℕ) (Rs : List (List ℕ)) (c : ℕ) :
    ∀ I ∈ updP d δ m j Rs c, I.isQ = false := by
  induction Rs generalizing j c with
  | nil => simp [updP]
  | cons R Rs ih =>
    intro I hI
    simp only [updP, List.mem_append] at hI
    rcases hI with hI | hI
    · exact addSpecCi_noQ _ _ _ _ I hI
    · exact ih _ _ I hI

theorem updP_length (Lm k : ℕ) (d : ℕ) (δ : ℕ → ℕ → List Spec) (m j : ℕ) (Rs : List (List ℕ))
    (hl : ∀ R ∈ Rs, R.length ≤ Lm) (c : ℕ)
    (hδl : ∀ t, t < Rs.length → (δ (j + t) m).length = (Rs.getD t []).length)
    (hk : ∀ t, ∀ sp ∈ δ t m, sp.2.length ≤ k) :
    (updP d δ m j Rs c).length ≤ (k + 8) * Lm * Rs.length := by
  induction Rs generalizing j c with
  | nil => simp [updP]
  | cons R Rs ih =>
    have h1 := ih (j + 1) (fun R' h => hl R' (by simp [h])) (c + 3 * R.length)
      (fun t ht => by
        have := hδl (t + 1) (by simp; omega)
        rw [show j + 1 + t = j + (t + 1) by ring]; simpa using this)
    have h2 := addSpecCi_length R ((δ j m).map (xorD d)) d c (k + 1)
      (by simp only [List.length_map]; simpa using hδl 0 (by simp))
      (fun sp hsp => by
        simp only [List.mem_map] at hsp
        obtain ⟨sp0, h0, rfl⟩ := hsp
        rw [len_xorD]; have := hk j sp0 h0; omega)
    have h3 := hl R (by simp)
    simp only [updP, List.length_append, List.length_cons]
    have : (k + 1 + 7) * R.length ≤ (k + 8) * Lm := Nat.mul_le_mul_left _ h3
    nlinarith

end

end

end QuantumLTF.Membership.A2

-- ===== module U5 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

/-! ### bitsToNat and valLE -/

theorem bitsToNat_castSucc (len : ℕ) (q : Qubits (len + 1)) :
    bitsToNat q = 2 * bitsToNat (fun i : Fin len => q i.castSucc) + (q (Fin.last len)).toNat := by
  unfold bitsToNat
  rw [Fin.sum_univ_castSucc, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hi := i.isLt
    simp only [Fin.val_castSucc]
    split_ifs
    · rw [show len + 1 - 1 - (i : ℕ) = (len - 1 - i) + 1 by omega, pow_succ]; ring
    · simp
  · simp only [Fin.val_last]; cases q (Fin.last len) <;> simp

theorem bitsToNat_eq_valLE (L : List Bool) : ∀ (len : ℕ) (q : Qubits len), L.length = len →
    (∀ i : Fin len, q i = L.reverse.getD i false) → bitsToNat q = valLE L := by
  induction L with
  | nil =>
    intro len q hl _
    subst hl; simp [bitsToNat]
  | cons b L ih =>
    intro len q hl hq
    simp only [List.length_cons] at hl
    subst hl
    rw [bitsToNat_castSucc, ih L.length _ rfl]
    · have : q (Fin.last L.length) = b := by
        rw [hq]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      rw [this, valLE_cons]; ring
    · intro i
      rw [hq]
      simp only [Fin.val_castSucc, List.reverse_cons]
      have hi : (i : ℕ) < L.reverse.length := by simp
      rw [List.getD_eq_getElem _ _ (by simp <;> omega), List.getD_eq_getElem _ _ hi]
      try simp [List.getElem_append_left hi]

/-! ### Track arithmetic -/

theorem mod_eq_of_modEq (X : ℕ) (W : ℤ) (len : ℕ) (h : (X : ℤ) ≡ W [ZMOD 2 ^ len])
    (h0 : 0 ≤ W) (h1 : W < 2 ^ len) : ((X % 2 ^ len : ℕ) : ℤ) = W := by
  rw [Int.natCast_mod]
  push_cast
  rw [h]
  exact Int.emod_eq_of_lt h0 h1

theorem track_step_xor (N len : ℕ) (B : List Bool) (hB : B.length = len) (dd : Bool) (Δ : ℤ)
    (hΔ : ((valLE B : ℕ) : ℤ) ≡ Δ [ZMOD 2 ^ len]) (V : ℝ)
    (hN : (N : ℝ) + ((if dd then -Δ else Δ : ℤ) : ℝ) = V) (h0 : 0 ≤ V) (h1 : V < 2 ^ len) :
    (((N + valLE (B.map (xor dd)) + dd.toNat) % 2 ^ len : ℕ) : ℝ) = V := by
  set z : ℤ := if dd then -Δ else Δ with hz
  have hW : ((N : ℤ) + z : ℤ) = ((N : ℤ) + z : ℤ) := rfl
  have hreal : (((N : ℤ) + z : ℤ) : ℝ) = V := by push_cast; exact hN
  have h0' : (0 : ℤ) ≤ N + z := by exact_mod_cast (hreal ▸ h0 : (0:ℝ) ≤ (((N : ℤ) + z : ℤ) : ℝ))
  have h1' : (N : ℤ) + z < 2 ^ len := by
    have h2 : (((N : ℤ) + z : ℤ) : ℝ) < ((2 ^ len : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  have hx := valLE_map_xor B dd
  rw [hB] at hx
  have hmod : (((N + valLE (B.map (xor dd)) + dd.toNat : ℕ)) : ℤ) ≡ N + z [ZMOD 2 ^ len] := by
    cases dd
    · simp only [Bool.toNat_false, add_zero, if_false, Bool.false_eq_true] at hx ⊢
      rw [hz, if_neg (by simp)]
      have e : ∀ L : List Bool, L.map (xor false) = L := by
        intro L
        induction L with
        | nil => rfl
        | cons b L ih => simp [ih]
      rw [e]; push_cast
      exact Int.ModEq.add_left _ hΔ
    · simp only [Bool.toNat_true, if_true] at hx ⊢
      rw [hz, if_pos rfl]
      have e2 : ((valLE (B.map (xor true)) + 1 : ℕ) : ℤ) = 2 ^ len - (valLE B : ℤ) := by
        have : ((valLE (B.map (xor true)) + 1 + valLE B : ℕ) : ℤ) = ((2 ^ len : ℕ) : ℤ) := by
          rw [hx]
        push_cast at this ⊢; linarith
      have : ((N + valLE (B.map (xor true)) + 1 : ℕ) : ℤ) = N + (2 ^ len - (valLE B : ℤ)) := by
        rw [← e2]; push_cast; ring
      rw [this]
      apply Int.ModEq.add_left
      have h3 : (2 : ℤ) ^ len - valLE B ≡ 0 - valLE B [ZMOD 2 ^ len] :=
        Int.ModEq.sub_right _ (Int.modEq_zero_iff_dvd.mpr dvd_rfl)
      refine h3.trans ?_
      rw [zero_sub]; exact Int.ModEq.neg hΔ
  have key := mod_eq_of_modEq _ _ len hmod h0' h1'
  rw [← hreal, ← key]
  push_cast; rfl

/-! ### One bisection step of the query tree -/

theorem bis_step {n : ℕ} (p x : EuclideanSpace ℝ (Fin n)) (s : ℤ)
    (g : EuclideanSpace ℝ (Fin n) → ℤ) (hg : ∀ y, g y = 1 ∨ g y = -1) (m : ℕ) (lo L : ℝ) :
    (affineBoundaryBisect p x s (m + 1) lo (lo + L)).run g =
      (affineBoundaryBisect p x s m
        (if xor (decide (g (x + (lo + L / 2) • p) = -1)) (!decide (s = 1)) then lo + L / 2 else lo)
        ((if xor (decide (g (x + (lo + L / 2) • p) = -1)) (!decide (s = 1))
          then lo + L / 2 else lo) + L / 2)).run g := by
  have hmid : (lo + (lo + L)) / 2 = lo + L / 2 := by ring
  have hhi : lo + L / 2 + L / 2 = lo + L := by ring
  simp only [affineBoundaryBisect, QueryTree.run, hmid]
  rcases hg (x + (lo + L / 2) • p) with h | h <;> by_cases hs : s = 1 <;>
    simp [h, hs, hhi]

/-! ### The bisection rounds -/

section
variable (n ℓ sW : ℕ) (δ : ℕ → ℕ → List Spec)

def rP : ℕ → List (List ℕ) → ℕ → List Ins
  | 0, _, _ => []
  | m + 1, Ts, c =>
      copyRegs (Ts.take n) c ++ [Ins.qry c, Ins.cnot sW (c + n * ℓ)] ++
        (updP (c + n * ℓ) δ m 0 Ts (c + n * ℓ + 1) ++
          rP m (updT Ts (c + n * ℓ + 1)) (updE Ts (c + n * ℓ + 1)))

def rT : ℕ → List (List ℕ) → ℕ → List (List ℕ)
  | 0, Ts, _ => Ts
  | m + 1, Ts, c => rT m (updT Ts (c + n * ℓ + 1)) (updE Ts (c + n * ℓ + 1))

def rE : ℕ → List (List ℕ) → ℕ → ℕ
  | 0, _, c => c
  | m + 1, Ts, c => rE m (updT Ts (c + n * ℓ + 1)) (updE Ts (c + n * ℓ + 1))

theorem rE_ge (m : ℕ) (Ts : List (List ℕ)) (c : ℕ) : c ≤ rE n ℓ m Ts c := by
  induction m generalizing Ts c with
  | zero => exact le_rfl
  | succ m ih =>
    have := updE_ge Ts (c + n * ℓ + 1)
    exact le_trans (by omega) (ih _ _)

theorem rT_getD_length (m : ℕ) (Ts : List (List ℕ)) (c j : ℕ) :
    ((rT n ℓ m Ts c).getD j []).length = (Ts.getD j []).length := by
  induction m generalizing Ts c with
  | zero => rfl
  | succ m ih => simp only [rT]; rw [ih, updT_getD_length]

theorem rT_length (m : ℕ) (Ts : List (List ℕ)) (c : ℕ) :
    (rT n ℓ m Ts c).length = Ts.length := by
  induction m generalizing Ts c with
  | zero => rfl
  | succ m ih => simp only [rT]; rw [ih, updT_length]

theorem rT_bound (m : ℕ) (Ts : List (List ℕ)) (c : ℕ) :
    ∀ R ∈ rT n ℓ m Ts c, ∀ w ∈ R, (∃ R0 ∈ Ts, w ∈ R0) ∨ (c ≤ w ∧ w < rE n ℓ m Ts c) := by
  induction m generalizing Ts c with
  | zero => intro R hR w hw; exact Or.inl ⟨R, hR, hw⟩
  | succ m ih =>
    intro R hR w hw
    simp only [rT] at hR
    simp only [rE]
    rcases ih _ _ R hR w hw with ⟨R0, h0, hw0⟩ | h
    · have := updT_bound Ts (c + n * ℓ + 1) R0 h0 w hw0
      have := rE_ge n ℓ m (updT Ts (c + n * ℓ + 1)) (updE Ts (c + n * ℓ + 1))
      right; omega
    · have := updE_ge Ts (c + n * ℓ + 1)
      right; omega

theorem take_len_of (Ts : List (List ℕ)) (h : ∀ R ∈ Ts.take n, R.length = ℓ)
    (c : ℕ) : ∀ R ∈ (updT Ts c).take n, R.length = ℓ := by
  intro R hR
  obtain ⟨R0, h0, e⟩ := updT_take n Ts c R hR
  rw [e]; exact h R0 h0

theorem rP_good (S : ℕ → Prop) (m : ℕ) (Ts : List (List ℕ)) (c : ℕ)
    (hl : ∀ R ∈ Ts.take n, R.length = ℓ) (hR : ∀ R ∈ Ts, ∀ a ∈ R, a < c ∧ S a)
    (hS : ∀ w, c ≤ w → S w) (hsW : sW < c ∧ S sW)
    (hδl : ∀ t m', t < Ts.length → (δ t m').length = (Ts.getD t []).length)
    (hδs : ∀ t m', ∀ sp ∈ δ t m', ∀ a, SpSrc sp a → a < c ∧ S a) :
    ∀ I ∈ rP n ℓ sW δ m Ts c, Good (n * ℓ) S c (rE n ℓ m Ts c) I := by
  induction m generalizing Ts c with
  | zero => simp [rP]
  | succ m ih =>
    intro I hI
    have hE1 := updE_ge Ts (c + n * ℓ + 1)
    have hE2 := rE_ge n ℓ m (updT Ts (c + n * ℓ + 1)) (updE Ts (c + n * ℓ + 1))
    simp only [rE] at *
    simp only [rP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with (hI | hI | hI) | hI | hI
    · have := copyRegs_good (n * ℓ) S ℓ (Ts.take n) hl c
        (fun R h a ha => hR R (List.mem_of_mem_take h) a ha) I hI
      refine this.mono le_rfl ?_
      have : (Ts.take n).length ≤ n := List.length_take_le _ _
      have : ℓ * (Ts.take n).length ≤ ℓ * n := Nat.mul_le_mul_left _ this
      have h5 : ℓ * n = n * ℓ := Nat.mul_comm _ _
      omega
    · subst hI
      refine ⟨by simp [Ins.tgt], by simp [Ins.tgt]; omega, fun s hs => ?_⟩
      simp only [Ins.src, Ins.tgt] at hs ⊢
      exact ⟨hs.2, hS s hs.1⟩
    · subst hI
      refine ⟨by simp [Ins.tgt], by simp [Ins.tgt]; omega, fun s hs => ?_⟩
      simp only [Ins.src, Ins.tgt] at hs ⊢
      subst hs; exact ⟨by omega, hsW.2⟩
    · have := updP_good (n * ℓ) S (c + n * ℓ) δ m 0 Ts (c + n * ℓ + 1)
        ⟨by omega, hS _ (by omega)⟩
        (fun R h a ha => by have := hR R h a ha; exact ⟨by omega, this.2⟩)
        (fun t ht => by simpa using hδl t m ht)
        (fun t sp hsp a ha => by have := hδs t m sp hsp a ha; exact ⟨by omega, this.2⟩)
        (fun w hw => hS w (by omega)) I hI
      exact this.mono (by omega) hE2
    · have := ih (updT Ts (c + n * ℓ + 1)) (updE Ts (c + n * ℓ + 1)) (take_len_of n ℓ Ts hl _)
        (fun R h a ha => by
          have := updT_bound Ts (c + n * ℓ + 1) R h a ha
          exact ⟨this.2, hS a (by omega)⟩)
        (fun w hw => hS w (by omega)) ⟨by omega, hsW.2⟩
        (fun t m' ht => by
          rw [updT_length] at ht; rw [updT_getD_length]; exact hδl t m' ht)
        (fun t m' sp hsp a ha => by have := hδs t m' sp hsp a ha; exact ⟨by omega, this.2⟩) I hI
      exact this.mono (by omega) le_rfl

theorem rP_countQ (m : ℕ) (Ts : List (List ℕ)) (c : ℕ) :
    (rP n ℓ sW δ m Ts c).countP Ins.isQ = m := by
  induction m generalizing Ts c with
  | zero => rfl
  | succ m ih =>
    simp only [rP, List.countP_append, List.countP_cons, ih]
    have h1 : (copyRegs (Ts.take n) c).countP Ins.isQ = 0 :=
      List.countP_eq_zero.mpr (fun I hI => by simp [copyRegs_noQ _ _ I hI])
    have h2 : (updP (c + n * ℓ) δ m 0 Ts (c + n * ℓ + 1)).countP Ins.isQ = 0 :=
      List.countP_eq_zero.mpr (fun I hI => by simp [updP_noQ _ _ _ _ _ _ I hI])
    rw [h1, h2]; simp [Ins.isQ]; omega

theorem rP_length (Lm k : ℕ) (m : ℕ) (Ts : List (List ℕ)) (c : ℕ)
    (hl : ∀ R ∈ Ts.take n, R.length = ℓ) (hL : ∀ R ∈ Ts, R.length ≤ Lm)
    (hδl : ∀ t m', t < Ts.length → (δ t m').length = (Ts.getD t []).length)
    (hk : ∀ t m', ∀ sp ∈ δ t m', sp.2.length ≤ k) :
    (rP n ℓ sW δ m Ts c).length ≤ m * (2 * ℓ * n + 2 + (k + 8) * Lm * Ts.length) := by
  induction m generalizing Ts c with
  | zero => simp [rP]
  | succ m ih =>
    have h1 := copyRegs_length ℓ (Ts.take n) hl c
    have h1' : (Ts.take n).length ≤ n := List.length_take_le _ _
    have h2 := updP_length Lm k (c + n * ℓ) δ m 0 Ts hL (c + n * ℓ + 1)
      (fun t ht => by simpa using hδl t m ht) (fun t => hk t m)
    have h3 := ih (updT Ts (c + n * ℓ + 1)) (updE Ts (c + n * ℓ + 1)) (take_len_of n ℓ Ts hl _)
      (fun R h => by
        obtain ⟨R0, h0, e⟩ := updT_len Ts _ R h
        rw [e]; exact hL R0 h0)
      (fun t m' ht => by
        rw [updT_length] at ht; rw [updT_getD_length]; exact hδl t m' ht)
    rw [updT_length] at h3
    simp only [rP, List.length_append, List.length_cons, List.length_nil]
    have : 2 * ℓ * (Ts.take n).length ≤ 2 * ℓ * n := Nat.mul_le_mul_left _ h1'
    nlinarith

end

end

end QuantumLTF.Membership.A2

-- ===== module U6 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

section
variable (n ℓ sW : ℕ) (δ : ℕ → ℕ → List Spec)

theorem rP_sem (f q : ℕ) (s : ℤ) (p x' : EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → ℤ) (hg : ∀ y, g y = 1 ∨ g y = -1)
    (sb : Bool) (hs1 : sb = decide (s = 1))
    (htil : ℝ) (len fr : ℕ → ℕ) (val : ℕ → ℝ → ℝ) (slope : ℕ → ℝ)
    (hlen : ∀ j, j < n → len j = ℓ) (hfr : ∀ j, j < n → fr j = f)
    (hval : ∀ j (hj : j < n) mid, val j mid = x' ⟨j, hj⟩ + mid * p ⟨j, hj⟩)
    (haff : ∀ j, j < n + 1 → ∀ mid δ', val j (mid + δ') = val j mid + δ' * slope j)
    (Δ : ℕ → ℕ → ℤ)
    (hΔr : ∀ j, j < n + 1 → ∀ m, m < q →
      (Δ j m : ℝ) = 2 ^ (fr j) * slope j * 2 ^ m / 2 ^ (q + 2))
    (cin : ℕ) (Z0 : ℕ → Bool)
    (hΔ : ∀ j, j < n + 1 → ∀ m, m < q →
      ((valLE ((δ j m).map (specVal Z0)) : ℕ) : ℤ) ≡ Δ j m [ZMOD 2 ^ (len j)])
    (hδs : ∀ j m, ∀ sp ∈ δ j m, ∀ a, SpSrc sp a → a < cin)
    (hδl : ∀ j, j < n + 1 → ∀ m, (δ j m).length = len j)
    (hsW : sW < cin) (hZ0s : Z0 sW = sb)
    (hrange : ∀ j, j < n + 1 → ∀ mid, htil - 1 / 4 ≤ mid → mid ≤ htil + 1 / 4 →
      |2 ^ (fr j) * val j mid| < 2 ^ (len j) / 2) :
    ∀ m, m ≤ q → ∀ (lo L : ℝ) (Ts : List (List ℕ)) (c : ℕ) (Z : ℕ → Bool),
      L = 2 ^ m / 2 ^ (q + 1) → htil - 1 / 4 ≤ lo → lo + L ≤ htil + 1 / 4 →
      Ts.length = n + 1 →
      (∀ j, j < n + 1 → (Ts.getD j []).length = len j ∧
        (valLE ((Ts.getD j []).map Z) : ℝ) = 2 ^ (len j) / 2 + 2 ^ (fr j) * val j (lo + L / 2)) →
      (∀ R ∈ Ts, ∀ a ∈ R, a < c) → Fresh Z c → cin ≤ c → (∀ w, w < cin → Z w = Z0 w) →
      let O : Qubits (n * ℓ) → Bool := fun y => decide (g (addrOf n ℓ f y) = -1)
      (∀ w, w < c → evalP (n * ℓ) O (rP n ℓ sW δ m Ts c) Z w = Z w) ∧
      Fresh (evalP (n * ℓ) O (rP n ℓ sW δ m Ts c) Z) (rE n ℓ m Ts c) ∧
      ∀ j, j < n + 1 →
        (valLE (((rT n ℓ m Ts c).getD j []).map (evalP (n * ℓ) O (rP n ℓ sW δ m Ts c) Z)) : ℝ) =
          2 ^ (len j) / 2 + 2 ^ (fr j) *
            val j ((affineBoundaryBisect p x' s m lo (lo + L)).run g) := by
  intro m
  induction m with
  | zero =>
    intro _ lo L Ts c Z _ _ _ _ hTs _ hF _ _ O
    refine ⟨fun _ _ => rfl, hF, fun j hj => ?_⟩
    have : (lo + (lo + L)) / 2 = lo + L / 2 := by ring
    simp only [rP, rT, affineBoundaryBisect, QueryTree.run, this]
    exact (hTs j hj).2
  | succ m ih =>
    intro hm lo L Ts c Z hL hlo1 hlo2 hTl hTs hTw hF hcin hZ0 O
    have hgetD : ∀ i (hi : i < n + 1), (Ts.getD i []) = Ts[i]'(by omega) := fun i hi =>
      List.getD_eq_getElem _ _ (by omega)
    have htake : ∀ R ∈ Ts.take n, R.length = ℓ := by
      intro R hR
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hR
      have hi' : i < n := by have := List.length_take_le n Ts; omega
      rw [List.getElem_take, ← hgetD i (by omega), (hTs i (by omega)).1, hlen i hi']
    have htakeLen : (Ts.take n).length = n := by simp [hTl]
    set d := c + n * ℓ with hd
    -- step 1: copy
    obtain ⟨C1, C2, C3⟩ := copyRegs_sem (n * ℓ) O ℓ (Ts.take n) htake c Z
      (fun R h a ha => hTw R (List.mem_of_mem_take h) a ha) hF
    rw [htakeLen, Nat.mul_comm ℓ n] at C2
    rw [htakeLen] at C3
    set Z1 := evalP (n * ℓ) O (copyRegs (Ts.take n) c) Z with hZ1
    set mid := lo + L / 2 with hmid
    have hblock : addrOf n ℓ f (fun j => Z1 (c + j)) = x' + mid • p := by
      ext i
      simp only [addrOf, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      have hi := i.isLt
      have e1 : splitReg n ℓ (fun j => Z1 (c + j)) i =
          (fun mm : Fin ℓ => Z ((Ts.getD i []).reverse.getD mm 0)) := by
        funext mm
        simp only [splitReg, finProdFinEquiv_apply_val]
        rw [show c + (↑mm + ℓ * ↑i) = c + ℓ * i + mm by ring, C3 i hi mm mm.isLt]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi]
      rw [e1]
      have hRl : (Ts.getD i []).length = ℓ := by rw [(hTs i (by omega)).1, hlen i hi]
      have hb := bitsToNat_eq_valLE ((Ts.getD i []).map Z) ℓ
        (fun mm => Z ((Ts.getD i []).reverse.getD mm 0)) (by rw [List.length_map, hRl]) (by
          intro mm
          have h1 : (mm : ℕ) < (Ts.getD i []).reverse.length := by
            rw [List.length_reverse, hRl]; exact mm.isLt
          have h2 : (mm : ℕ) < ((Ts.getD i []).map Z).reverse.length := by
            rw [List.length_reverse, List.length_map, hRl]; exact mm.isLt
          rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
          simp [List.getElem_reverse])
      simp only [fpVal, hb, (hTs i (by omega)).2, hlen i hi, hfr i hi, hval i hi]
      field_simp
      ring
    -- step 2: query and XOR in the sign wire
    set bit := xor (decide (g (x' + mid • p) = -1)) (!sb) with hbit
    set dv := xor (decide (g (x' + mid • p) = -1)) sb with hdv
    have hdvbit : dv = !bit := by
      simp only [hdv, hbit]; cases decide (g (x' + mid • p) = -1) <;> cases sb <;> rfl
    have hZ1d : Z1 d = false := C2 d (by omega)
    have hZ1s : Z1 sW = sb := by rw [C1 sW (by omega), hZ0 sW hsW, hZ0s]
    have e2 : evalP (n * ℓ) O [Ins.qry c, Ins.cnot sW d] Z1 = Function.update Z1 d dv := by
      have hq : (Ins.qry c).eval (n * ℓ) O Z1 =
          Function.update Z1 d (decide (g (x' + mid • p) = -1)) := by
        simp only [Ins.eval, Ins.tgt, Ins.fn]
        rw [← hd, hZ1d, Bool.false_xor]
        congr 2
        simp only [O]
        rw [hblock]
      have hsd : sW ≠ d := by omega
      rw [evalP_cons, hq, evalP_cons, evalP_nil, eval_cnot, Function.update_self,
        Function.update_of_ne hsd, hZ1s, Function.update_idem]
    -- step 3: update tracks
    set Z2 := Function.update Z1 d dv with hZ2
    have hF2 : Fresh Z2 (d + 1) := by
      intro w hw; rw [hZ2, Function.update_of_ne (by omega)]; exact C2 w (by omega)
    have hZ2lt : ∀ w, w < c → Z2 w = Z w := by
      intro w hw; rw [hZ2, Function.update_of_ne (by omega), C1 w hw]
    obtain ⟨D1, D2, D3⟩ := updP_sem (n * ℓ) O d δ m 0 Ts (d + 1) Z2 (by omega)
      (fun R h a ha => by have := hTw R h a ha; omega) hF2
      (fun t ht => by rw [Nat.zero_add, hδl t (by omega) m, (hTs t (by omega)).1])
      (fun t sp hsp a ha => by have := hδs t m sp hsp a ha; omega)
    set Z3 := evalP (n * ℓ) O (updP d δ m 0 Ts (d + 1)) Z2 with hZ3
    -- step 4: induction hypothesis
    set lo' := if bit then lo + L / 2 else lo with hlo'
    have hL' : L / 2 = 2 ^ m / 2 ^ (q + 1) := by rw [hL, pow_succ]; ring
    have hL0 : 0 ≤ L := by rw [hL]; positivity
    have hlo'1 : htil - 1 / 4 ≤ lo' := by
      simp only [hlo']; split_ifs <;> linarith
    have hlo'2 : lo' + L / 2 ≤ htil + 1 / 4 := by
      simp only [hlo']; split_ifs <;> linarith
    have hTs' : ∀ j, j < n + 1 → ((updT Ts (d + 1)).getD j []).length = len j ∧
        (valLE (((updT Ts (d + 1)).getD j []).map Z3) : ℝ) =
          2 ^ (len j) / 2 + 2 ^ (fr j) * val j (lo' + L / 2 / 2) := by
      intro j hj
      refine ⟨by rw [updT_getD_length]; exact (hTs j hj).1, ?_⟩
      rw [D3 j (by omega), (hTs j hj).1, Nat.zero_add]
      have hmem : Ts.getD j [] ∈ Ts := by rw [hgetD j hj]; exact List.getElem_mem _
      have hmap : (Ts.getD j []).map Z2 = (Ts.getD j []).map Z :=
        List.map_congr_left (fun w hw => hZ2lt w (hTw _ hmem w hw))
      have hδmap : (δ j m).map (specVal Z2) = (δ j m).map (specVal Z0) :=
        List.map_congr_left (fun sp hsp => specVal_congr _ _ _ (fun a ha => by
          have := hδs j m sp hsp a ha
          rw [hZ2lt a (by omega), hZ0 a this]))
      have hZ2d : Z2 d = dv := by simp [hZ2]
      rw [hmap, hδmap, hZ2d]
      have hval0 := (hTs j hj).2
      have hmid' : lo' + L / 2 / 2 = mid + (if bit then L / 4 else -(L / 4)) := by
        simp only [hlo', hmid]; split_ifs <;> ring
      have hrng := hrange j hj (lo' + L / 2 / 2) (by linarith) (by linarith)
      apply track_step_xor _ _ _ (by rw [List.length_map, hδl j hj m]) dv (Δ j m) (hΔ j hj m (by omega))
      · rw [hval0, hmid', haff j hj mid, hdvbit]
        have hL4 : L / 4 = 2 ^ m / 2 ^ (q + 2) := by
          rw [hL, pow_succ, pow_succ, pow_succ]; ring
        have hu := hΔr j hj m (by omega)
        cases bit
        · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
          push_cast; rw [hu, hL4]; ring
        · simp only [Bool.not_true, if_true, Bool.false_eq_true, if_false]
          push_cast; rw [hu, hL4]; ring
      · have := (abs_lt.mp hrng).1; linarith
      · have := (abs_lt.mp hrng).2
        have h2 : (2 : ℝ) ^ (len j) / 2 + 2 ^ (len j) / 2 = 2 ^ len j := by ring
        linarith
    obtain ⟨E1, E2, E3⟩ := ih (by omega) lo' (L / 2) (updT Ts (d + 1)) (updE Ts (d + 1)) Z3 hL'
      hlo'1 hlo'2 (by rw [updT_length, hTl]) hTs'
      (fun R h a ha => (updT_bound Ts (d + 1) R h a ha).2) D2
      (by have := updE_ge Ts (d + 1); omega)
      (fun w hw => by
        rw [D1 w (by omega), hZ2lt w (by omega), hZ0 w hw])
    -- assemble
    have hP : rP n ℓ sW δ (m + 1) Ts c = (copyRegs (Ts.take n) c ++
        [Ins.qry c, Ins.cnot sW d]) ++
        (updP d δ m 0 Ts (d + 1) ++ rP n ℓ sW δ m (updT Ts (d + 1)) (updE Ts (d + 1))) := rfl
    have hev : evalP (n * ℓ) O (rP n ℓ sW δ (m + 1) Ts c) Z =
        evalP (n * ℓ) O (rP n ℓ sW δ m (updT Ts (d + 1)) (updE Ts (d + 1))) Z3 := by
      rw [hP, evalP_append, evalP_append, evalP_append, ← hZ1, e2]
    have hE : rE n ℓ (m + 1) Ts c = rE n ℓ m (updT Ts (d + 1)) (updE Ts (d + 1)) := rfl
    have hT : rT n ℓ (m + 1) Ts c = rT n ℓ m (updT Ts (d + 1)) (updE Ts (d + 1)) := rfl
    have hge := updE_ge Ts (d + 1)
    rw [hev, hE, hT]
    refine ⟨fun w hw => ?_, E2, fun j hj => ?_⟩
    · rw [E1 w (by omega), D1 w (by omega), hZ2lt w hw]
    · rw [E3 j hj, bis_step p x' s g hg m lo L]
      have hb : xor (decide (g (x' + (lo + L / 2) • p) = -1)) (!decide (s = 1)) = bit := by
        rw [hbit, hs1]
      rw [hb]

end

end

end QuantumLTF.Membership.A2

-- ===== module U7 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

/-! ### Sequences of blocks occupying consecutive regions -/

def blocks (B : ℕ → List Ins) : ℕ → List Ins
  | 0 => []
  | k + 1 => blocks B k ++ B k

section
variable (A : ℕ) (O : Qubits A → Bool)

theorem blocks_sem (B : ℕ → List Ins) (c sz : ℕ) (Pr : ℕ → (ℕ → Bool) → Prop)
    (hPr : ∀ i Z1 Z2, (∀ w, c + i * sz ≤ w → w < c + (i + 1) * sz → Z1 w = Z2 w) →
      Pr i Z1 → Pr i Z2)
    (Z : ℕ → Bool) (k : ℕ)
    (hB : ∀ i, i < k → ∀ Z', Fresh Z' (c + i * sz) → (∀ w, w < c → Z' w = Z w) →
      (∀ w, w < c + i * sz → evalP A O (B i) Z' w = Z' w) ∧
      Fresh (evalP A O (B i) Z') (c + (i + 1) * sz) ∧ Pr i (evalP A O (B i) Z'))
    (hF : Fresh Z c) :
    (∀ w, w < c → evalP A O (blocks B k) Z w = Z w) ∧
    Fresh (evalP A O (blocks B k) Z) (c + k * sz) ∧
    ∀ i, i < k → Pr i (evalP A O (blocks B k) Z) := by
  induction k with
  | zero => exact ⟨fun _ _ => rfl, by simp only [zero_mul, add_zero]; exact hF, fun i hi => by omega⟩
  | succ k ih =>
    obtain ⟨P1, P2, P3⟩ := ih (fun i hi => hB i (by omega))
    set Zk := evalP A O (blocks B k) Z
    obtain ⟨Q1, Q2, Q3⟩ := hB k (by omega) Zk P2 P1
    simp only [blocks, evalP_append]
    refine ⟨fun w hw => by rw [Q1 w (by have := Nat.zero_le (k * sz); omega), P1 w hw], Q2,
      fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · apply hPr i Zk _ _ (P3 i h)
      intro w _ h2
      have : (i + 1) * sz ≤ k * sz := Nat.mul_le_mul_right _ h
      exact (Q1 w (by omega)).symm
    · subst h; exact Q3

theorem blocks_good (S : ℕ → Prop) (B : ℕ → List Ins) (c sz k : ℕ)
    (hB : ∀ i, i < k → ∀ I ∈ B i, Good A S (c + i * sz) (c + (i + 1) * sz) I) :
    ∀ I ∈ blocks B k, Good A S c (c + k * sz) I := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    intro I hI
    simp only [blocks, List.mem_append] at hI
    rcases hI with hI | hI
    · exact (ih (fun i hi => hB i (by omega)) I hI).mono le_rfl
        (by have := Nat.mul_le_mul_right sz (Nat.le_succ k); simp only [Nat.succ_eq_add_one] at this; omega)
    · exact (hB k (by omega) I hI).mono (by omega) le_rfl

theorem blocks_noQ (B : ℕ → List Ins) (k : ℕ) (hB : ∀ i, i < k → ∀ I ∈ B i, I.isQ = false) :
    ∀ I ∈ blocks B k, I.isQ = false := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    intro I hI
    simp only [blocks, List.mem_append] at hI
    rcases hI with hI | hI
    · exact ih (fun i hi => hB i (by omega)) I hI
    · exact hB k (by omega) I hI

theorem blocks_length (B : ℕ → List Ins) (k L : ℕ) (hB : ∀ i, i < k → (B i).length ≤ L) :
    (blocks B k).length ≤ k * L := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    have := ih (fun i hi => hB i (by omega))
    have h2 := hB k (by omega)
    simp only [blocks, List.length_append, Nat.succ_mul]; omega

end

/-! ### A constant plus a list of terms, in a fresh register -/

section
variable (A : ℕ) (O : Qubits A → Bool)

def cblk (w K : ℕ) (ts : List (List Spec)) (c : ℕ) : List Ins :=
  fill (constSpecs K w) c ++ accP (List.range' c w) ts (c + w)

def cblkOut (w : ℕ) (ts : List (List Spec)) (c : ℕ) : List ℕ :=
  accOut (List.range' c w) ts (c + w)

def cblkSize (w : ℕ) (ts : List (List Spec)) : ℕ := w + ts.length * (3 * w + 1)

theorem cblkOut_length (w : ℕ) (ts : List (List Spec)) (c : ℕ) :
    (cblkOut w ts c).length = w := by simp [cblkOut, accOut_length]

theorem cblkOut_bound (w : ℕ) (ts : List (List Spec)) (c : ℕ) :
    ∀ a ∈ cblkOut w ts c, c ≤ a ∧ a < c + cblkSize w ts := by
  intro a ha
  rcases accOut_bound _ _ _ a ha with h | h
  · simp [List.mem_range'] at h; obtain ⟨i, hi, rfl⟩ := h; simp only [cblkSize]
    constructor
    · omega
    · have := Nat.zero_le (ts.length * (3 * w + 1)); omega
  · simp only [List.length_range'] at h; simp only [cblkSize]; omega

theorem cblk_sem (Z0 : ℕ → Bool) (c0 : ℕ) (w K : ℕ) (ts : List (List Spec)) (c : ℕ)
    (Z : ℕ → Bool) (hc : c0 ≤ c) (hl : ∀ t ∈ ts, t.length = w)
    (hs : ∀ t ∈ ts, SrcLt t c0) (hZ : ∀ v, v < c0 → Z v = Z0 v) (hF : Fresh Z c) :
    (∀ v, v < c → evalP A O (cblk w K ts c) Z v = Z v) ∧
    Fresh (evalP A O (cblk w K ts c) Z) (c + cblkSize w ts) ∧
    valLE ((cblkOut w ts c).map (evalP A O (cblk w K ts c) Z)) = (K + sumV Z0 ts) % 2 ^ w := by
  have hs0 : SrcLt (constSpecs K w) c := fun sp hsp a ha => absurd ha (constSpecs_src K w sp hsp a)
  obtain ⟨F1, F2, _⟩ := fill_sem A O _ c Z hF hs0
  have Fm := fill_map A O _ c Z hF hs0
  rw [constSpecs_length] at F2 Fm
  set Z1 := evalP A O (fill (constSpecs K w) c) Z
  obtain ⟨G1, G2, G3⟩ := accP_sem A O Z0 c0 (List.range' c w) ts (c + w) Z1 (by omega)
    (fun t ht => by simp [hl t ht]) (fun a ha => by simp [List.mem_range'] at ha; omega)
    hs (fun v hv => by rw [F1 v (by omega), hZ v hv]) F2
  simp only [cblk, cblkOut, cblkSize, evalP_append]
  refine ⟨fun v hv => by rw [G1 v (by omega), F1 v hv], ?_, ?_⟩
  · simpa [Nat.add_assoc] using G2
  · rw [G3, Fm, constSpecs_val]; simp [Nat.add_mod]

theorem cblk_good (S : ℕ → Prop) (w K : ℕ) (ts : List (List Spec)) (c : ℕ)
    (hl : ∀ t ∈ ts, t.length = w) (hs : ∀ t ∈ ts, ∀ sp ∈ t, ∀ a, SpSrc sp a → a < c ∧ S a)
    (hS : ∀ v, c ≤ v → S v) :
    ∀ I ∈ cblk w K ts c, Good A S c (c + cblkSize w ts) I := by
  intro I hI
  simp only [cblk, List.mem_append] at hI
  rcases hI with hI | hI
  · have := fill_good A S (constSpecs K w) c
      (fun sp hsp a ha => absurd ha (constSpecs_src K w sp hsp a)) I hI
    rw [constSpecs_length] at this
    exact this.mono le_rfl (by simp only [cblkSize]; omega)
  · have := accP_good A S (List.range' c w) ts (c + w) (fun t ht => by simp [hl t ht])
      (fun a ha => by simp [List.mem_range'] at ha; exact ⟨by omega, hS a (by omega)⟩)
      (fun t ht sp hsp a ha => by have := hs t ht sp hsp a ha; exact ⟨by omega, this.2⟩)
      (fun v hv => hS v (by omega)) I hI
    simp only [List.length_range'] at this
    exact this.mono (by omega) (by simp only [cblkSize]; omega)

theorem cblk_noQ (w K : ℕ) (ts : List (List Spec)) (c : ℕ) :
    ∀ I ∈ cblk w K ts c, I.isQ = false := by
  intro I hI
  simp only [cblk, List.mem_append] at hI
  rcases hI with hI | hI
  · exact fill_noQ _ _ I hI
  · exact accP_noQ _ _ _ I hI

theorem cblk_length (w K : ℕ) (ts : List (List Spec)) (c k : ℕ)
    (hl : ∀ t ∈ ts, t.length = w) (hk : ∀ t ∈ ts, ∀ sp ∈ t, sp.2.length ≤ k) :
    (cblk w K ts c).length ≤ w + ts.length * ((k + 7) * w) := by
  have h1 := fill_length (constSpecs K w) 0 (fun sp hsp => by
    rw [constSpecs_terms K w sp hsp]) c
  rw [constSpecs_length] at h1
  have h2 := accP_length (List.range' c w) ts (c + w) k (fun t ht => by simp [hl t ht]) hk
  simp only [List.length_range'] at h2
  simp only [cblk, List.length_append]; omega

end

end

end QuantumLTF.Membership.A2

-- ===== module U8 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

section
variable (A : ℕ) (O : Qubits A → Bool)

/-! ### Copy-out into the value register -/

def copyOut (R : List ℕ) (nb Vb : ℕ) : List Ins :=
  (List.range Vb).map fun m => Ins.cnot (R.reverse.getD m 0) (nb + m)

theorem copyOut_sem (R : List ℕ) (nb base : ℕ) (hR : ∀ a ∈ R, base ≤ a) (Z : ℕ → Bool) :
    ∀ k, k ≤ R.length → nb + k ≤ base → (∀ m, m < k → Z (nb + m) = false) →
    ∀ w, evalP A O (copyOut R nb k) Z w =
      if nb ≤ w ∧ w < nb + k then Z (R.reverse.getD (w - nb) 0) else Z w := by
  have hsrc : ∀ m, m < R.length → base ≤ R.reverse.getD m 0 := by
    intro m hm
    have h : m < R.reverse.length := by simp; omega
    rw [List.getD_eq_getElem _ _ h]; exact hR _ (List.mem_reverse.mp (List.getElem_mem h))
  intro k
  induction k with
  | zero => intro _ _ _ w; simp [copyOut, evalP] <;> omega
  | succ k ih =>
    intro hk hb hz w
    have ih' := ih (by omega) (by omega) (fun m hm => hz m (by omega))
    simp only [copyOut, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      evalP_append] at ih' ⊢
    simp only [evalP_cons, evalP_nil, eval_cnot]
    have hsk := ih' (R.reverse.getD k 0)
    have hs := hsrc k (by omega)
    rw [if_neg (by omega)] at hsk
    by_cases hw : w = nb + k
    · subst hw
      rw [Function.update_self, hsk, ih', if_neg (by omega), hz k (by omega)]
      simp
    · rw [Function.update_of_ne hw, ih']
      by_cases h1 : nb ≤ w ∧ w < nb + k
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

theorem copyOut_length (R : List ℕ) (nb k : ℕ) : (copyOut R nb k).length = k := by
  simp [copyOut]

theorem copyOut_noQ (R : List ℕ) (nb k : ℕ) : ∀ I ∈ copyOut R nb k, I.isQ = false := by
  intro I hI
  simp only [copyOut, List.mem_map] at hI
  obtain ⟨m, _, rfl⟩ := hI; rfl

end

def prodTerms (Kw : ℕ) : List ℕ → ℕ → List ℕ → List (List Spec)
  | [], _, _ => []
  | a :: R, k, P => shiftSp (k + 2) Kw (andSpecs a P) :: prodTerms Kw R (k + 1) P

theorem prodTerms_length (Kw : ℕ) (R : List ℕ) (k : ℕ) (P : List ℕ) :
    (prodTerms Kw R k P).length = R.length := by
  induction R generalizing k with
  | nil => rfl
  | cons a R ih => simp [prodTerms, ih]

theorem prodTerms_mem (Kw : ℕ) (R : List ℕ) (k : ℕ) (P : List ℕ) :
    ∀ t ∈ prodTerms Kw R k P, ∃ a ∈ R, ∃ j, k ≤ j ∧ j < k + R.length ∧
      t = shiftSp (j + 2) Kw (andSpecs a P) := by
  induction R generalizing k with
  | nil => simp [prodTerms]
  | cons a R ih =>
    intro t ht
    simp only [prodTerms, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨a, by simp, k, le_rfl, by simp, rfl⟩
    · obtain ⟨b, hb, j, h1, h2, e⟩ := ih (k + 1) t ht
      exact ⟨b, by simp [hb], j, by omega, by simp; omega, e⟩

theorem prodTerms_sumV (Kw : ℕ) (Z : ℕ → Bool) (R : List ℕ) (k : ℕ) (P : List ℕ) :
    sumV Z (prodTerms Kw R k P) = 2 ^ (k + 2) * valLE (R.map Z) * valLE (P.map Z) := by
  induction R generalizing k with
  | nil => simp [prodTerms, sumV]
  | cons a R ih =>
    simp only [prodTerms, sumV, ih, shiftSp_val, andSpecs_val, List.map_cons, valLE_cons]
    cases Z a <;> simp only [Bool.false_eq_true, if_false, if_true, Bool.toNat_false,
      Bool.toNat_true] <;> ring

def Kc (z : ℤ) (len : ℕ) : ℕ := (z % (2 : ℤ) ^ len).toNat

theorem Kc_modEq (z : ℤ) (len : ℕ) : ((Kc z len : ℕ) : ℤ) ≡ z [ZMOD 2 ^ len] := by
  unfold Kc
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  exact Int.mod_modEq _ _

structure Prm where
  n : ℕ
  b : ℕ
  q : ℕ
  r : ℕ
  ℓ₁ : ℕ
  f₁ : ℕ
  Bh : ℕ
  fh : ℕ
  ℓ : ℕ
  f : ℕ

namespace Prm
variable (G : Prm)

def Vf : ℕ := G.fh + G.q + 2
def Vb : ℕ := G.Vf + G.Bh + 2
def Kw : ℕ := G.Bh + G.ℓ₁ + 3
def sW : ℕ := G.n * G.ℓ₁
def hB : ℕ := G.n * G.ℓ₁ + 1
def xB : ℕ := G.hB + G.Bh
def vB : ℕ := G.xB + G.n * G.b
def base : ℕ := G.vB + G.Vb
def pReg (i : ℕ) : List ℕ := regLE (G.ℓ₁ * i) G.ℓ₁
def hReg : List ℕ := regLE G.hB G.Bh
def xReg (i : ℕ) : List ℕ := regLE (G.xB + G.b * i) G.b

def qTerms (i : ℕ) : List (List Spec) :=
  shiftSp (G.ℓ₁ + 1) G.Kw (notSpecs G.hReg) :: shiftSp (G.Bh + 1) G.Kw (notSpecs (G.pReg i)) ::
    prodTerms G.Kw G.hReg 0 (G.pReg i)
def qSize : ℕ := G.Kw + (G.Bh + 2) * (3 * G.Kw + 1)
def qSt (i : ℕ) : ℕ := G.base + i * G.qSize
def qP (i : ℕ) : List Ins := cblk G.Kw 0 (G.qTerms i) (G.qSt i)
def qOut (i : ℕ) : List ℕ := cblkOut G.Kw (G.qTerms i) (G.qSt i)

def tS0 : ℕ := G.base + G.n * G.qSize
def eQ : ℕ := G.f - G.fh - G.f₁ - 2
def Kp : ℤ := 2 ^ (G.Bh + G.ℓ₁) - 2 ^ (G.ℓ₁ + 1) * (2 ^ G.Bh - 1) -
  2 ^ (G.Bh + 1) * (2 ^ G.ℓ₁ - 1)
def Kt : ℤ := 2 ^ (G.ℓ - 1) - 2 ^ (G.f - G.r - 1) + 2 ^ (G.f - G.r - G.b - 1) + 2 ^ G.eQ * G.Kp
def tTerms (i : ℕ) : List (List Spec) :=
  [shiftSp (G.f - G.r - G.b) G.ℓ (copySpecs (G.xReg i)), shiftSp G.eQ G.ℓ (copySpecs (G.qOut i))]
def tSize : ℕ := G.ℓ + 2 * (3 * G.ℓ + 1)
def tSt (i : ℕ) : ℕ := G.tS0 + i * G.tSize
def tP (i : ℕ) : List Ins := cblk G.ℓ (Kc G.Kt G.ℓ) (G.tTerms i) (G.tSt i)
def tOut (i : ℕ) : List ℕ := cblkOut G.ℓ (G.tTerms i) (G.tSt i)

def oSt : ℕ := G.tS0 + G.n * G.tSize
def Ko : ℤ := 2 ^ (G.Vb - 1) - 2 ^ (G.Vf - G.fh - 1 + G.Bh)
def oTerms : List (List Spec) := [shiftSp (G.Vf - G.fh) G.Vb (copySpecs G.hReg)]
def oSize : ℕ := G.Vb + 1 * (3 * G.Vb + 1)
def oP : List Ins := cblk G.Vb (Kc G.Ko G.Vb) G.oTerms G.oSt
def oOut : List ℕ := cblkOut G.Vb G.oTerms G.oSt
def c0 : ℕ := G.oSt + G.oSize

def Ts0 : List (List ℕ) := (List.range G.n).map G.tOut ++ [G.oOut]
def eD (m : ℕ) : ℕ := m + G.f - G.q - 3 - G.f₁
def δ (j m : ℕ) : List Spec :=
  if j < G.n then (if m < G.q then sgnSpecs (G.pReg j) (G.eD m) G.ℓ else List.replicate G.ℓ zSp)
  else constSpecs (2 ^ (m + G.Vf - G.q - 2)) G.Vb

def initP : List Ins := blocks G.qP G.n ++ blocks G.tP G.n ++ G.oP
def prog : List Ins := G.initP ++ rP G.n G.ℓ G.sW G.δ G.q G.Ts0 G.c0
def cEnd : ℕ := rE G.n G.ℓ G.q G.Ts0 G.c0
def outR : List ℕ := (rT G.n G.ℓ G.q G.Ts0 G.c0).getD G.n []
def Pfull : List Ins := G.prog ++ copyOut G.outR G.vB G.Vb ++ G.prog.reverse
def W : ℕ := G.cEnd - G.base
def S (w : ℕ) : Prop := w < G.vB ∨ G.base ≤ w

/-- Format conditions. -/
structure WF : Prop where
  hf : G.r + G.b + G.fh + G.f₁ + G.q + 3 ≤ G.f
  hl : G.f + G.Bh + G.ℓ₁ + 3 ≤ G.ℓ

end Prm

end

end QuantumLTF.Membership.A2

-- ===== module U9 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

namespace Prm
variable (G : Prm)

/-! ### Sizes and wire bounds -/

theorem pReg_length (i : ℕ) : (G.pReg i).length = G.ℓ₁ := regLE_length _ _
theorem hReg_length : G.hReg.length = G.Bh := regLE_length _ _
theorem xReg_length (i : ℕ) : (G.xReg i).length = G.b := regLE_length _ _

theorem pReg_lt (i : ℕ) (hi : i < G.n) : ∀ a ∈ G.pReg i, a < G.sW := by
  intro a ha
  have := regLE_mem _ _ a ha
  have : G.ℓ₁ * i + G.ℓ₁ ≤ G.n * G.ℓ₁ := by
    rw [Nat.mul_comm G.n]; have := Nat.mul_le_mul_left G.ℓ₁ hi; rw [Nat.mul_succ] at this; omega
  simp only [sW]; omega

theorem hReg_mem (a : ℕ) (ha : a ∈ G.hReg) : G.hB ≤ a ∧ a < G.xB := by
  have := regLE_mem _ _ a ha; simp only [xB]; omega

theorem xReg_mem (i : ℕ) (hi : i < G.n) (a : ℕ) (ha : a ∈ G.xReg i) : G.xB ≤ a ∧ a < G.vB := by
  have := regLE_mem _ _ a ha
  have : G.b * i + G.b ≤ G.n * G.b := by
    rw [Nat.mul_comm G.n]; have := Nat.mul_le_mul_left G.b hi; rw [Nat.mul_succ] at this; omega
  simp only [vB]; omega

theorem sW_lt_hB : G.sW < G.hB := by simp [sW, hB]
theorem hB_le_xB : G.hB ≤ G.xB := by simp [xB]
theorem xB_le_vB : G.xB ≤ G.vB := by simp [vB]
theorem vB_le_base : G.vB ≤ G.base := by simp [base]

/-- Every input wire (p, s, htil, x) lies below `vB`. -/
def InW (a : ℕ) : Prop := a < G.vB

theorem qTerms_length (i : ℕ) : (G.qTerms i).length = G.Bh + 2 := by
  simp [qTerms, prodTerms_length, hReg_length]

theorem qTerms_len (i : ℕ) : ∀ t ∈ G.qTerms i, t.length = G.Kw := by
  intro t ht
  simp only [qTerms, List.mem_cons] at ht
  rcases ht with rfl | rfl | ht
  · apply shiftSp_length; simp [notSpecs, hReg_length, Kw]; omega
  · apply shiftSp_length; simp [notSpecs, pReg_length, Kw]; omega
  · obtain ⟨a, _, j, _, h2, rfl⟩ := prodTerms_mem _ _ _ _ t ht
    apply shiftSp_length; simp [andSpecs, pReg_length, Kw, hReg_length] at h2 ⊢; omega

theorem qTerms_src (i : ℕ) (hi : i < G.n) : ∀ t ∈ G.qTerms i, ∀ sp ∈ t, ∀ a, SpSrc sp a →
    G.InW a := by
  have hp := G.pReg_lt i hi
  have hs := G.sW_lt_hB; have h1 := G.hB_le_xB; have h2 := G.xB_le_vB
  intro t ht sp hsp a ha
  simp only [qTerms, List.mem_cons] at ht
  simp only [InW]
  rcases ht with rfl | rfl | ht
  · obtain ⟨sp', hsp', ha'⟩ := shiftSp_src _ _ _ a sp hsp ha
    simp only [notSpecs, List.mem_map] at hsp'
    obtain ⟨b, hb, rfl⟩ := hsp'
    rw [SpSrc_ngSp _ _ ha']; have := G.hReg_mem b hb; omega
  · obtain ⟨sp', hsp', ha'⟩ := shiftSp_src _ _ _ a sp hsp ha
    simp only [notSpecs, List.mem_map] at hsp'
    obtain ⟨b, hb, rfl⟩ := hsp'
    rw [SpSrc_ngSp _ _ ha']; have := hp b hb; omega
  · obtain ⟨c, hc, j, _, _, rfl⟩ := prodTerms_mem _ _ _ _ t ht
    obtain ⟨sp', hsp', ha'⟩ := shiftSp_src _ _ _ a sp hsp ha
    simp only [andSpecs, List.mem_map] at hsp'
    obtain ⟨b, hb, rfl⟩ := hsp'
    rcases SpSrc_anSp _ _ _ ha' with rfl | rfl
    · have := G.hReg_mem a hc; omega
    · have := hp a hb; omega

theorem qTerms_terms (i : ℕ) : ∀ t ∈ G.qTerms i, ∀ sp ∈ t, sp.2.length ≤ 1 := by
  intro t ht
  simp only [qTerms, List.mem_cons] at ht
  rcases ht with rfl | rfl | ht
  · apply shiftSp_terms; intro sp hsp; simp only [notSpecs, List.mem_map] at hsp
    obtain ⟨b, _, rfl⟩ := hsp; simp [ngSp]
  · apply shiftSp_terms; intro sp hsp; simp only [notSpecs, List.mem_map] at hsp
    obtain ⟨b, _, rfl⟩ := hsp; simp [ngSp]
  · obtain ⟨c, _, j, _, _, rfl⟩ := prodTerms_mem _ _ _ _ t ht
    apply shiftSp_terms; intro sp hsp; simp only [andSpecs, List.mem_map] at hsp
    obtain ⟨b, _, rfl⟩ := hsp; simp [anSp]

theorem qSize_eq (i : ℕ) : cblkSize G.Kw (G.qTerms i) = G.qSize := by
  simp [cblkSize, qSize, qTerms_length]

theorem qOut_length (i : ℕ) : (G.qOut i).length = G.Kw := cblkOut_length _ _ _

theorem qOut_bound (i : ℕ) : ∀ a ∈ G.qOut i, G.qSt i ≤ a ∧ a < G.qSt i + G.qSize := by
  intro a ha; have := cblkOut_bound _ _ _ a ha; rw [qSize_eq] at this; exact this

theorem qSt_succ (i : ℕ) : G.qSt i + G.qSize = G.base + (i + 1) * G.qSize := by
  simp only [qSt]; ring

theorem qOut_lt (i : ℕ) (hi : i < G.n) : ∀ a ∈ G.qOut i, G.base ≤ a ∧ a < G.tS0 := by
  intro a ha
  have := G.qOut_bound i a ha
  have h2 : (i + 1) * G.qSize ≤ G.n * G.qSize := Nat.mul_le_mul_right _ hi
  rw [qSt_succ] at this
  simp only [qSt, tS0] at *; constructor <;> omega

theorem tTerms_len (W : G.WF) (i : ℕ) : ∀ t ∈ G.tTerms i, t.length = G.ℓ := by
  have h1 := W.hf; have h2 := W.hl
  intro t ht
  simp only [tTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · apply shiftSp_length; simp [copySpecs, xReg_length]; omega
  · apply shiftSp_length; simp [copySpecs, qOut_length, Kw, eQ]; omega

theorem tTerms_src (i : ℕ) (hi : i < G.n) : ∀ t ∈ G.tTerms i, ∀ sp ∈ t, ∀ a, SpSrc sp a →
    a < G.tS0 ∧ G.S a := by
  intro t ht sp hsp a ha
  simp only [tTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · obtain ⟨sp', hsp', ha'⟩ := shiftSp_src _ _ _ a sp hsp ha
    have := copySpecs_src' _ sp' hsp' a ha'
    have := G.xReg_mem i hi a this
    have : G.vB ≤ G.tS0 := by simp [tS0, base]; omega
    exact ⟨by omega, Or.inl (by omega)⟩
  · obtain ⟨sp', hsp', ha'⟩ := shiftSp_src _ _ _ a sp hsp ha
    have := copySpecs_src' _ sp' hsp' a ha'
    have := G.qOut_lt i hi a this
    exact ⟨this.2, Or.inr this.1⟩

theorem tTerms_terms (i : ℕ) : ∀ t ∈ G.tTerms i, ∀ sp ∈ t, sp.2.length ≤ 1 := by
  intro t ht
  simp only [tTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;>
  · apply shiftSp_terms; intro sp hsp; simp only [copySpecs, List.mem_map] at hsp
    obtain ⟨b, _, rfl⟩ := hsp; simp [cpSp]

theorem tSize_eq (i : ℕ) : cblkSize G.ℓ (G.tTerms i) = G.tSize := by
  simp [cblkSize, tSize, tTerms]

theorem tOut_length (i : ℕ) : (G.tOut i).length = G.ℓ := cblkOut_length _ _ _

theorem tSt_succ (i : ℕ) : G.tSt i + G.tSize = G.tS0 + (i + 1) * G.tSize := by
  simp only [tSt]; ring

theorem tOut_lt (i : ℕ) (hi : i < G.n) : ∀ a ∈ G.tOut i, G.tS0 ≤ a ∧ a < G.oSt := by
  intro a ha
  have := cblkOut_bound _ _ _ a ha
  rw [tSize_eq, tSt_succ] at this
  have h2 : (i + 1) * G.tSize ≤ G.n * G.tSize := Nat.mul_le_mul_right _ hi
  simp only [tSt, oSt] at *; constructor <;> omega

theorem oTerms_len : ∀ t ∈ G.oTerms, t.length = G.Vb := by
  intro t ht
  simp only [oTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  apply shiftSp_length; simp [copySpecs, hReg_length, Vb, Vf]; omega

theorem oTerms_src : ∀ t ∈ G.oTerms, ∀ sp ∈ t, ∀ a, SpSrc sp a → G.InW a := by
  intro t ht sp hsp a ha
  simp only [oTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  obtain ⟨sp', hsp', ha'⟩ := shiftSp_src _ _ _ a sp hsp ha
  have := copySpecs_src' _ sp' hsp' a ha'
  have := G.hReg_mem a this; have := G.xB_le_vB
  simp only [InW]; omega

theorem oTerms_terms : ∀ t ∈ G.oTerms, ∀ sp ∈ t, sp.2.length ≤ 1 := by
  intro t ht
  simp only [oTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  apply shiftSp_terms; intro sp hsp; simp only [copySpecs, List.mem_map] at hsp
  obtain ⟨b, _, rfl⟩ := hsp; simp [cpSp]

theorem oSize_eq : cblkSize G.Vb G.oTerms = G.oSize := by simp [cblkSize, oSize, oTerms]

theorem oOut_length : G.oOut.length = G.Vb := cblkOut_length _ _ _

theorem oOut_lt : ∀ a ∈ G.oOut, G.oSt ≤ a ∧ a < G.c0 := by
  intro a ha
  have := cblkOut_bound _ _ _ a ha
  rw [oSize_eq] at this; simp only [c0]; exact this

theorem base_le_tS0 : G.base ≤ G.tS0 := by simp [tS0]
theorem tS0_le_oSt : G.tS0 ≤ G.oSt := by simp [oSt]
theorem oSt_le_c0 : G.oSt ≤ G.c0 := by simp [c0]

theorem Vb_le_ℓ (W : G.WF) : G.Vb ≤ G.ℓ := by
  have h1 := W.hf; have h2 := W.hl; simp only [Vb, Vf]; omega

/-! ### The initial tracks -/

theorem Ts0_length : G.Ts0.length = G.n + 1 := by simp [Ts0]

theorem Ts0_getD_lt (j : ℕ) (hj : j < G.n) : G.Ts0.getD j [] = G.tOut j := by
  rw [Ts0, List.getD_append _ _ _ _ (by simp; exact hj)]
  rw [List.getD_eq_getElem _ _ (by simp; exact hj)]; simp

theorem Ts0_getD_n : G.Ts0.getD G.n [] = G.oOut := by
  rw [Ts0, List.getD_append_right _ _ _ _ (by simp)]; simp

theorem Ts0_take : G.Ts0.take G.n = (List.range G.n).map G.tOut := by
  rw [Ts0, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]

theorem Ts0_wires : ∀ R ∈ G.Ts0, ∀ a ∈ R, G.tS0 ≤ a ∧ a < G.c0 := by
  intro R hR a ha
  simp only [Ts0, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hR
  rcases hR with ⟨i, hi, rfl⟩ | rfl
  · have := G.tOut_lt i hi a ha; have := G.oSt_le_c0; omega
  · have := G.oOut_lt a ha; have := G.tS0_le_oSt; omega

theorem Ts0_take_len : ∀ R ∈ G.Ts0.take G.n, R.length = G.ℓ := by
  rw [Ts0_take]
  intro R hR
  simp only [List.mem_map, List.mem_range] at hR
  obtain ⟨i, _, rfl⟩ := hR
  exact G.tOut_length i

theorem Ts0_len_le (W : G.WF) : ∀ R ∈ G.Ts0, R.length ≤ G.ℓ := by
  intro R hR
  simp only [Ts0, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hR
  rcases hR with ⟨i, _, rfl⟩ | rfl
  · rw [tOut_length]
  · rw [oOut_length]; exact G.Vb_le_ℓ W

theorem δ_length (W : G.WF) (t m : ℕ) (ht : t < G.Ts0.length) :
    (G.δ t m).length = (G.Ts0.getD t []).length := by
  have h1 := W.hf; have h2 := W.hl
  rw [Ts0_length] at ht
  unfold δ
  by_cases h : t < G.n
  · rw [if_pos h, Ts0_getD_lt _ _ h, tOut_length]
    split_ifs with hm
    · apply sgnSpecs_length; rw [pReg_length]; simp only [eD]; omega
    · simp
  · have : t = G.n := by omega
    subst this
    rw [if_neg (lt_irrefl _), Ts0_getD_n, oOut_length, constSpecs_length]

theorem δ_src (t m : ℕ) : ∀ sp ∈ G.δ t m, ∀ a, SpSrc sp a → G.InW a := by
  intro sp hsp a ha
  unfold δ at hsp
  split_ifs at hsp with h1 h2
  · have := sgnSpecs_src _ _ _ sp hsp a ha
    have := G.pReg_lt t h1 a this
    have := G.sW_lt_hB; have := G.hB_le_xB; have := G.xB_le_vB
    simp only [InW]; omega
  · simp only [List.mem_replicate] at hsp; rw [hsp.2] at ha; exact absurd ha (SpSrc_zSp a)
  · exact absurd ha (constSpecs_src _ _ sp hsp a)

theorem δ_terms (t m : ℕ) : ∀ sp ∈ G.δ t m, sp.2.length ≤ 1 := by
  intro sp hsp
  unfold δ at hsp
  split_ifs at hsp with h1 h2
  · exact sgnSpecs_terms _ _ _ sp hsp
  · simp only [List.mem_replicate] at hsp; rw [hsp.2]; simp [zSp]
  · rw [constSpecs_terms _ _ sp hsp]; omega

/-! ### Well-formedness of the program -/

theorem c0_le_cEnd : G.c0 ≤ G.cEnd := rE_ge _ _ _ _ _

theorem outR_length : G.outR.length = G.Vb := by
  rw [outR, rT_getD_length, Ts0_getD_n, oOut_length]

theorem outR_wires : ∀ a ∈ G.outR, G.base ≤ a ∧ a < G.cEnd := by
  intro a ha
  have hmem : G.outR ∈ rT G.n G.ℓ G.q G.Ts0 G.c0 := by
    rw [outR, List.getD_eq_getElem _ _ (by rw [rT_length, Ts0_length]; omega)]
    exact List.getElem_mem _
  have := G.c0_le_cEnd
  have := G.base_le_tS0; have := G.tS0_le_oSt; have := G.oSt_le_c0
  rcases rT_bound G.n G.ℓ G.q G.Ts0 G.c0 G.outR hmem a ha with ⟨R0, h0, ha0⟩ | h
  · have := G.Ts0_wires R0 h0 a ha0
    simp only [cEnd] at *; omega
  · simp only [cEnd] at *; omega

theorem prog_good (W : G.WF) : ∀ I ∈ G.prog, Good (G.n * G.ℓ) G.S G.base G.cEnd I := by
  set A := G.n * G.ℓ
  have hc0 := G.c0_le_cEnd
  have e1 := G.base_le_tS0; have e2 := G.tS0_le_oSt; have e3 := G.oSt_le_c0
  have hS : ∀ w, G.base ≤ w → G.S w := fun w h => Or.inr h
  have hin : ∀ a, G.InW a → a < G.base ∧ G.S a := fun a h => by
    simp only [InW] at h; have := G.vB_le_base; exact ⟨by omega, Or.inl h⟩
  intro I hI
  simp only [prog, initP, List.mem_append] at hI
  rcases hI with ((hI | hI) | hI) | hI
  · have := blocks_good A G.S G.qP G.base G.qSize G.n (fun i hi I hI => by
      have := cblk_good A G.S G.Kw 0 (G.qTerms i) (G.qSt i) (G.qTerms_len i)
        (fun t ht sp hsp a ha => by
          have := hin a (G.qTerms_src i hi t ht sp hsp a ha)
          exact ⟨by simp only [qSt]; omega, this.2⟩)
        (fun w hw => hS w (by simp only [qSt] at hw; omega)) I hI
      rw [qSize_eq, qSt_succ] at this
      exact this.mono le_rfl le_rfl) I hI
    exact this.mono le_rfl (by simp only [tS0] at *; omega)
  · have := blocks_good A G.S G.tP G.tS0 G.tSize G.n (fun i hi I hI => by
      have := cblk_good A G.S G.ℓ (Kc G.Kt G.ℓ) (G.tTerms i) (G.tSt i) (G.tTerms_len W i)
        (fun t ht sp hsp a ha => by
          have := G.tTerms_src i hi t ht sp hsp a ha
          exact ⟨by simp only [tSt]; omega, this.2⟩)
        (fun w hw => hS w (by simp only [tSt] at hw; omega)) I hI
      rw [tSize_eq, tSt_succ] at this
      exact this.mono le_rfl le_rfl) I hI
    exact this.mono (by omega) (by simp only [oSt] at *; omega)
  · have := cblk_good A G.S G.Vb (Kc G.Ko G.Vb) G.oTerms G.oSt G.oTerms_len
      (fun t ht sp hsp a ha => by
        have := hin a (G.oTerms_src t ht sp hsp a ha); exact ⟨by omega, this.2⟩)
      (fun w hw => hS w (by omega)) I hI
    rw [oSize_eq] at this
    exact this.mono (by omega) (by simp only [c0] at *; omega)
  · have := rP_good G.n G.ℓ G.sW G.δ G.S G.q G.Ts0 G.c0 G.Ts0_take_len
      (fun R h a ha => by
        have := G.Ts0_wires R h a ha
        exact ⟨this.2, hS a (by omega)⟩)
      (fun w hw => hS w (by omega))
      (by
        have h1 := G.sW_lt_hB; have h2 := G.hB_le_xB; have h3 := G.xB_le_vB
        have h4 := G.vB_le_base
        exact ⟨by omega, Or.inl (by omega)⟩)
      (fun t m' ht => G.δ_length W t m' ht)
      (fun t m' sp hsp a ha => by
        have := hin a (G.δ_src t m' sp hsp a ha); exact ⟨by omega, this.2⟩) I hI
    exact this.mono (by omega) le_rfl

theorem prog_countQ : G.prog.countP Ins.isQ = G.q := by
  have h1 : (G.initP).countP Ins.isQ = 0 := by
    apply List.countP_eq_zero.mpr
    intro I hI
    simp only [initP, List.mem_append] at hI
    rcases hI with (hI | hI) | hI
    · simp [blocks_noQ G.qP G.n (fun i _ => cblk_noQ _ _ _ _) I hI]
    · simp [blocks_noQ G.tP G.n (fun i _ => cblk_noQ _ _ _ _) I hI]
    · simp [cblk_noQ _ _ _ _ I hI]
  simp only [prog, List.countP_append, h1, rP_countQ]; omega

theorem Pfull_countQ : G.Pfull.countP Ins.isQ = 2 * G.q := by
  have h3 : (copyOut G.outR G.vB G.Vb).countP Ins.isQ = 0 :=
    List.countP_eq_zero.mpr (fun I hI => by simp [copyOut_noQ _ _ _ I hI])
  simp only [Pfull, List.countP_append, List.countP_reverse, h3, prog_countQ]; omega

theorem prog_length (W : G.WF) :
    G.prog.length ≤ G.n * (9 * (G.Bh + 2) * G.Kw) + G.n * (17 * G.ℓ) + 9 * G.Vb +
      G.q * (2 * G.ℓ * G.n + 2 + 9 * G.ℓ * (G.n + 1)) := by
  have h1 := blocks_length G.qP G.n (9 * (G.Bh + 2) * G.Kw) (fun i _ => by
    have := cblk_length G.Kw 0 (G.qTerms i) (G.qSt i) 1 (G.qTerms_len i) (G.qTerms_terms i)
    rw [qTerms_length] at this
    simp only [qP]
    have hK : G.Kw ≤ (G.Bh + 2) * G.Kw := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith)
  have h2 := blocks_length G.tP G.n (17 * G.ℓ) (fun i _ => by
    have := cblk_length G.ℓ (Kc G.Kt G.ℓ) (G.tTerms i) (G.tSt i) 1 (G.tTerms_len W i)
      (G.tTerms_terms i)
    rw [show (G.tTerms i).length = 2 from rfl] at this
    simp only [tP]; omega)
  have h3 := cblk_length G.Vb (Kc G.Ko G.Vb) G.oTerms G.oSt 1 G.oTerms_len G.oTerms_terms
  rw [show G.oTerms.length = 1 from rfl] at h3
  have h4 := rP_length G.n G.ℓ G.sW G.δ G.ℓ 1 G.q G.Ts0 G.c0 G.Ts0_take_len (G.Ts0_len_le W)
    (fun t m' ht => G.δ_length W t m' ht) (fun t m' => G.δ_terms t m')
  rw [Ts0_length, show (1 : ℕ) + 8 = 9 from rfl] at h4
  simp only [prog, initP, List.length_append]
  simp only [oP]
  omega

theorem Pfull_length (W : G.WF) (hn : 1 ≤ G.n) :
    G.Pfull.length ≤ 18 * G.n * (G.Bh + 2) * G.Kw + 54 * G.n * G.ℓ * (G.q + 1) := by
  have h := G.prog_length W
  have hV := G.Vb_le_ℓ W
  have hl : 1 ≤ G.ℓ := by have := W.hl; omega
  simp only [Pfull, List.length_append, List.length_reverse, copyOut_length]
  have e1 : G.q * (2 * G.ℓ * G.n + 2 + 9 * G.ℓ * (G.n + 1)) ≤ G.q * (22 * G.n * G.ℓ) := by
    apply Nat.mul_le_mul_left
    have : 2 ≤ 2 * G.ℓ * G.n := by nlinarith
    nlinarith
  have e3 : G.Vb ≤ G.n * G.ℓ := by nlinarith
  have r1 : G.q * (22 * G.n * G.ℓ) = 22 * (G.q * (G.n * G.ℓ)) := by ring
  have r2 : 54 * G.n * G.ℓ * (G.q + 1) = 54 * (G.q * (G.n * G.ℓ)) + 54 * (G.n * G.ℓ) := by ring
  have r3 : G.n * (17 * G.ℓ) = 17 * (G.n * G.ℓ) := by ring
  have r4 : G.n * (9 * (G.Bh + 2) * G.Kw) = 9 * (G.n * (G.Bh + 2) * G.Kw) := by ring
  have r5 : 18 * G.n * (G.Bh + 2) * G.Kw = 18 * (G.n * (G.Bh + 2) * G.Kw) := by ring
  rw [r2, r5]
  rw [r1] at e1
  rw [r3, r4] at h
  omega

end Prm

end

end QuantumLTF.Membership.A2

-- ===== module U10 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

theorem bitsToNat_lt' {b : ℕ} (z : Qubits b) : bitsToNat z < 2 ^ b := by
  rw [← bitsEquivFin_apply]; exact (bitsEquivFin b z).isLt

theorem ltf_pm {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ltf w θ y = 1 ∨ ltf w θ y = -1 := by
  unfold ltf sgn; split_ifs <;> simp

theorem rho_eq (n : ℕ) : rho n = (2 : ℝ)⁻¹ ^ ⌈Real.logb 2 (40 * Real.sqrt n)⌉₊ := rfl

theorem gridPoint_scaled (b r o' : ℕ) (z : Qubits b) :
    (2 : ℝ) ^ (r + b + (o' + 1)) * ((2 : ℝ)⁻¹ ^ r * gridPoint b z) =
      2 ^ (o' + 1) * (bitsToNat z : ℝ) + 2 ^ o' * (1 - 2 ^ b) := by
  simp only [gridPoint, pow_add, pow_succ, inv_pow]
  field_simp
  ring

theorem abs_rho_grid_le (b r : ℕ) (z : Qubits b) :
    |(2 : ℝ)⁻¹ ^ r * gridPoint b z| ≤ 1 / 2 := by
  have hX := bitsToNat_lt' z
  have hX' : (bitsToNat z : ℝ) + 1 ≤ 2 ^ b := by exact_mod_cast hX
  have hpos : (0 : ℝ) < 2 ^ b := by positivity
  have hg : |gridPoint b z| ≤ 1 / 2 := by
    simp only [gridPoint, pow_succ]
    rw [abs_le]
    constructor
    · have : (0 : ℝ) ≤ (bitsToNat z : ℝ) * (2 ^ b)⁻¹ := by positivity
      have : (0 : ℝ) ≤ (2 ^ b * 2 : ℝ)⁻¹ := by positivity
      linarith
    · have h1 : (bitsToNat z : ℝ) * (2 ^ b)⁻¹ ≤ 1 - (2 ^ b)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ hpos]
        have : (1 - (2 : ℝ) ^ b)⁻¹ = (1 - (2 : ℝ) ^ b)⁻¹ := rfl
        field_simp
        linarith
      have h2 : (2 ^ b * 2 : ℝ)⁻¹ = (2 ^ b)⁻¹ / 2 := by field_simp
      have h3 : (0 : ℝ) ≤ (2 ^ b)⁻¹ := by positivity
      rw [h2]; linarith
  have hr : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ r := by positivity
  have hr1 : (2 : ℝ)⁻¹ ^ r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [abs_mul, abs_of_nonneg hr]
  calc (2 : ℝ)⁻¹ ^ r * |gridPoint b z| ≤ 1 * |gridPoint b z| :=
        mul_le_mul_of_nonneg_right hr1 (abs_nonneg _)
    _ ≤ 1 / 2 := by linarith


namespace Prm
variable (G : Prm)

/-- The input wires hold `zp, sb, hb, x`, and all work wires are fresh. -/
structure Inp (zp : Qubits (G.n * G.ℓ₁)) (sb : Bool) (hb : Qubits G.Bh)
    (x : Fin G.n → Qubits G.b) (Z0 : ℕ → Bool) : Prop where
  hp : ∀ (i : Fin G.n) (j : Fin G.ℓ₁), Z0 (G.ℓ₁ * i + j) = splitReg G.n G.ℓ₁ zp i j
  hs : Z0 G.sW = sb
  hh : ∀ j : Fin G.Bh, Z0 (G.hB + j) = hb j
  hx : ∀ (i : Fin G.n) (j : Fin G.b), Z0 (G.xB + G.b * i + j) = x i j
  hF : Fresh Z0 G.base

section
variable {G} {zp : Qubits (G.n * G.ℓ₁)} {sb : Bool} {hb : Qubits G.Bh}
  {x : Fin G.n → Qubits G.b} {Z0 : ℕ → Bool}

theorem Inp.valP (I : G.Inp zp sb hb x Z0) (i : Fin G.n) :
    valLE ((G.pReg i).map Z0) = bitsToNat (splitReg G.n G.ℓ₁ zp i) :=
  (valLE_regLE _ _ Z0 _ (fun j => (I.hp i j).symm)).symm

theorem Inp.valH (I : G.Inp zp sb hb x Z0) : valLE (G.hReg.map Z0) = bitsToNat hb :=
  (valLE_regLE _ _ Z0 _ (fun j => (I.hh j).symm)).symm

theorem Inp.valX (I : G.Inp zp sb hb x Z0) (i : Fin G.n) :
    valLE ((G.xReg i).map Z0) = bitsToNat (x i) :=
  (valLE_regLE _ _ Z0 _ (fun j => (I.hx i j).symm)).symm

end

theorem qsum_lt (A B nH H nN N : ℕ) (h1 : nH + H + 1 = A) (h2 : nN + N + 1 = B) :
    2 * B * nH + 2 * A * nN + 4 * H * N < 8 * A * B := by
  subst h1; subst h2; nlinarith

theorem qsum_eq (A B nH H nN N : ℕ) (h1 : nH + H + 1 = A) (h2 : nN + N + 1 = B) :
    ((2 * B * nH + 2 * A * nN + 4 * H * N : ℕ) : ℤ) +
      ((A * B : ℤ) - 2 * B * (A - 1) - 2 * A * (B - 1)) =
      (2 * (H : ℤ) - A) * (2 * (N : ℤ) - B) := by
  have e1 : (nH : ℤ) = A - 1 - H := by have := congrArg (fun t : ℕ => (t : ℤ)) h1; push_cast at this; linarith
  have e2 : (nN : ℤ) = B - 1 - N := by have := congrArg (fun t : ℕ => (t : ℤ)) h2; push_cast at this; linarith
  push_cast; rw [e1, e2]; ring

theorem Kp_eq : G.Kp = ((2 : ℤ) ^ G.Bh * 2 ^ G.ℓ₁ - 2 * 2 ^ G.ℓ₁ * (2 ^ G.Bh - 1) -
    2 * 2 ^ G.Bh * (2 ^ G.ℓ₁ - 1)) := by
  simp only [Kp, pow_add, pow_succ]; ring

section
variable (A : ℕ) (O : Qubits A → Bool)
variable {G} {zp : Qubits (G.n * G.ℓ₁)} {sb : Bool} {hb : Qubits G.Bh}
  {x : Fin G.n → Qubits G.b} {Z0 : ℕ → Bool}

/-- The value of the product register of coordinate `i`. -/
def qVal (zp : Qubits (G.n * G.ℓ₁)) (hb : Qubits G.Bh) (i : Fin G.n) : ℤ :=
  (2 * (bitsToNat hb : ℤ) - 2 ^ G.Bh) * (2 * (bitsToNat (splitReg G.n G.ℓ₁ zp i) : ℤ) - 2 ^ G.ℓ₁)
    - G.Kp

theorem qsum_val (I : G.Inp zp sb hb x Z0) (i : Fin G.n) :
    ((sumV Z0 (G.qTerms i) : ℕ) : ℤ) = qVal zp hb i ∧ sumV Z0 (G.qTerms i) < 2 ^ G.Kw := by
  have hH := notSpecs_val Z0 G.hReg
  have hN := notSpecs_val Z0 (G.pReg i)
  rw [G.hReg_length, I.valH] at hH
  rw [G.pReg_length, I.valP] at hN
  have hs : sumV Z0 (G.qTerms i) =
      2 * 2 ^ G.ℓ₁ * valLE ((notSpecs G.hReg).map (specVal Z0)) +
      2 * 2 ^ G.Bh * valLE ((notSpecs (G.pReg i)).map (specVal Z0)) +
      4 * bitsToNat hb * bitsToNat (splitReg G.n G.ℓ₁ zp i) := by
    simp only [qTerms, sumV, shiftSp_val, prodTerms_sumV, I.valH, I.valP, pow_succ, pow_add]
    ring
  rw [hs]
  constructor
  · have e := qsum_eq _ _ _ _ _ _ hH hN
    rw [qVal, Kp_eq]; push_cast at e ⊢; linarith
  · have := qsum_lt _ _ _ _ _ _ hH hN
    have e : 2 ^ G.Kw = 8 * 2 ^ G.Bh * 2 ^ G.ℓ₁ := by
      simp only [Kw, pow_add, pow_succ]; ring
    rw [e]; linarith

theorem qblocks_sem (I : G.Inp zp sb hb x Z0) :
    (∀ w, w < G.base → evalP A O (blocks G.qP G.n) Z0 w = Z0 w) ∧
    Fresh (evalP A O (blocks G.qP G.n) Z0) G.tS0 ∧
    ∀ i : Fin G.n, (valLE ((G.qOut i).map (evalP A O (blocks G.qP G.n) Z0)) : ℤ) =
      qVal zp hb i := by
  have hvb := G.vB_le_base
  obtain ⟨B1, B2, B3⟩ := blocks_sem A O G.qP G.base G.qSize
    (fun i Z => valLE ((G.qOut i).map Z) = sumV Z0 (G.qTerms i) % 2 ^ G.Kw)
    (fun i Z1 Z2 h hP => by
      rw [← hP]; congr 1; apply List.map_congr_left; intro a ha
      have := G.qOut_bound i a ha; rw [qSt_succ] at this
      exact (h a (by simp only [qSt] at this; omega) this.2).symm)
    Z0 G.n (fun i hi Z' hF' hZ' => by
      obtain ⟨C1, C2, C3⟩ := cblk_sem A O Z0 G.vB G.Kw 0 (G.qTerms i) (G.qSt i) Z'
        (by simp only [qSt]; omega) (G.qTerms_len i)
        (fun t ht sp hsp a ha => G.qTerms_src i hi t ht sp hsp a ha)
        (fun v hv => hZ' v (by omega)) (by simpa [qSt] using hF')
      refine ⟨fun v hv => C1 v (by simpa [qSt] using hv), ?_, ?_⟩
      · rw [qSize_eq, qSt_succ] at C2; exact C2
      · rw [qP, qOut, C3, Nat.zero_add])
    I.hF
  refine ⟨B1, by simpa [tS0] using B2, fun i => ?_⟩
  rw [B3 i i.isLt, Nat.mod_eq_of_lt (qsum_val I i).2]
  exact (qsum_val I i).1

theorem tblocks_sem (W : G.WF) (ZA : ℕ → Bool) (hF : Fresh ZA G.tS0) :
    (∀ w, w < G.tS0 → evalP A O (blocks G.tP G.n) ZA w = ZA w) ∧
    Fresh (evalP A O (blocks G.tP G.n) ZA) G.oSt ∧
    ∀ i : Fin G.n, valLE ((G.tOut i).map (evalP A O (blocks G.tP G.n) ZA)) =
      (Kc G.Kt G.ℓ + (2 ^ (G.f - G.r - G.b) * valLE ((G.xReg i).map ZA) +
        2 ^ G.eQ * valLE ((G.qOut i).map ZA))) % 2 ^ G.ℓ := by
  obtain ⟨B1, B2, B3⟩ := blocks_sem A O G.tP G.tS0 G.tSize
    (fun i Z => valLE ((G.tOut i).map Z) = (Kc G.Kt G.ℓ + sumV ZA (G.tTerms i)) % 2 ^ G.ℓ)
    (fun i Z1 Z2 h hP => by
      rw [← hP]; congr 1; apply List.map_congr_left; intro a ha
      have := cblkOut_bound _ _ _ a ha; rw [tSize_eq, tSt_succ] at this
      exact (h a (by simp only [tSt] at this; omega) this.2).symm)
    ZA G.n (fun i hi Z' hF' hZ' => by
      obtain ⟨C1, C2, C3⟩ := cblk_sem A O ZA G.tS0 G.ℓ (Kc G.Kt G.ℓ) (G.tTerms i) (G.tSt i) Z'
        (by simp only [tSt]; omega) (G.tTerms_len W i)
        (fun t ht sp hsp a ha => (G.tTerms_src i hi t ht sp hsp a ha).1)
        hZ' (by simpa [tSt] using hF')
      refine ⟨fun v hv => C1 v (by simpa [tSt] using hv), ?_, ?_⟩
      · rw [tSize_eq, tSt_succ] at C2; exact C2
      · rw [tP, tOut, C3])
    hF
  refine ⟨B1, by simpa [oSt] using B2, fun i => ?_⟩
  rw [B3 i i.isLt]
  simp [tTerms, sumV, shiftSp_val, copySpecs_map]

theorem oblock_sem (ZB : ℕ → Bool) (hF : Fresh ZB G.oSt) :
    (∀ w, w < G.oSt → evalP A O G.oP ZB w = ZB w) ∧
    Fresh (evalP A O G.oP ZB) G.c0 ∧
    valLE (G.oOut.map (evalP A O G.oP ZB)) =
      (Kc G.Ko G.Vb + 2 ^ (G.Vf - G.fh) * valLE (G.hReg.map ZB)) % 2 ^ G.Vb := by
  have := G.tS0_le_oSt
  obtain ⟨C1, C2, C3⟩ := cblk_sem A O ZB G.oSt G.Vb (Kc G.Ko G.Vb) G.oTerms G.oSt ZB le_rfl
    G.oTerms_len (fun t ht sp hsp a ha => by
      have := G.oTerms_src t ht sp hsp a ha
      simp only [InW] at this; have := G.vB_le_base; have := G.base_le_tS0; omega)
    (fun _ _ => rfl) hF
  refine ⟨C1, by rw [oSize_eq] at C2; exact C2, ?_⟩
  rw [oP, oOut, C3]
  simp [oTerms, sumV, shiftSp_val, copySpecs_map]

end

end Prm

end

end QuantumLTF.Membership.A2

-- ===== module U11 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

/-! ### Real-number identities -/

theorem fpVal_eq (B f : ℕ) (z : Qubits B) :
    fpVal B f z = (2 * (bitsToNat z : ℝ) - 2 ^ B) / 2 ^ (f + 1) := by
  simp only [fpVal, pow_succ]; field_simp

theorem abs_fpVal_le (B f : ℕ) (z : Qubits B) : |fpVal B f z| ≤ 2 ^ B := by
  have hN := bitsToNat_lt' z
  have hN' : (bitsToNat z : ℝ) + 1 ≤ 2 ^ B := by exact_mod_cast hN
  have h0 : (0 : ℝ) ≤ bitsToNat z := by positivity
  have hf : (1 : ℝ) ≤ 2 ^ f := one_le_pow₀ (by norm_num)
  have hB : (0 : ℝ) < 2 ^ B := by positivity
  simp only [fpVal]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ f), div_le_iff₀ (by positivity)]
  have : |(bitsToNat z : ℝ) - 2 ^ B / 2| ≤ 2 ^ B := by
    rw [abs_le]; constructor <;> linarith
  nlinarith

theorem grid_track (f r b : ℕ) (h : r + b + 1 ≤ f) (z : Qubits b) :
    (2 : ℝ) ^ f * ((2 : ℝ)⁻¹ ^ r * gridPoint b z) =
      2 ^ (f - r - b) * (bitsToNat z : ℝ) - 2 ^ (f - r - 1) + 2 ^ (f - r - b - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, f = a + r + b + 1 := ⟨f - r - b - 1, by omega⟩
  rw [show a + r + b + 1 - r - b = a + 1 by omega, show a + r + b + 1 - r - 1 = a + b by omega,
    show a + 1 - 1 = a by omega]
  simp only [gridPoint, pow_add, pow_succ, inv_pow]
  field_simp
  try ring

theorem prod_track (f fh f₁ eQ Bh ℓ₁ : ℕ) (h : f = eQ + fh + f₁ + 2) (H N : ℕ) :
    (2 : ℝ) ^ f * (((H : ℝ) - 2 ^ Bh / 2) / 2 ^ fh * (((N : ℝ) - 2 ^ ℓ₁ / 2) / 2 ^ f₁)) =
      2 ^ eQ * ((2 * (H : ℝ) - 2 ^ Bh) * (2 * (N : ℝ) - 2 ^ ℓ₁)) := by
  subst h
  simp only [pow_add, pow_succ]
  field_simp

theorem out_track (Vf fh Bh : ℕ) (h : fh + 1 ≤ Vf) (H : ℕ) :
    (2 : ℝ) ^ Vf * (((H : ℝ) - 2 ^ Bh / 2) / 2 ^ fh) =
      2 ^ (Vf - fh) * (H : ℝ) - 2 ^ (Vf - fh - 1 + Bh) := by
  obtain ⟨a, rfl⟩ : ∃ a, Vf = a + fh + 1 := ⟨Vf - fh - 1, by omega⟩
  rw [show a + fh + 1 - fh = a + 1 by omega, show a + 1 - 1 + Bh = a + Bh by omega]
  simp only [pow_add, pow_succ]
  field_simp
  try ring

theorem delta_coord (f f₁ q m : ℕ) (h : q + 3 + f₁ ≤ f) (N ℓ₁ : ℕ) :
    ((2 ^ (m + f - q - 3 - f₁) * (2 * (N : ℤ) - 2 ^ ℓ₁) : ℤ) : ℝ) =
      2 ^ f * (((N : ℝ) - 2 ^ ℓ₁ / 2) / 2 ^ f₁) * 2 ^ m / 2 ^ (q + 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, f = a + q + 3 + f₁ := ⟨f - q - 3 - f₁, by omega⟩
  rw [show m + (a + q + 3 + f₁) - q - 3 - f₁ = m + a by omega]
  push_cast
  simp only [pow_add, pow_succ]
  field_simp
  try ring

theorem delta_out (Vf q m : ℕ) (h : q + 2 ≤ Vf) :
    (((2 ^ (m + Vf - q - 2) : ℕ) : ℤ) : ℝ) = 2 ^ Vf * 1 * 2 ^ m / 2 ^ (q + 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, Vf = a + q + 2 := ⟨Vf - q - 2, by omega⟩
  rw [show m + (a + q + 2) - q - 2 = m + a by omega]
  push_cast
  simp only [pow_add, pow_succ]
  field_simp

end

end QuantumLTF.Membership.A2

-- ===== module U12 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

namespace Prm
variable (G : Prm)

def Oc (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) : Qubits (G.n * G.ℓ) → Bool :=
  fun y => decide (ltf w θ (addrOf G.n G.ℓ G.f y) = -1)

theorem pow_half (ℓ : ℕ) (h : 1 ≤ ℓ) : (2 : ℝ) ^ ℓ / 2 = 2 ^ (ℓ - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, ℓ = a + 1 := ⟨ℓ - 1, by omega⟩
  rw [show a + 1 - 1 = a by omega, pow_succ]; ring

theorem sem_val (W : G.WF) {zp : Qubits (G.n * G.ℓ₁)} {sb : Bool} {hb : Qubits G.Bh}
    {x : Fin G.n → Qubits G.b} {Z0 : ℕ → Bool} (I : G.Inp zp sb hb x Z0)
    (hr : rho G.n = (2 : ℝ)⁻¹ ^ G.r) (s : ℤ) (hs1 : sb = decide (s = 1))
    (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) :
    (valLE (G.outR.map (evalP (G.n * G.ℓ) (G.Oc w θ) G.prog Z0)) : ℝ) =
      2 ^ G.Vb / 2 + 2 ^ G.Vf *
        (affineBoundaryBisect (addrOf G.n G.ℓ₁ G.f₁ zp) (rho G.n • gridVec G.n G.b x) s G.q
          (fpVal G.Bh G.fh hb - 1 / 4) (fpVal G.Bh G.fh hb + 1 / 4)).run (ltf w θ) ∧
    ∀ v, v < G.base → evalP (G.n * G.ℓ) (G.Oc w θ) G.prog Z0 v = Z0 v := by
  have Wf := W.hf; have Wl := W.hl
  set p := addrOf G.n G.ℓ₁ G.f₁ zp with hp
  set htil := fpVal G.Bh G.fh hb with hhtil
  set x' := rho G.n • gridVec G.n G.b x with hx'
  set H := bitsToNat hb with hH
  set N : Fin G.n → ℕ := fun i => bitsToNat (splitReg G.n G.ℓ₁ zp i) with hN
  have hpi : ∀ i, p i = ((N i : ℝ) - 2 ^ G.ℓ₁ / 2) / 2 ^ G.f₁ := fun i => rfl
  have hhv : htil = ((H : ℝ) - 2 ^ G.Bh / 2) / 2 ^ G.fh := rfl
  have hx'i : ∀ i : Fin G.n, x' i = (2 : ℝ)⁻¹ ^ G.r * gridPoint G.b (x i) := by
    intro i; simp [hx', gridVec, hr]
  have hpb : ∀ i, |p i| ≤ 2 ^ G.ℓ₁ := fun i => abs_fpVal_le _ _ _
  have hhb : |htil| ≤ 2 ^ G.Bh := abs_fpVal_le _ _ _
  set A := G.n * G.ℓ
  set O := G.Oc w θ
  -- initialisation blocks
  obtain ⟨A1, A2, A3⟩ := qblocks_sem A O I
  set ZA := evalP A O (blocks G.qP G.n) Z0 with hZA
  obtain ⟨B1, B2, B3⟩ := tblocks_sem A O W ZA A2
  set ZB := evalP A O (blocks G.tP G.n) ZA with hZB
  obtain ⟨C1, C2, C3⟩ := oblock_sem A O ZB B2
  set ZC := evalP A O G.oP ZB with hZC
  have e1 := G.base_le_tS0; have e2 := G.tS0_le_oSt; have e3 := G.oSt_le_c0
  have hvb := G.vB_le_base
  have hZCA : ∀ v, v < G.tS0 → ZC v = ZA v := fun v hv => by
    rw [C1 v (by omega), B1 v hv]
  have hZC0 : ∀ v, v < G.base → ZC v = Z0 v := fun v hv => by
    rw [hZCA v (by omega), A1 v hv]
  -- track data
  let len : ℕ → ℕ := fun j => if j < G.n then G.ℓ else G.Vb
  let fr : ℕ → ℕ := fun j => if j < G.n then G.f else G.Vf
  let val : ℕ → ℝ → ℝ := fun j mid => if h : j < G.n then x' ⟨j, h⟩ + mid * p ⟨j, h⟩ else mid
  let slope : ℕ → ℝ := fun j => if h : j < G.n then p ⟨j, h⟩ else 1
  let Δ : ℕ → ℕ → ℤ := fun j m => if h : j < G.n then
    2 ^ (G.eD m) * (2 * (N ⟨j, h⟩ : ℤ) - 2 ^ G.ℓ₁) else ((2 ^ (m + G.Vf - G.q - 2) : ℕ) : ℤ)
  have hrange : ∀ j, j < G.n + 1 → ∀ mid, htil - 1 / 4 ≤ mid → mid ≤ htil + 1 / 4 →
      |2 ^ (fr j) * val j mid| < 2 ^ (len j) / 2 := by
    intro j hj mid h1 h2
    have hmid : |mid| ≤ 2 ^ G.Bh + 1 / 4 := by
      rw [abs_le] at hhb ⊢; constructor <;> linarith
    by_cases h : j < G.n
    · simp only [fr, len, val, h, if_true, dif_pos h]
      have hxj : |x' ⟨j, h⟩| ≤ 1 / 2 := by rw [hx'i]; exact abs_rho_grid_le _ _ _
      have hpj := hpb ⟨j, h⟩
      have hB : (1 : ℝ) ≤ 2 ^ G.Bh := one_le_pow₀ (by norm_num)
      have hB' : (1 : ℝ) ≤ 2 ^ G.ℓ₁ := one_le_pow₀ (by norm_num)
      have hsum : |x' ⟨j, h⟩ + mid * p ⟨j, h⟩| < 2 ^ G.Bh * 2 ^ G.ℓ₁ * 4 := by
        calc |x' ⟨j, h⟩ + mid * p ⟨j, h⟩| ≤ |x' ⟨j, h⟩| + |mid| * |p ⟨j, h⟩| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ 1 / 2 + (2 ^ G.Bh + 1 / 4) * 2 ^ G.ℓ₁ := by gcongr
          _ < 2 ^ G.Bh * 2 ^ G.ℓ₁ * 4 := by nlinarith only [hB, hB']
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ G.f)]
      have e : (2 : ℝ) ^ G.ℓ / 2 ≥ 2 ^ G.f * (2 ^ G.Bh * 2 ^ G.ℓ₁ * 4) := by
        have : (2 : ℝ) ^ G.ℓ = 2 ^ (G.f + G.Bh + G.ℓ₁ + 3) * 2 ^ (G.ℓ - (G.f + G.Bh + G.ℓ₁ + 3)) := by
          rw [← pow_add]; congr 1; omega
        rw [this]
        have h1 : (1 : ℝ) ≤ 2 ^ (G.ℓ - (G.f + G.Bh + G.ℓ₁ + 3)) := one_le_pow₀ (by norm_num)
        have h2 : (2 : ℝ) ^ (G.f + G.Bh + G.ℓ₁ + 3) / 2 = 2 ^ G.f * (2 ^ G.Bh * 2 ^ G.ℓ₁ * 4) := by
          simp only [pow_add, pow_succ]; ring
        have h3 : (0 : ℝ) < 2 ^ (G.f + G.Bh + G.ℓ₁ + 3) := by positivity
        nlinarith only [h1, h2, h3]
      calc 2 ^ G.f * |x' ⟨j, h⟩ + mid * p ⟨j, h⟩| < 2 ^ G.f * (2 ^ G.Bh * 2 ^ G.ℓ₁ * 4) :=
            mul_lt_mul_of_pos_left hsum (by positivity)
        _ ≤ 2 ^ G.ℓ / 2 := e
    · simp only [fr, len, val, h, if_false, dif_neg h, not_false_eq_true]
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ G.Vf)]
      have hB : (1 : ℝ) ≤ 2 ^ G.Bh := one_le_pow₀ (by norm_num)
      have e : (2 : ℝ) ^ G.Vb / 2 = 2 ^ G.Vf * (2 ^ G.Bh * 2) := by
        simp only [Vb, pow_add, pow_succ]; ring
      rw [e]
      exact mul_lt_mul_of_pos_left (by linarith) (by positivity)
  -- initial coordinate tracks
  have hT : ∀ j : Fin G.n, (valLE ((G.tOut j).map ZC) : ℝ) =
      2 ^ G.ℓ / 2 + 2 ^ G.f * (x' j + htil * p j) := by
    intro j
    have hmap : (G.tOut j).map ZC = (G.tOut j).map ZB :=
      List.map_congr_left (fun a ha => C1 a (G.tOut_lt j j.isLt a ha).2)
    rw [hmap, B3 j]
    have hX : valLE ((G.xReg j).map ZA) = bitsToNat (x j) := by
      rw [← I.valX j]; congr 1; apply List.map_congr_left; intro a ha
      exact A1 a (by have := G.xReg_mem j j.isLt a ha; omega)
    rw [hX]
    have hQ := A3 j
    set Qn := valLE ((G.qOut j).map ZA)
    set Wt : ℤ := G.Kt + 2 ^ (G.f - G.r - G.b) * (bitsToNat (x j) : ℤ) + 2 ^ G.eQ * qVal zp hb j
      with hWt
    have hWr : (Wt : ℝ) = 2 ^ G.ℓ / 2 + 2 ^ G.f * (x' j + htil * p j) := by
      rw [mul_add, hx'i, grid_track _ _ _ (by omega), hhv, hpi j,
        prod_track G.f G.fh G.f₁ G.eQ G.Bh G.ℓ₁ (by simp only [eQ]; omega),
        pow_half _ (by omega)]
      simp only [hWt, Kt, qVal]
      push_cast
      ring
    have hrng := hrange j (by omega) htil (by linarith) (by linarith)
    simp only [fr, len, val, j.isLt, if_true, dif_pos j.isLt, Fin.eta] at hrng
    have hl2 : (2 : ℝ) ^ G.ℓ / 2 + 2 ^ G.ℓ / 2 = 2 ^ G.ℓ := by ring
    have h0 : 0 ≤ Wt := by
      have : (0 : ℝ) ≤ Wt := by rw [hWr]; have := (abs_lt.mp hrng).1; linarith
      exact_mod_cast this
    have h1 : Wt < 2 ^ G.ℓ := by
      have : (Wt : ℝ) < ((2 ^ G.ℓ : ℤ) : ℝ) := by
        push_cast; rw [hWr]; have := (abs_lt.mp hrng).2; linarith
      exact_mod_cast this
    have hmod : ((Kc G.Kt G.ℓ + (2 ^ (G.f - G.r - G.b) * bitsToNat (x j) + 2 ^ G.eQ * Qn) : ℕ) : ℤ)
        ≡ Wt [ZMOD 2 ^ G.ℓ] := by
      have hk := Kc_modEq G.Kt G.ℓ
      push_cast; rw [hQ, hWt]
      have := Int.ModEq.add_right ((2 : ℤ) ^ (G.f - G.r - G.b) * (bitsToNat (x j) : ℤ) +
        2 ^ G.eQ * qVal zp hb j) hk
      rw [add_assoc]; exact this
    have key := mod_eq_of_modEq _ _ _ hmod h0 h1
    rw [← hWr, ← key]; push_cast; rfl
  -- initial output track
  have hO : (valLE (G.oOut.map ZC) : ℝ) = 2 ^ G.Vb / 2 + 2 ^ G.Vf * htil := by
    rw [C3]
    have hHv : valLE (G.hReg.map ZB) = H := by
      rw [hH, ← I.valH]; congr 1; apply List.map_congr_left; intro a ha
      have := G.hReg_mem a ha; have := G.xB_le_vB
      rw [B1 a (by omega), A1 a (by omega)]
    rw [hHv]
    set Wo : ℤ := G.Ko + 2 ^ (G.Vf - G.fh) * (H : ℤ) with hWo
    have hWr : (Wo : ℝ) = 2 ^ G.Vb / 2 + 2 ^ G.Vf * htil := by
      rw [hhv, out_track _ _ _ (by simp only [Vf]; omega), pow_half _ (by simp only [Vb]; omega)]
      simp only [hWo, Ko]; push_cast; ring
    have hrng := hrange G.n (by omega) htil (by linarith) (by linarith)
    simp only [fr, len, val, lt_irrefl, if_false, dif_neg (lt_irrefl _)] at hrng
    have hl2 : (2 : ℝ) ^ G.Vb / 2 + 2 ^ G.Vb / 2 = 2 ^ G.Vb := by ring
    have h0 : 0 ≤ Wo := by
      have : (0 : ℝ) ≤ Wo := by rw [hWr]; have := (abs_lt.mp hrng).1; linarith
      exact_mod_cast this
    have h1 : Wo < 2 ^ G.Vb := by
      have : (Wo : ℝ) < ((2 ^ G.Vb : ℤ) : ℝ) := by
        push_cast; rw [hWr]; have := (abs_lt.mp hrng).2; linarith
      exact_mod_cast this
    have hmod : ((Kc G.Ko G.Vb + 2 ^ (G.Vf - G.fh) * H : ℕ) : ℤ) ≡ Wo [ZMOD 2 ^ G.Vb] := by
      have hk := Kc_modEq G.Ko G.Vb
      push_cast; rw [hWo]
      exact Int.ModEq.add_right _ hk
    have key := mod_eq_of_modEq _ _ _ hmod h0 h1
    rw [← hWr, ← key]; push_cast; rfl
  -- the rounds
  have hL : (1 / 2 : ℝ) = 2 ^ G.q / 2 ^ (G.q + 1) := by rw [pow_succ]; field_simp
  have hlomid : htil - 1 / 4 + 1 / 2 / 2 = htil := by ring
  obtain ⟨R1, _, R3⟩ := rP_sem G.n G.ℓ G.sW G.δ G.f G.q s p x' (ltf w θ) (ltf_pm w θ) sb hs1
    htil len fr val slope
    (fun j hj => by simp [len, hj]) (fun j hj => by simp [fr, hj])
    (fun j hj mid => by simp [val, hj])
    (fun j hj mid δ' => by
      by_cases h : j < G.n
      · simp only [val, slope, dif_pos h]; ring
      · simp only [val, slope, dif_neg h]; ring)
    Δ
    (fun j hj m hm => by
      by_cases h : j < G.n
      · simp only [Δ, fr, slope, dif_pos h, if_pos h]
        rw [hpi]
        exact delta_coord G.f G.f₁ G.q m (by omega) (N ⟨j, h⟩) G.ℓ₁
      · simp only [Δ, fr, slope, dif_neg h, if_neg h]
        exact delta_out G.Vf G.q m (by simp only [Vf]; omega))
    G.vB Z0
    (fun j hj m hm => by
      by_cases h : j < G.n
      · have e : G.δ j m = sgnSpecs (G.pReg j) (G.eD m) G.ℓ := by simp [δ, h, hm]
        rw [e]
        have := sgnSpecs_val Z0 (G.pReg j) (G.eD m) G.ℓ
          (by rw [pReg_length]; simp only [eD]; omega)
        rw [pReg_length, I.valP ⟨j, h⟩] at this
        simpa [len, h, Δ] using this
      · have e : G.δ j m = constSpecs (2 ^ (m + G.Vf - G.q - 2)) G.Vb := by simp [δ, h]
        rw [e, constSpecs_val]
        simp only [len, h, if_false, Δ, dif_neg h]
        rw [Int.natCast_mod]; push_cast
        exact Int.mod_modEq _ _)
    (fun j m sp hsp a ha => G.δ_src j m sp hsp a ha)
    (fun j hj m => by
      have := G.δ_length W j m (by rw [Ts0_length]; exact hj)
      rw [this]
      by_cases h : j < G.n
      · rw [Ts0_getD_lt _ _ h, tOut_length]; simp [len, h]
      · have : j = G.n := by omega
        subst this; rw [Ts0_getD_n, oOut_length]; simp [len])
    (by have := G.sW_lt_hB; have := G.hB_le_xB; have := G.xB_le_vB; omega) I.hs hrange
    G.q le_rfl (htil - 1 / 4) (1 / 2) G.Ts0 G.c0 ZC hL (by linarith) (by linarith) G.Ts0_length
    (by
      intro j hj
      rw [hlomid]
      by_cases h : j < G.n
      · rw [G.Ts0_getD_lt j h]
        refine ⟨by simp [len, h, tOut_length], ?_⟩
        have := hT ⟨j, h⟩
        simp only [len, fr, val, h, if_true, dif_pos h]
        exact this
      · have hjn : j = G.n := by omega
        subst hjn
        rw [G.Ts0_getD_n]
        refine ⟨by simp [len, oOut_length], ?_⟩
        simp only [len, fr, val, lt_irrefl, if_false, dif_neg (lt_irrefl _)]
        exact hO)
    (fun R h a ha => (G.Ts0_wires R h a ha).2) C2 (by omega)
    (fun v hv => hZC0 v (by omega))
  have hprog : evalP A O G.prog Z0 = evalP A O (rP G.n G.ℓ G.sW G.δ G.q G.Ts0 G.c0) ZC := by
    simp only [prog, initP, evalP_append]; rfl
  have hhi : htil - 1 / 4 + 1 / 2 = htil + 1 / 4 := by ring
  constructor
  · have := R3 G.n (by omega)
    rw [hhi] at this
    simp only [len, fr, val, lt_irrefl, if_false, dif_neg (lt_irrefl _)] at this
    rw [outR, hprog]
    exact this
  · intro v hv
    rw [hprog]; exact (R1 v (by omega)).trans (hZC0 v hv)

end Prm

end

end QuantumLTF.Membership.A2

-- ===== module U13 =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

theorem ofQ_append {m k : ℕ} (a : Qubits m) (b : Qubits k) (w : ℕ) :
    ofQ (Fin.append a b) w = if w < m then ofQ a w else ofQ b (w - m) := by
  unfold ofQ
  by_cases h1 : w < m
  · rw [if_pos h1, dif_pos (by omega), dif_pos h1]
    have : (⟨w, by omega⟩ : Fin (m + k)) = Fin.castAdd k ⟨w, h1⟩ := rfl
    rw [this, Fin.append_left]
  · rw [if_neg h1]
    by_cases h2 : w < m + k
    · rw [dif_pos h2, dif_pos (by omega)]
      have : (⟨w, h2⟩ : Fin (m + k)) = Fin.natAdd m ⟨w - m, by omega⟩ := Fin.ext (by simp; omega)
      rw [this, Fin.append_right]
    · rw [dif_neg h2, dif_neg (by omega)]

theorem ofQ_lt {m : ℕ} (a : Qubits m) (w : ℕ) (h : w < m) : ofQ a w = a ⟨w, h⟩ := by
  simp [ofQ, h]

theorem ofQ_false (m w : ℕ) : ofQ (fun _ : Fin m => false) w = false := by
  unfold ofQ; split_ifs <;> rfl

theorem toQ_congr (N : ℕ) (Z Z' : ℕ → Bool) (h : ∀ w, w < N → Z w = Z' w) : toQ N Z = toQ N Z' := by
  funext ⟨w, hw⟩; exact h w hw

theorem evalP_tgt_frame (A : ℕ) (O : Qubits A → Bool) (V : ℕ → Prop) (P : List Ins)
    (hP : ∀ I ∈ P, ¬ V (I.tgt A)) (Z : ℕ → Bool) : ∀ w, V w → evalP A O P Z w = Z w := by
  induction P generalizing Z with
  | nil => intro w _; rfl
  | cons I P ih =>
    intro w hw
    rw [evalP_cons, ih (fun J hJ => hP J (by simp [hJ])) _ w hw]
    have : w ≠ I.tgt A := by rintro rfl; exact hP I (by simp) hw
    simp [Ins.eval, Function.update_of_ne this]

namespace Prm
variable (G : Prm)

abbrev NN : ℕ := G.n * G.ℓ₁ + 1 + G.Bh + (G.n * G.b + G.Vb + G.W)

def fullB (zp : Qubits (G.n * G.ℓ₁)) (sb : Bool) (hb : Qubits G.Bh)
    (y : Qubits (G.n * G.b + G.Vb + G.W)) : Qubits G.NN :=
  Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb) y

theorem ofQ_fullB (zp : Qubits (G.n * G.ℓ₁)) (sb : Bool) (hb : Qubits G.Bh)
    (x : Fin G.n → Qubits G.b) (v : Qubits G.Vb) (w : ℕ) :
    ofQ (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x v)) w =
      if w < G.n * G.ℓ₁ + 1 + G.Bh then ofQ (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb) w
      else if w < G.vB then ofQ (flatReg G.n G.b x) (w - G.xB)
      else if w < G.base then ofQ v (w - G.vB) else false := by
  have e1 : G.xB = G.n * G.ℓ₁ + 1 + G.Bh := rfl
  have e2 : G.vB = G.xB + G.n * G.b := rfl
  have e3 : G.base = G.vB + G.Vb := rfl
  by_cases h1 : w < G.n * G.ℓ₁ + 1 + G.Bh
  · rw [fullB, ofQ_append, if_pos h1, if_pos h1]
  · rw [fullB, ofQ_append, if_neg h1, if_neg h1]
    simp only [regBasis, ofQ_append, ofQ_false]
    by_cases h2 : w < G.vB
    · rw [if_pos (by omega), if_pos (by omega), if_pos h2, e1]
    · rw [if_neg h2]
      by_cases h3 : w < G.base
      · rw [if_pos (by omega), if_neg (by omega), if_pos h3]
        congr 1; omega
      · rw [if_neg (by omega), if_neg h3]

theorem inp_of (W : G.WF) (zp : Qubits (G.n * G.ℓ₁)) (sb : Bool) (hb : Qubits G.Bh)
    (x : Fin G.n → Qubits G.b) :
    G.Inp zp sb hb x (ofQ (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x fun _ => false))) := by
  have hl : G.n * G.ℓ₁ + 1 + G.Bh = G.xB := rfl
  refine ⟨fun i j => ?_, ?_, fun j => ?_, fun i j => ?_, fun w hw => ?_⟩
  · have hlt : G.ℓ₁ * i + j < G.n * G.ℓ₁ := by
      have := i.isLt; have := j.isLt
      have : G.ℓ₁ * (i + 1) ≤ G.ℓ₁ * G.n := Nat.mul_le_mul_left _ i.isLt
      rw [Nat.mul_comm G.n]; nlinarith
    rw [ofQ_fullB, if_pos (by omega), ofQ_append, if_pos (by omega), ofQ_append, if_pos hlt,
      ofQ_lt _ _ hlt]
    simp only [splitReg]; congr 1; ext; simp [finProdFinEquiv_apply_val]; ring
  · rw [ofQ_fullB, if_pos (by simp only [sW]; omega), ofQ_append, if_pos (by simp [sW]),
      ofQ_append, if_neg (by simp [sW])]
    simp [ofQ, sW]
  · rw [ofQ_fullB, if_pos (by simp only [hB]; omega), ofQ_append, if_neg (by simp only [hB]; omega),
      ofQ_lt _ _ (by simp [hB])]
    congr 1; ext; simp [hB]
  · have hlt : G.b * i + j < G.n * G.b := by
      have := j.isLt
      have : G.b * (i + 1) ≤ G.b * G.n := Nat.mul_le_mul_left _ i.isLt
      rw [Nat.mul_comm G.n]; nlinarith
    rw [ofQ_fullB, if_neg (by rw [hl]; omega), if_pos (by simp only [vB]; omega),
      show G.xB + G.b * i + j - G.xB = G.b * i + j by omega, ofQ_lt _ _ hlt]
    simp only [flatReg]
    have e : (⟨G.b * i + j, hlt⟩ : Fin (G.n * G.b)) = finProdFinEquiv (i, j) := by
      ext; simp [finProdFinEquiv_apply_val]; ring
    rw [e, Equiv.symm_apply_apply]
  · rw [ofQ_fullB, if_neg (by simp only [base, vB] at hw; omega),
      if_neg (by simp only [base] at hw; omega), if_neg (by omega)]

theorem NN_eq : G.NN = G.cEnd := by
  have h1 := G.c0_le_cEnd; have h2 := G.base_le_tS0; have h3 := G.tS0_le_oSt
  have h4 := G.oSt_le_c0
  have hb : G.base = G.n * G.ℓ₁ + 1 + G.Bh + G.n * G.b + G.Vb := rfl
  show G.n * G.ℓ₁ + 1 + G.Bh + (G.n * G.b + G.Vb + (G.cEnd - G.base)) = G.cEnd
  omega

def Htil (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) (Z0 : ℕ → Bool) : Qubits G.Vb :=
  fun m => evalP (G.n * G.ℓ) (G.Oc w θ) G.prog Z0 (G.outR.reverse.getD m 0)

theorem good_WF {A : ℕ} {S : ℕ → Prop} {lo hi : ℕ} {I : Ins} (h : Good A S lo hi I) (N : ℕ)
    (hN : hi ≤ N) : I.WF N A :=
  ⟨by have := h.2.1; omega, fun s hs => by have := (h.2.2 s hs).1; have := h.2.1; omega⟩

theorem Pfull_wf (W : G.WF) : ∀ I ∈ G.Pfull, I.WF G.NN (G.n * G.ℓ) := by
  have hgood := G.prog_good W
  have hN := G.NN_eq
  have hb := G.vB_le_base
  intro I hI
  simp only [Pfull, List.mem_append, List.mem_reverse] at hI
  rcases hI with (hI | hI) | hI
  · exact good_WF (hgood I hI) _ (by omega)
  · simp only [copyOut, List.mem_map, List.mem_range] at hI
    obtain ⟨m, hm, rfl⟩ := hI
    have hm' : m < G.outR.reverse.length := by simp [outR_length, hm]
    have hmem : G.outR.reverse.getD m 0 ∈ G.outR := by
      rw [List.getD_eq_getElem _ _ hm']; exact List.mem_reverse.mp (List.getElem_mem _)
    have := G.outR_wires _ hmem
    have h1 : G.vB + m < G.base := by simp only [base]; omega
    refine ⟨by simp only [Ins.tgt]; omega, fun s hs => ?_⟩
    simp only [Ins.src, Ins.tgt] at hs ⊢
    subst hs
    constructor
    · omega
    · simp only [base] at *; omega
  · exact good_WF (hgood I hI) _ (by omega)

theorem Pfull_tgt (W : G.WF) : ∀ I ∈ G.Pfull, G.vB ≤ I.tgt (G.n * G.ℓ) := by
  have hgood := G.prog_good W
  have hb := G.vB_le_base
  intro I hI
  simp only [Pfull, List.mem_append, List.mem_reverse] at hI
  rcases hI with (hI | hI) | hI
  · have := (hgood I hI).1; omega
  · simp only [copyOut, List.mem_map, List.mem_range] at hI
    obtain ⟨m, hm, rfl⟩ := hI
    simp [Ins.tgt]
  · have := (hgood I hI).1; omega

theorem sem_circuit (W : G.WF) (zp : Qubits (G.n * G.ℓ₁)) (sb : Bool) (hb : Qubits G.Bh)
    (x : Fin G.n → Qubits G.b) (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) :
    act ((toCP G.NN (G.n * G.ℓ) G.Pfull).unitary (fun _ => memOracle G.n G.ℓ G.f w θ))
      (ket (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x fun _ => false))) =
    ket (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x
      (G.Htil w θ (ofQ (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x fun _ => false)))))) := by
  set Z0 := ofQ (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x fun _ => false)) with hZ0
  have I := G.inp_of W zp sb hb x
  set O := G.Oc w θ
  have hgood := G.prog_good W
  have hbv := G.vB_le_base
  rw [← toQ_ofQ (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x fun _ => false)),
    act_toCP G.NN (G.n * G.ℓ) O _ (memOracle_eq G.n G.ℓ G.f w θ) G.Pfull (G.Pfull_wf W)]
  congr 1
  rw [← toQ_ofQ (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x (G.Htil w θ Z0)))]
  apply toQ_congr
  intro v hv
  -- classical reasoning
  have hpres : ∀ u, u < G.base → evalP (G.n * G.ℓ) O G.prog Z0 u = Z0 u := by
    intro u hu
    exact evalP_tgt_frame (G.n * G.ℓ) O (· < G.base) G.prog
      (fun I hI h => absurd h (not_lt.mpr (hgood I hI).1)) Z0 u hu
  have hval0 : ∀ m, m < G.Vb → Z0 (G.vB + m) = false := by
    intro m hm
    rw [hZ0, ofQ_fullB, if_neg (by simp only [vB, xB, hB]; omega), if_neg (by omega),
      if_pos (by simp only [base]; omega), ofQ_false]
  set Z1 := evalP (G.n * G.ℓ) O G.prog Z0 with hZ1
  set Z2 := evalP (G.n * G.ℓ) O (copyOut G.outR G.vB G.Vb) Z1 with hZ2
  have hcopy := copyOut_sem (G.n * G.ℓ) O G.outR G.vB G.base (fun a ha => (G.outR_wires a ha).1) Z1 G.Vb
    (by rw [outR_length]) (by simp [base]) (fun m hm => by
      rw [hpres _ (by simp only [base]; omega)]; exact hval0 m hm)
  let V : ℕ → Prop := fun u => G.vB ≤ u ∧ u < G.base
  have hP : ∀ I ∈ G.prog.reverse, ¬ V (I.tgt (G.n * G.ℓ)) ∧ ∀ s, I.src (G.n * G.ℓ) s → ¬ V s := by
    intro I hI
    have hg := hgood I (List.mem_reverse.mp hI)
    refine ⟨fun h => by have := hg.1; simp only [V] at h; omega, fun s hs h => ?_⟩
    have := (hg.2.2 s hs).2
    simp only [V, S] at h this; omega
  obtain ⟨Fr1, Fr2⟩ := evalP_frame (G.n * G.ℓ) O V G.prog.reverse hP Z2 Z1 (fun u hu => by
    rw [hZ2, hcopy u, if_neg]
    have : G.base = G.vB + G.Vb := rfl
    simp only [V] at hu ⊢; omega)
  have hrev := evalP_reverse (G.n * G.ℓ) O G.prog (fun I hI h => by
    have := ((hgood I hI).2.2 _ h).1; omega) Z0
  have hfull : evalP (G.n * G.ℓ) O G.Pfull Z0 = evalP (G.n * G.ℓ) O G.prog.reverse Z2 := by
    simp only [Pfull, evalP_append]; rfl
  rw [hfull]
  by_cases hV : V v
  · simp only [V] at hV
    rw [Fr2 v hV, hZ2, hcopy v, if_pos (by simp only [base] at hV; omega), ofQ_fullB,
      if_neg (by simp only [vB, xB, hB] at hV; omega), if_neg (by omega), if_pos hV.2,
      ofQ_lt _ _ (by simp only [base] at hV; omega)]
    rfl
  · rw [Fr1 v hV, hrev, hZ0, ofQ_fullB, ofQ_fullB]
    simp only [V] at hV
    split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)

theorem blockdiag (W : G.WF) (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) (y y' : Qubits G.NN)
    (h : (toCP G.NN (G.n * G.ℓ) G.Pfull).unitary (fun _ => memOracle G.n G.ℓ G.f w θ) y' y ≠ 0) :
    ∀ i : Fin (G.n * G.ℓ₁ + 1 + G.Bh),
      y' (Fin.castAdd (G.n * G.b + G.Vb + G.W) i) = y (Fin.castAdd (G.n * G.b + G.Vb + G.W) i) := by
  have e := unitary_entry_ne_zero G.NN (G.n * G.ℓ) (G.Oc w θ) _ (memOracle_eq G.n G.ℓ G.f w θ)
    G.Pfull (G.Pfull_wf W) y y' h
  intro i
  rw [e]
  have hi : (i : ℕ) < G.xB := i.isLt
  have hxv := G.xB_le_vB
  have := evalP_tgt_frame (G.n * G.ℓ) (G.Oc w θ) (· < G.xB) G.Pfull
    (fun I hI h => absurd h (not_lt.mpr (le_trans hxv (G.Pfull_tgt W I hI)))) (ofQ y) i hi
  simp only [toQ, Fin.coe_castAdd]
  rw [this]
  exact ofQ_lt _ _ (Fin.castAdd (G.n * G.b + G.Vb + G.W) i).isLt

theorem sem_fp (W : G.WF) (zp : Qubits (G.n * G.ℓ₁)) (sb : Bool) (hb : Qubits G.Bh)
    (x : Fin G.n → Qubits G.b) (hr : rho G.n = (2 : ℝ)⁻¹ ^ G.r) (s : ℤ) (hs1 : sb = decide (s = 1))
    (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) :
    fpVal G.Vb G.Vf
      (G.Htil w θ (ofQ (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x fun _ => false)))) =
      (affineBoundaryBisect (addrOf G.n G.ℓ₁ G.f₁ zp) (rho G.n • gridVec G.n G.b x) s G.q
        (fpVal G.Bh G.fh hb - 1 / 4) (fpVal G.Bh G.fh hb + 1 / 4)).run (ltf w θ) := by
  set Z0 := ofQ (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x fun _ => false))
  obtain ⟨hv, _⟩ := G.sem_val W (G.inp_of W zp sb hb x) hr s hs1 w θ
  set Z1 := evalP (G.n * G.ℓ) (G.Oc w θ) G.prog Z0
  have hb' : bitsToNat (G.Htil w θ Z0) = valLE (G.outR.map Z1) := by
    apply bitsToNat_eq_valLE
    · simp [outR_length]
    · intro i
      have h1 : (i : ℕ) < G.outR.reverse.length := by simp [outR_length]
      have h2 : (i : ℕ) < (G.outR.map Z1).reverse.length := by simp [outR_length]
      rw [List.getD_eq_getElem _ _ h2]
      simp only [Htil]
      rw [List.getD_eq_getElem _ _ h1]
      simp [Z1]
  simp only [fpVal, hb', hv]
  field_simp
  ring

theorem gate_bound (W : G.WF) (hn : 1 ≤ G.n) :
    (toCP G.NN (G.n * G.ℓ) G.Pfull).gateCount ≤
      18 * G.n * (G.Bh + 2) * G.Kw + 54 * G.n * G.ℓ * (G.q + 1) :=
  le_trans (gateCount_toCP _ _ _) (G.Pfull_length W hn)

theorem query_bound : (toCP G.NN (G.n * G.ℓ) G.Pfull).queryCount 0 ≤ 2 * G.q := by
  have := queryCount_toCP G.NN (G.n * G.ℓ) G.Pfull
  rw [G.Pfull_countQ] at this; exact this

end Prm

end

end QuantumLTF.Membership.A2


-- ===== module Uniform =====

namespace QuantumLTF.Membership.A2
open QAlgorithms

noncomputable section

theorem rceil_bound (n : ℕ) (hn : 1 ≤ n) :
    (⌈Real.logb 2 (40 * Real.sqrt n)⌉₊ : ℝ) ≤ 9 + Real.log n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn'
  have h40 : 1 ≤ 40 * Real.sqrt n := by linarith
  have hy0 : 0 ≤ Real.logb 2 (40 * Real.sqrt n) :=
    Real.logb_nonneg (by norm_num) h40
  have hceil := Nat.ceil_lt_add_one hy0
  have hlog40 : Real.log 40 < 4 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h27 : (2.7 : ℝ) < Real.exp 1 := by linarith
    have := pow_lt_pow_left₀ h27 (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    norm_num at this
    linarith
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn'
  have heq : Real.log (40 * Real.sqrt n) = Real.log 40 + Real.log n / 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity)]
  have hy : Real.logb 2 (40 * Real.sqrt n) ≤ 8 + Real.log n := by
    rw [Real.logb, heq, div_le_iff₀ (by linarith)]
    have : 0 ≤ Real.log 40 := Real.log_nonneg (by norm_num)
    nlinarith
  linarith


theorem gate_real (N ℓ Bh l1 q X L K0 : ℝ) (hK : 3 ≤ K0) (hL : 1 ≤ L) (hX : 1 ≤ X)
    (hKX : Bh + l1 + 3 ≤ K0 * X) (hq : q + 1 ≤ K0 * L) (hN : 0 ≤ N) (hℓ : 0 ≤ ℓ) (hB : 0 ≤ Bh)
    (hl : 0 ≤ l1) :
    18 * N * (Bh + 2) * (Bh + l1 + 3) + 54 * N * ℓ * (q + 1) ≤
      100 * K0 ^ 2 * N * X ^ 2 * L + 100 * K0 ^ 2 * N * ℓ * L := by
  have hsq : (Bh + 2) * (Bh + l1 + 3) ≤ (K0 * X) ^ 2 := by
    have : (Bh + 2) * (Bh + l1 + 3) ≤ (Bh + l1 + 3) ^ 2 := by nlinarith
    have h0 : 0 ≤ Bh + l1 + 3 := by positivity
    nlinarith
  have e1 : 18 * N * (Bh + 2) * (Bh + l1 + 3) ≤ 100 * K0 ^ 2 * N * X ^ 2 * L := by
    have h1 : 18 * N * ((Bh + 2) * (Bh + l1 + 3)) ≤ 18 * N * (K0 * X) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h2 : 18 * N * (K0 * X) ^ 2 ≤ 100 * K0 ^ 2 * N * X ^ 2 * L := by
      have : 0 ≤ N * K0 ^ 2 * X ^ 2 := by positivity
      nlinarith
    nlinarith
  have e2 : 54 * N * ℓ * (q + 1) ≤ 100 * K0 ^ 2 * N * ℓ * L := by
    have h0 : 0 ≤ N * ℓ := by positivity
    have h1 : 54 * (N * ℓ) * (q + 1) ≤ 54 * (N * ℓ) * (K0 * L) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    have h2 : (54 * K0) * (N * ℓ * L) ≤ (100 * K0 ^ 2) * (N * ℓ * L) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    nlinarith
  linarith

/-- **Uniform Theorem 3.2 circuit.** One reversible circuit, fixed before `w, θ` and before the
values of `p, s, h̃` (read from registers), for every sufficiently fine oracle format `(ℓ, f)`. -/
theorem uniform_height_circuit (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε η : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < η → η < 1 / 8 →
      ∀ (b ℓ₁ f₁ Bh fh : ℕ), (ℓ₁ : ℝ) ≤ C₁ * Real.log n → f₁ ≤ ℓ₁ →
        (Bh : ℝ) ≤ C₂ * Real.log (1 / ε) → fh ≤ Bh →
      ∃ (Vb Vf F D : ℕ),
        (Vb : ℝ) ≤ C * (Real.log (1 / ε) + Real.log (1 / η)) ∧
        (F : ℝ) ≤ C * (Real.log n + Real.log (1 / ε) + Real.log (1 / η) + b) ∧
        (D : ℝ) ≤ C * (Real.log n + Real.log (1 / ε) + Real.log (1 / η) + b) ∧
        ∀ ℓ f : ℕ, F ≤ f → f + D ≤ ℓ →
        ∃ (W : ℕ) (c : OracleCircuit gatesRev (fun _ : Fin 1 => n * ℓ + 1)
            (n * ℓ₁ + 1 + Bh + (n * b + Vb + W))),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C * Real.log (1 / η) ∧
          (c.gateCount : ℝ) ≤ C * n * (b + Real.log n + Real.log (1 / ε) + Real.log (1 / η)) ^ 2 *
              Real.log (1 / η) + C * n * ℓ * Real.log (1 / η) ∧
          (∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
              (y y' : Qubits (n * ℓ₁ + 1 + Bh + (n * b + Vb + W))),
            (c.unitary fun _ => memOracle n ℓ f w θ) y' y ≠ 0 →
            ∀ i : Fin (n * ℓ₁ + 1 + Bh),
              y' (Fin.castAdd (n * b + Vb + W) i) = y (Fin.castAdd (n * b + Vb + W) i)) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (zp : Qubits (n * ℓ₁)) (sb : Bool)
            (hb : Qubits Bh), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w (addrOf n ℓ₁ f₁ zp)| → |inner ℝ w (addrOf n ℓ₁ f₁ zp)| ≤ 3 →
            (if sb then (1 : ℤ) else -1) = sgn (inner ℝ w (addrOf n ℓ₁ f₁ zp)) →
            |fpVal Bh fh hb - height w θ (addrOf n ℓ₁ f₁ zp) 0| ≤ ε / 100 →
            ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, act (c.unitary fun _ => memOracle n ℓ f w θ)
                  (ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                    (regBasis n b Vb W x fun _ => false))) =
                ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                    (regBasis n b Vb W x (Htil x)))) ∧
              ∀ x, |fpVal Vb Vf (Htil x) -
                height w θ (addrOf n ℓ₁ f₁ zp) (rho n • gridVec n b x)| ≤ η := by
  obtain ⟨Cu, hCu, hparam⟩ := QuantumLTF.Membership.local_bisection_parameters
  set K0 : ℝ := C₁ + C₂ + Cu + 3 with hK0
  have hK3 : 3 ≤ K0 := by rw [hK0]; linarith
  refine ⟨100 * K0 ^ 2, by positivity, ?_⟩
  intro n hn ε η hε hε2 hη hη8 b ℓ₁ f₁ Bh fh hℓ₁ hf₁ hBh hfh
  obtain ⟨q, hq, hqerr⟩ := hparam η hη hη8
  set r := ⌈Real.logb 2 (40 * Real.sqrt n)⌉₊ with hr
  have hrb : (r : ℝ) ≤ 9 + Real.log n := rceil_bound n (by omega)
  -- real facts
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogn : 0 ≤ Real.log n := le_trans (by linarith) (Real.log_le_log (by norm_num) hn1)
  have hLe : 0 ≤ Real.log (1 / ε) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hε]; linarith
  have hL : 1 ≤ Real.log (1 / η) := by
    have h8 : (8 : ℝ) < 1 / η := (lt_div_iff₀ hη).2 (by linarith only [hη8])
    have hlog : Real.log 8 < Real.log (1 / η) :=
      Real.strictMonoOn_log (by norm_num : (8 : ℝ) ∈ Set.Ioi 0)
        (lt_trans (by norm_num) h8) h8
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at hlog
    push_cast at hlog
    linarith
  set Le := Real.log (1 / ε)
  set L := Real.log (1 / η)
  set ln := Real.log n
  clear_value Le L ln K0
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hCu0 : 0 ≤ Cu := le_of_lt hCu
  have hfhB : (fh : ℝ) ≤ Bh := by exact_mod_cast hfh
  have hf₁ℓ : (f₁ : ℝ) ≤ ℓ₁ := by exact_mod_cast hf₁
  have hC0 : (0 : ℝ) ≤ 100 * K0 ^ 2 := by positivity
  have hKC : 20 * K0 ≤ 100 * K0 ^ 2 := by nlinarith only [hK3]
  have hB1 : (Bh : ℝ) ≤ K0 * Le :=
    le_trans hBh (mul_le_mul_of_nonneg_right (by linarith) hLe)
  have hq1 : (q : ℝ) ≤ K0 * L :=
    le_trans hq (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have hl1 : (ℓ₁ : ℝ) ≤ K0 * ln :=
    le_trans hℓ₁ (mul_le_mul_of_nonneg_right (by linarith) hlogn)
  have hKL : 0 ≤ K0 * L := by positivity
  have hKe : 0 ≤ K0 * Le := by positivity
  have hKn : 0 ≤ K0 * ln := by positivity
  have hKb : 0 ≤ K0 * b := by positivity
  refine ⟨fh + q + 2 + Bh + 2, fh + q + 2, r + b + fh + f₁ + q + 3, Bh + ℓ₁ + 3, ?_, ?_, ?_, ?_⟩
  · push_cast
    have h1 : (fh : ℝ) + q + 2 + Bh + 2 ≤ (2 * K0 + 4) * (Le + L) := by
      have : (2 * K0 + 4) * (Le + L) = 2 * (K0 * Le) + 2 * (K0 * L) + 4 * Le + 4 * L := by ring
      rw [this]; linarith
    have h2 : (2 * K0 + 4) * (Le + L) ≤ 100 * K0 ^ 2 * (Le + L) :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hK3]) (by linarith)
    linarith
  · push_cast
    have h1 : (r : ℝ) + b + fh + f₁ + q + 3 ≤ (K0 + 13) * (ln + Le + L + b) := by
      have : (K0 + 13) * (ln + Le + L + b) =
          K0 * ln + K0 * Le + K0 * L + K0 * b + 13 * ln + 13 * Le + 13 * L + 13 * b := by ring
      rw [this]; linarith
    have h2 : (K0 + 13) * (ln + Le + L + b) ≤ 100 * K0 ^ 2 * (ln + Le + L + b) :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hK3]) (by linarith)
    linarith
  · push_cast
    have h1 : (Bh : ℝ) + ℓ₁ + 3 ≤ (K0 + 3) * (ln + Le + L + b) := by
      have : (K0 + 3) * (ln + Le + L + b) =
          K0 * ln + K0 * Le + K0 * L + K0 * b + 3 * ln + 3 * Le + 3 * L + 3 * b := by ring
      rw [this]; linarith
    have h2 : (K0 + 3) * (ln + Le + L + b) ≤ 100 * K0 ^ 2 * (ln + Le + L + b) :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hK3]) (by linarith)
    linarith
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = b + ln + Le + L := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by linarith
  have hKX : (Bh : ℝ) + ℓ₁ + 3 ≤ K0 * X := by
    have : K0 * X = K0 * b + K0 * ln + K0 * Le + K0 * L := by rw [hX]; ring
    have h3 : 3 * 1 ≤ K0 * L := mul_le_mul hK3 hL (by norm_num) (by linarith)
    rw [this]; linarith only [hB1, hl1, h3, hKb, hKn, hKe]
  have hq1' : (q : ℝ) + 1 ≤ K0 * L := by
    have h1 : (Cu + 1) * L ≤ K0 * L := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (q : ℝ) ≤ Cu * L := hq
    have h3 : (Cu + 1) * L = Cu * L + L := by ring
    linarith only [h1, h2, h3, hL]
  have hQ : 2 * (q : ℝ) ≤ 100 * K0 ^ 2 * L := by
    have h1 : (2 * K0) * L ≤ (100 * K0 ^ 2) * L :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hK3]) (by linarith)
    have h2 : 2 * (q : ℝ) ≤ 2 * (K0 * L) := by linarith only [hq1']
    have h3 : 2 * (K0 * L) = (2 * K0) * L := by ring
    linarith only [h1, h2, h3]
  intro ℓ f hF hD
  let G : Prm := ⟨n, b, q, r, ℓ₁, f₁, Bh, fh, ℓ, f⟩
  have W : G.WF := ⟨by show r + b + fh + f₁ + q + 3 ≤ f; omega,
    by show f + Bh + ℓ₁ + 3 ≤ ℓ; omega⟩
  have hq2 := G.query_bound
  have hg := G.gate_bound W (by show 1 ≤ n; omega)
  have hbd := G.blockdiag W
  have hsc := G.sem_circuit W
  have hfp := G.sem_fp W
  have hun := uncontrolled_toCP G.NN (G.n * G.ℓ) G.Pfull
  obtain ⟨c, hc⟩ : ∃ c : OracleCircuit gatesRev (fun _ : Fin 1 => G.n * G.ℓ + 1) G.NN,
      c = toCP G.NN (G.n * G.ℓ) G.Pfull := ⟨_, rfl⟩
  rw [← hc] at hq2 hg hbd hsc hun
  refine ⟨G.W, c, hun, ?_, ?_, ?_, ?_⟩
  · have h : (c.queryCount 0 : ℝ) ≤ 2 * q := by
      have := (Nat.cast_le (α := ℝ)).mpr hq2
      rwa [Nat.cast_mul, Nat.cast_ofNat] at this
    exact le_trans h hQ
  · have hg' : (c.gateCount : ℝ) ≤
        18 * n * (Bh + 2) * (Bh + ℓ₁ + 3) + 54 * n * ℓ * (q + 1) := by
      have := (Nat.cast_le (α := ℝ)).mpr hg
      push_cast at this
      simpa [G, Prm.Kw] using this
    have := gate_real (n : ℝ) ℓ Bh ℓ₁ q X L K0 hK3 hL hX1 hKX hq1' (by positivity) (by positivity)
      (by positivity) (by positivity)
    rw [hX] at this
    exact le_trans hg' this
  · intro w θ y y' h
    exact hbd w θ y y' h
  · intro w θ zp sb hb hw ha _ hs hbase
    refine ⟨fun x => G.Htil w θ (ofQ (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x
      fun _ => false))), fun x => hsc zp sb hb x w θ, fun x => ?_⟩
    have hs1 : sb = decide ((if sb then (1 : ℤ) else -1) = 1) := by cases sb <;> simp
    have e := hfp zp sb hb x rfl _ hs1 w θ
    show |fpVal G.Vb G.Vf (G.Htil w θ (ofQ (G.fullB zp sb hb (regBasis G.n G.b G.Vb G.W x
      fun _ => false)))) - height w θ (addrOf n ℓ₁ f₁ zp) (rho n • gridVec n b x)| ≤ η
    rw [e, hs]
    exact (QuantumLTF.Membership.localizedAffineBisect_error hn ε hε hε2 w _ θ _ hw ha hbase x q).trans hqerr

end

end QuantumLTF.Membership.A2



open QAlgorithms QuantumLTF.Membership in
theorem solution (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε η : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < η → η < 1 / 8 →
      ∀ (b ℓ₁ f₁ Bh fh : ℕ), (ℓ₁ : ℝ) ≤ C₁ * Real.log n → f₁ ≤ ℓ₁ →
        (Bh : ℝ) ≤ C₂ * Real.log (1 / ε) → fh ≤ Bh →
      ∃ (Vb Vf F D : ℕ),
        (Vb : ℝ) ≤ C * (Real.log (1 / ε) + Real.log (1 / η)) ∧
        (F : ℝ) ≤ C * (Real.log n + Real.log (1 / ε) + Real.log (1 / η) + b) ∧
        (D : ℝ) ≤ C * (Real.log n + Real.log (1 / ε) + Real.log (1 / η) + b) ∧
        ∀ ℓ f : ℕ, F ≤ f → f + D ≤ ℓ →
        ∃ (W : ℕ) (c : OracleCircuit gatesRev (fun _ : Fin 1 => n * ℓ + 1)
            (n * ℓ₁ + 1 + Bh + (n * b + Vb + W))),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C * Real.log (1 / η) ∧
          (c.gateCount : ℝ) ≤ C * n * (b + Real.log n + Real.log (1 / ε) + Real.log (1 / η)) ^ 2 *
              Real.log (1 / η) + C * n * ℓ * Real.log (1 / η) ∧
          (∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
              (y y' : Qubits (n * ℓ₁ + 1 + Bh + (n * b + Vb + W))),
            (c.unitary fun _ => memOracle n ℓ f w θ) y' y ≠ 0 →
            ∀ i : Fin (n * ℓ₁ + 1 + Bh),
              y' (Fin.castAdd (n * b + Vb + W) i) = y (Fin.castAdd (n * b + Vb + W) i)) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) (zp : Qubits (n * ℓ₁)) (sb : Bool)
            (hb : Qubits Bh), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w (addrOf n ℓ₁ f₁ zp)| → |inner ℝ w (addrOf n ℓ₁ f₁ zp)| ≤ 3 →
            (if sb then (1 : ℤ) else -1) = sgn (inner ℝ w (addrOf n ℓ₁ f₁ zp)) →
            |fpVal Bh fh hb - height w θ (addrOf n ℓ₁ f₁ zp) 0| ≤ ε / 100 →
            ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, act (c.unitary fun _ => memOracle n ℓ f w θ)
                  (ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                    (regBasis n b Vb W x fun _ => false))) =
                ket (Fin.append (Fin.append (Fin.append zp (fun _ : Fin 1 => sb)) hb)
                    (regBasis n b Vb W x (Htil x)))) ∧
              ∀ x, |fpVal Vb Vf (Htil x) -
                height w θ (addrOf n ℓ₁ f₁ zp) (rho n • gridVec n b x)| ≤ η :=
  QuantumLTF.Membership.A2.uniform_height_circuit C₁ C₂ hC₁ hC₂
