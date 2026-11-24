-- Prove2me | solution 2 for QuantumLTF.Membership.localizedAffineBisect_circuit
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-23T23:29:17.17931+00:00
-- url     : https://prove2.me/submissions/e9431bc8-287b-4f72-a62d-273c286c032c

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_IsFp
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_regBasis
import Definitions.Def_QuantumLTF_Membership_addrOf

-- ===== Q1.lean =====

namespace LTFA
open QAlgorithms QuantumLTF.Membership

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

end

end LTFA

-- ===== Q2.lean =====

namespace LTFA
open QAlgorithms QuantumLTF.Membership

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

/-! ### Fill -/

abbrev Spec := Bool × Option ℕ

def oval (Z : ℕ → Bool) : Option ℕ → Bool
  | some a => Z a
  | none => false

def specVal (Z : ℕ → Bool) (sp : Spec) : Bool := xor sp.1 (oval Z sp.2)

def oIns (t : ℕ) : Option ℕ → List Ins
  | some a => [Ins.cnot a t]
  | none => []

def specIns (t : ℕ) (sp : Spec) : List Ins :=
  (if sp.1 then [Ins.not t] else []) ++ oIns t sp.2

def fill : List Spec → ℕ → List Ins
  | [], _ => []
  | sp :: sps, c => specIns c sp ++ fill sps (c + 1)

def SrcLt (sps : List Spec) (c : ℕ) : Prop := ∀ sp ∈ sps, ∀ a, sp.2 = some a → a < c

theorem specIns_sem (t : ℕ) (sp : Spec) (Z : ℕ → Bool) (hZ : Z t = false)
    (hs : ∀ a, sp.2 = some a → a ≠ t) :
    evalP A O (specIns t sp) Z = Function.update Z t (specVal Z sp) := by
  obtain ⟨k, o⟩ := sp
  cases k <;> cases o with
  | none => simp [specIns, oIns, evalP, specVal, oval, hZ]
  | some a =>
    have ha := hs a rfl
    simp [specIns, oIns, evalP, specVal, oval, hZ, Function.update_of_ne ha]
    all_goals (funext w; by_cases hw : w = t <;> simp [hw, Function.update_of_ne ha])

theorem fill_sem (sps : List Spec) (c : ℕ) (Z : ℕ → Bool) (hF : Fresh Z c) (hs : SrcLt sps c) :
    (∀ w, w < c → evalP A O (fill sps c) Z w = Z w) ∧
    Fresh (evalP A O (fill sps c) Z) (c + sps.length) ∧
    ∀ m (hm : m < sps.length), evalP A O (fill sps c) Z (c + m) = specVal Z sps[m] := by
  induction sps generalizing c Z with
  | nil =>
    refine ⟨fun _ _ => rfl, by simpa [fill, evalP] using hF, fun m hm => by simp at hm⟩
  | cons sp sps ih =>
    have hsp : ∀ a, sp.2 = some a → a ≠ c := fun a ha => (hs sp (by simp) a ha).ne
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
      obtain ⟨k, o⟩ := sp'
      cases o with
      | none => rfl
      | some a =>
        have := hs (k, some a) (by simp [h]) a rfl
        simp [specVal, oval, hZ1, Function.update_of_ne this.ne]
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

theorem fill_length (sps : List Spec) (c : ℕ) : (fill sps c).length ≤ 2 * sps.length := by
  induction sps generalizing c with
  | nil => simp [fill]
  | cons sp sps ih =>
    have := ih (c + 1)
    obtain ⟨k, o⟩ := sp
    cases k <;> cases o <;> simp [fill, specIns, oIns] <;> omega

theorem fill_noQ (sps : List Spec) (c : ℕ) : ∀ I ∈ fill sps c, I.isQ = false := by
  induction sps generalizing c with
  | nil => simp [fill]
  | cons sp sps ih =>
    intro I hI
    simp only [fill, specIns, List.mem_append] at hI
    rcases hI with (hI | hI) | hI
    · split_ifs at hI <;> simp at hI; subst hI; rfl
    · obtain ⟨k, o⟩ := sp; cases o <;> simp [oIns] at hI; subst hI; rfl
    · exact ih _ I hI

theorem fill_good (S : ℕ → Prop) (sps : List Spec) (c : ℕ)
    (hs : ∀ sp ∈ sps, ∀ a, sp.2 = some a → a < c ∧ S a) :
    ∀ I ∈ fill sps c, Good A S c (c + sps.length) I := by
  induction sps generalizing c with
  | nil => simp [fill]
  | cons sp sps ih =>
    intro I hI
    simp only [fill, specIns, List.mem_append] at hI
    rcases hI with (hI | hI) | hI
    · split_ifs at hI <;> simp at hI; subst hI
      refine ⟨le_rfl, by simp [Ins.tgt], fun s hs => ?_⟩; simp [Ins.src] at hs
    · obtain ⟨k, o⟩ := sp; cases o with
      | none => simp [oIns] at hI
      | some a =>
        simp [oIns] at hI; subst hI
        have := hs (k, some a) (by simp) a rfl
        refine ⟨le_rfl, by simp [Ins.tgt], fun s hs' => ?_⟩
        simp only [Ins.src] at hs'; subst hs'; exact this
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

end LTFA

-- ===== Q3.lean =====

namespace LTFA
open QAlgorithms QuantumLTF.Membership

noncomputable section

section
variable (A : ℕ) (O : Qubits A → Bool)

/-! ### Adding a filled register to a register -/

def addSpec (R : List ℕ) (sps : List Spec) (c : ℕ) : List Ins :=
  fill sps c ++ adder R (List.range' c R.length) (c + R.length) (c + R.length + 1)

def addOut (R : List ℕ) (c : ℕ) : List ℕ := adderOut R (c + R.length + 1)

theorem addSpec_sem (R : List ℕ) (sps : List Spec) (c : ℕ) (Z : ℕ → Bool)
    (hl : sps.length = R.length) (hR : ∀ a ∈ R, a < c) (hs : SrcLt sps c) (hF : Fresh Z c) :
    (∀ w, w < c → evalP A O (addSpec R sps c) Z w = Z w) ∧
    Fresh (evalP A O (addSpec R sps c) Z) (c + 3 * R.length + 1) ∧
    valLE ((addOut R c).map (evalP A O (addSpec R sps c) Z)) =
      (valLE (R.map Z) + valLE (sps.map (specVal Z))) % 2 ^ R.length := by
  obtain ⟨F1, F2, _⟩ := fill_sem A O sps c Z hF hs
  have Fm := fill_map A O sps c Z hF hs
  rw [hl] at F2 Fm
  set Z1 := evalP A O (fill sps c) Z
  obtain ⟨G1, G2, G3⟩ := adder_sem A O R (List.range' c R.length) (by simp) (c + R.length)
    (c + R.length + 1) Z1 (fun a ha => by have := hR a ha; omega)
    (fun b hb => by simp [List.mem_range'] at hb; omega) (by omega)
    (fun w hw => F2 w (by omega))
  simp only [addSpec, evalP_append]
  refine ⟨fun w hw => by rw [G1 w (by omega), F1 w hw], fun w hw => G2 w (by omega), ?_⟩
  rw [addOut, G3, Fm, F2 (c + R.length) le_rfl]
  have : R.map Z1 = R.map Z := List.map_congr_left (fun a ha => F1 a (hR a ha))
  rw [this]; simp

theorem addSpec_good (S : ℕ → Prop) (R : List ℕ) (sps : List Spec) (c : ℕ)
    (hl : sps.length = R.length) (hR : ∀ a ∈ R, a < c ∧ S a)
    (hs : ∀ sp ∈ sps, ∀ a, sp.2 = some a → a < c ∧ S a) (hS : ∀ w, c ≤ w → S w) :
    ∀ I ∈ addSpec R sps c, Good A S c (c + 3 * R.length + 1) I := by
  intro I hI
  simp only [addSpec, List.mem_append] at hI
  rcases hI with hI | hI
  · exact (fill_good A S sps c hs I hI).mono le_rfl (by omega)
  · have := adder_good A S R (List.range' c R.length) (c + R.length) (c + R.length + 1)
      (fun a ha => by have := hR a ha; exact ⟨by omega, this.2⟩)
      (fun b hb => by simp [List.mem_range'] at hb; exact ⟨by omega, hS b (by omega)⟩)
      ⟨by omega, hS _ (by omega)⟩ (fun w hw => hS w (by omega)) I hI
    exact this.mono (by omega) (by omega)

theorem addSpec_noQ (R : List ℕ) (sps : List Spec) (c : ℕ) :
    ∀ I ∈ addSpec R sps c, I.isQ = false := by
  intro I hI
  simp only [addSpec, List.mem_append] at hI
  rcases hI with hI | hI
  · exact fill_noQ sps c I hI
  · exact adder_noQ R _ _ _ I hI

theorem addSpec_length (R : List ℕ) (sps : List Spec) (c : ℕ) (hl : sps.length = R.length) :
    (addSpec R sps c).length ≤ 8 * R.length := by
  have h1 := fill_length sps c
  have h2 := adder_length R (List.range' c R.length) (c + R.length) (c + R.length + 1)
  simp only [addSpec, List.length_append]; omega

theorem addOut_length (R : List ℕ) (c : ℕ) : (addOut R c).length = R.length :=
  adderOut_length _ _

theorem addOut_bound (R : List ℕ) (c : ℕ) :
    ∀ w ∈ addOut R c, c ≤ w ∧ w < c + 3 * R.length + 1 := by
  intro w hw
  have := adderOut_bound R _ w hw
  omega

/-! ### Specs -/

def constSpecs : ℕ → ℕ → List Spec
  | _, 0 => []
  | K, len + 1 => (decide (K % 2 = 1), none) :: constSpecs (K / 2) len

def muxSpecs (d : ℕ) : ℕ → ℕ → ℕ → List Spec
  | _, _, 0 => []
  | K0, K1, len + 1 =>
      (decide (K0 % 2 = 1), if K0 % 2 = K1 % 2 then none else some d) ::
        muxSpecs d (K0 / 2) (K1 / 2) len

def copySpecs (R : List ℕ) : List Spec := R.map fun a => (false, some a)

theorem constSpecs_length (K len : ℕ) : (constSpecs K len).length = len := by
  induction len generalizing K with
  | zero => rfl
  | succ len ih => simp [constSpecs, ih]

theorem muxSpecs_length (d K0 K1 len : ℕ) : (muxSpecs d K0 K1 len).length = len := by
  induction len generalizing K0 K1 with
  | zero => rfl
  | succ len ih => simp [muxSpecs, ih]

theorem constSpecs_val (Z : ℕ → Bool) (K len : ℕ) :
    valLE ((constSpecs K len).map (specVal Z)) = K % 2 ^ len := by
  induction len generalizing K with
  | zero => simp [constSpecs, Nat.mod_one]
  | succ len ih =>
    simp only [constSpecs, List.map_cons, valLE_cons, ih]
    rw [pow_succ', Nat.mod_mul]
    congr 1
    simp only [specVal, oval, Bool.xor_false]
    rcases Nat.mod_two_eq_zero_or_one K with h | h <;> simp [h]

theorem muxSpecs_map (Z : ℕ → Bool) (d K0 K1 len : ℕ) :
    (muxSpecs d K0 K1 len).map (specVal Z) =
      (constSpecs (if Z d then K1 else K0) len).map (specVal Z) := by
  induction len generalizing K0 K1 with
  | zero => rfl
  | succ len ih =>
    simp only [muxSpecs, constSpecs, List.map_cons, ih]
    congr 1
    · simp only [specVal]
      rcases Nat.mod_two_eq_zero_or_one K0 with h0 | h0 <;>
        rcases Nat.mod_two_eq_zero_or_one K1 with h1 | h1 <;>
        cases hz : Z d <;> simp [h0, h1, hz, oval]
    · cases Z d <;> rfl

theorem muxSpecs_val (Z : ℕ → Bool) (d K0 K1 len : ℕ) :
    valLE ((muxSpecs d K0 K1 len).map (specVal Z)) = (if Z d then K1 else K0) % 2 ^ len := by
  rw [muxSpecs_map, constSpecs_val]

theorem copySpecs_map (Z : ℕ → Bool) (R : List ℕ) :
    (copySpecs R).map (specVal Z) = R.map Z := by
  simp [copySpecs, specVal, oval]

theorem constSpecs_src (K len : ℕ) : ∀ sp ∈ constSpecs K len, sp.2 = none := by
  induction len generalizing K with
  | zero => simp [constSpecs]
  | succ len ih =>
    intro sp hsp
    simp only [constSpecs, List.mem_cons] at hsp
    rcases hsp with rfl | h
    · rfl
    · exact ih _ sp h

theorem muxSpecs_src (d K0 K1 len : ℕ) : ∀ sp ∈ muxSpecs d K0 K1 len, ∀ a, sp.2 = some a → a = d := by
  induction len generalizing K0 K1 with
  | zero => simp [muxSpecs]
  | succ len ih =>
    intro sp hsp a ha
    simp only [muxSpecs, List.mem_cons] at hsp
    rcases hsp with rfl | h
    · simp only at ha; split_ifs at ha; simp at ha; exact ha.symm
    · exact ih _ _ sp h a ha

theorem copySpecs_src (R : List ℕ) : ∀ sp ∈ copySpecs R, ∀ a, sp.2 = some a → a ∈ R := by
  intro sp hsp a ha
  simp only [copySpecs, List.mem_map] at hsp
  obtain ⟨b, hb, rfl⟩ := hsp
  simp at ha; subst ha; exact hb

theorem valLE_replicate_append (o : ℕ) (L : List Bool) :
    valLE (List.replicate o false ++ L) = 2 ^ o * valLE L := by
  induction o with
  | zero => simp
  | succ o ih => simp [List.replicate_succ, ih, pow_succ]; ring

theorem valLE_append_replicate (L : List Bool) (k : ℕ) :
    valLE (L ++ List.replicate k false) = valLE L := by
  induction L with
  | nil =>
    simp only [List.nil_append, valLE_nil]
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ih]
  | cons b L ih => simp [ih]

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
      have := copySpecs_src R.reverse sp hsp a ha
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
      simp [copySpecs, specVal, oval]
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
        hR R (by simp) a (List.mem_reverse.mp (copySpecs_src R.reverse sp hsp a ha))) I hI
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
    have h2 := fill_length (copySpecs R.reverse) c
    have h3 : (copySpecs R.reverse).length = ℓ := by simp [copySpecs, hl R (by simp)]
    rw [h3] at h2
    simp only [copyRegs, List.length_append, List.length_cons]
    rw [mul_add]; omega

/-! ### Updating a list of tracks by a bit-controlled constant -/

def Kc (z : ℤ) (len : ℕ) : ℕ := (z % (2 : ℤ) ^ len).toNat

def updP (d e : ℕ) (u : ℕ → ℤ) : ℕ → List (List ℕ) → ℕ → List Ins
  | _, [], _ => []
  | j, R :: Rs, c =>
      addSpec R (muxSpecs d (Kc (-(u j * 2 ^ e)) R.length) (Kc (u j * 2 ^ e) R.length) R.length)
        c ++ updP d e u (j + 1) Rs (c + 3 * R.length + 1)

def updT : List (List ℕ) → ℕ → List (List ℕ)
  | [], _ => []
  | R :: Rs, c => addOut R c :: updT Rs (c + 3 * R.length + 1)

def updE : List (List ℕ) → ℕ → ℕ
  | [], c => c
  | R :: Rs, c => updE Rs (c + 3 * R.length + 1)

theorem updE_ge (Rs : List (List ℕ)) (c : ℕ) : c ≤ updE Rs c := by
  induction Rs generalizing c with
  | nil => exact le_rfl
  | cons R Rs ih => exact le_trans (by omega) (ih _)

theorem updE_eq (ℓ : ℕ) (Rs : List (List ℕ)) (hl : ∀ R ∈ Rs, R.length ≤ ℓ) (c : ℕ) :
    updE Rs c ≤ c + (3 * ℓ + 1) * Rs.length := by
  induction Rs generalizing c with
  | nil => simp [updE]
  | cons R Rs ih =>
    have := ih (fun R' h => hl R' (by simp [h])) (c + 3 * R.length + 1)
    have h2 := hl R (by simp)
    simp only [updE, List.length_cons]
    rw [mul_add]; nlinarith

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
    | zero => simp [updT, addOut_length]
    | succ t => simp only [updT, List.getD_cons_succ]; exact ih _ _

theorem updT_bound (Rs : List (List ℕ)) (c : ℕ) :
    ∀ R ∈ updT Rs c, ∀ w ∈ R, c ≤ w ∧ w < updE Rs c := by
  induction Rs generalizing c with
  | nil => simp [updT]
  | cons R Rs ih =>
    intro R' hR' w hw
    simp only [updT, List.mem_cons] at hR'
    rcases hR' with rfl | h
    · have := addOut_bound R c w hw
      have := updE_ge Rs (c + 3 * R.length + 1)
      simp only [updE]; omega
    · have := ih _ R' h w hw
      simp only [updE]; omega

theorem updT_len (ℓ : ℕ) (Rs : List (List ℕ)) (c : ℕ) :
    ∀ R ∈ updT Rs c, ∃ R0 ∈ Rs, R.length = R0.length := by
  induction Rs generalizing c with
  | nil => simp [updT]
  | cons R Rs ih =>
    intro R' hR'
    simp only [updT, List.mem_cons] at hR'
    rcases hR' with rfl | h
    · exact ⟨R, by simp, addOut_length _ _⟩
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
      · exact ⟨R, by simp, addOut_length _ _⟩
      · obtain ⟨R0, h0, e⟩ := ih n _ R' h
        exact ⟨R0, by simp [h0], e⟩

theorem updP_sem (d e : ℕ) (u : ℕ → ℤ) (j : ℕ) (Rs : List (List ℕ)) (c : ℕ) (Z : ℕ → Bool)
    (hd : d < c) (hR : ∀ R ∈ Rs, ∀ a ∈ R, a < c) (hF : Fresh Z c) :
    (∀ w, w < c → evalP A O (updP d e u j Rs c) Z w = Z w) ∧
    Fresh (evalP A O (updP d e u j Rs c) Z) (updE Rs c) ∧
    ∀ t, t < Rs.length →
      valLE (((updT Rs c).getD t []).map (evalP A O (updP d e u j Rs c) Z)) =
        (valLE ((Rs.getD t []).map Z) +
          (if Z d then Kc (u (j + t) * 2 ^ e) (Rs.getD t []).length
            else Kc (-(u (j + t) * 2 ^ e)) (Rs.getD t []).length)) %
          2 ^ (Rs.getD t []).length := by
  induction Rs generalizing j c Z with
  | nil => exact ⟨fun _ _ => rfl, by simpa [updP, updE, evalP] using hF, fun t ht => by simp at ht⟩
  | cons R Rs ih =>
    set sps := muxSpecs d (Kc (-(u j * 2 ^ e)) R.length) (Kc (u j * 2 ^ e) R.length) R.length
    have hs : SrcLt sps c := fun sp hsp a ha => by
      rw [muxSpecs_src d _ _ _ sp hsp a ha]; exact hd
    obtain ⟨F1, F2, F3⟩ := addSpec_sem A O R sps c Z (muxSpecs_length _ _ _ _)
      (hR R (by simp)) hs hF
    set Z1 := evalP A O (addSpec R sps c) Z
    obtain ⟨G1, G2, G3⟩ := ih (j + 1) (c + 3 * R.length + 1) Z1 (by omega)
      (fun R' h a ha => by have := hR R' (by simp [h]) a ha; omega) F2
    simp only [updP, evalP_append]
    refine ⟨fun w hw => by rw [G1 w (by omega), F1 w hw], G2, ?_⟩
    intro t ht
    cases t with
    | zero =>
      simp only [updT, List.getD_cons_zero, Nat.add_zero]
      have : (addOut R c).map (evalP A O (updP d e u (j + 1) Rs (c + 3 * R.length + 1)) Z1) =
          (addOut R c).map Z1 :=
        List.map_congr_left (fun w hw => G1 w (by have := addOut_bound R c w hw; omega))
      rw [this, F3, muxSpecs_val]
      exact Nat.add_mod_mod _ _ _
    | succ t =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at ht
      simp only [updT, List.getD_cons_succ]
      rw [G3 t ht, show j + 1 + t = j + (t + 1) by ring, F1 d hd]
      have hmem : (Rs.getD t []) ∈ Rs := by
        rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
      have : (Rs.getD t []).map Z1 = (Rs.getD t []).map Z :=
        List.map_congr_left (fun w hw => F1 w (hR _ (List.mem_cons_of_mem _ hmem) w hw))
      rw [this]

theorem updP_good (S : ℕ → Prop) (d e : ℕ) (u : ℕ → ℤ) (j : ℕ) (Rs : List (List ℕ)) (c : ℕ)
    (hd : d < c ∧ S d) (hR : ∀ R ∈ Rs, ∀ a ∈ R, a < c ∧ S a) (hS : ∀ w, c ≤ w → S w) :
    ∀ I ∈ updP d e u j Rs c, Good A S c (updE Rs c) I := by
  induction Rs generalizing j c with
  | nil => simp [updP]
  | cons R Rs ih =>
    intro I hI
    simp only [updP, List.mem_append] at hI
    rcases hI with hI | hI
    · have := addSpec_good A S R _ c (muxSpecs_length _ _ _ _) (hR R (by simp))
        (fun sp hsp a ha => by rw [muxSpecs_src d _ _ _ sp hsp a ha]; exact hd) hS I hI
      exact this.mono le_rfl (by simp only [updE]; exact updE_ge _ _)
    · have := ih (j + 1) (c + 3 * R.length + 1) ⟨by omega, hd.2⟩
        (fun R' h a ha => by have := hR R' (by simp [h]) a ha; exact ⟨by omega, this.2⟩)
        (fun w hw => hS w (by omega)) I hI
      exact this.mono (by omega) (by simp [updE])

theorem updP_noQ (d e : ℕ) (u : ℕ → ℤ) (j : ℕ) (Rs : List (List ℕ)) (c : ℕ) :
    ∀ I ∈ updP d e u j Rs c, I.isQ = false := by
  induction Rs generalizing j c with
  | nil => simp [updP]
  | cons R Rs ih =>
    intro I hI
    simp only [updP, List.mem_append] at hI
    rcases hI with hI | hI
    · exact addSpec_noQ _ _ _ I hI
    · exact ih _ _ I hI

theorem updP_length (ℓ : ℕ) (d e : ℕ) (u : ℕ → ℤ) (j : ℕ) (Rs : List (List ℕ))
    (hl : ∀ R ∈ Rs, R.length ≤ ℓ) (c : ℕ) :
    (updP d e u j Rs c).length ≤ 8 * ℓ * Rs.length := by
  induction Rs generalizing j c with
  | nil => simp [updP]
  | cons R Rs ih =>
    have h1 := ih (j + 1) (fun R' h => hl R' (by simp [h])) (c + 3 * R.length + 1)
    have h2 := addSpec_length R (muxSpecs d (Kc (-(u j * 2 ^ e)) R.length)
      (Kc (u j * 2 ^ e) R.length) R.length) c (muxSpecs_length _ _ _ _)
    have h3 := hl R (by simp)
    simp only [updP, List.length_append, List.length_cons]
    rw [mul_add]; nlinarith

end

end

end LTFA

-- ===== Q4.lean =====

namespace LTFA
open QAlgorithms QuantumLTF.Membership

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

theorem track_step (N len : ℕ) (z : ℤ) (V : ℝ) (hN : (N : ℝ) + z = V) (h0 : 0 ≤ V)
    (h1 : V < 2 ^ len) : (((N + Kc z len) % 2 ^ len : ℕ) : ℝ) = V := by
  have hz : 0 ≤ z % (2 : ℤ) ^ len := Int.emod_nonneg _ (by positivity)
  have hV : ((N : ℤ) + z : ℤ) = ((N : ℤ) + z : ℤ) := rfl
  have h0' : (0 : ℤ) ≤ N + z := by
    have : ((((N : ℤ) + z : ℤ)) : ℝ) = V := by push_cast; exact hN
    exact_mod_cast (this ▸ h0 : (0:ℝ) ≤ (((N : ℤ) + z : ℤ) : ℝ))
  have h1' : (N : ℤ) + z < 2 ^ len := by
    have : ((((N : ℤ) + z : ℤ)) : ℝ) = V := by push_cast; exact hN
    have h2 : (((N : ℤ) + z : ℤ) : ℝ) < ((2 ^ len : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  have key : (((N + Kc z len) % 2 ^ len : ℕ) : ℤ) = N + z := by
    rw [Int.natCast_mod, Nat.cast_add, Kc, Int.toNat_of_nonneg hz]
    push_cast
    rw [Int.add_emod_emod, Int.emod_eq_of_lt h0' h1']
  have : ((((N + Kc z len) % 2 ^ len : ℕ) : ℤ) : ℝ) = (((N : ℤ) + z : ℤ) : ℝ) := by rw [key]
  rw [← hN]
  push_cast at this
  exact this

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
variable (n ℓ : ℕ) (s1 : Bool) (u : ℕ → ℤ)

def rP : ℕ → List (List ℕ) → ℕ → List Ins
  | 0, _, _ => []
  | m + 1, Ts, c =>
      copyRegs (Ts.take n) c ++ (Ins.qry c :: (if s1 then [] else [Ins.not (c + n * ℓ)])) ++
        (updP (c + n * ℓ) m u 0 Ts (c + n * ℓ + 1) ++
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
    (hS : ∀ w, c ≤ w → S w) :
    ∀ I ∈ rP n ℓ s1 u m Ts c, Good (n * ℓ) S c (rE n ℓ m Ts c) I := by
  induction m generalizing Ts c with
  | zero => simp [rP]
  | succ m ih =>
    intro I hI
    have hE1 := updE_ge Ts (c + n * ℓ + 1)
    have hE2 := rE_ge n ℓ m (updT Ts (c + n * ℓ + 1)) (updE Ts (c + n * ℓ + 1))
    simp only [rE] at *
    simp only [rP, List.mem_append, List.mem_cons] at hI
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
    · split_ifs at hI <;> simp at hI
      subst hI
      refine ⟨by simp [Ins.tgt], by simp [Ins.tgt]; omega, fun s hs => ?_⟩
      simp [Ins.src] at hs
    · have := updP_good (n * ℓ) S (c + n * ℓ) m u 0 Ts (c + n * ℓ + 1)
        ⟨by omega, hS _ (by omega)⟩
        (fun R h a ha => by have := hR R h a ha; exact ⟨by omega, this.2⟩)
        (fun w hw => hS w (by omega)) I hI
      exact this.mono (by omega) hE2
    · have := ih (updT Ts (c + n * ℓ + 1)) (updE Ts (c + n * ℓ + 1)) (take_len_of n ℓ Ts hl _)
        (fun R h a ha => by
          have := updT_bound Ts (c + n * ℓ + 1) R h a ha
          exact ⟨this.2, hS a (by omega)⟩)
        (fun w hw => hS w (by omega)) I hI
      exact this.mono (by omega) le_rfl

theorem rP_countQ (m : ℕ) (Ts : List (List ℕ)) (c : ℕ) :
    (rP n ℓ s1 u m Ts c).countP Ins.isQ = m := by
  induction m generalizing Ts c with
  | zero => rfl
  | succ m ih =>
    simp only [rP, List.countP_append, List.countP_cons, ih]
    have h1 : (copyRegs (Ts.take n) c).countP Ins.isQ = 0 :=
      List.countP_eq_zero.mpr (fun I hI => by simp [copyRegs_noQ _ _ I hI])
    have h2 : (updP (c + n * ℓ) m u 0 Ts (c + n * ℓ + 1)).countP Ins.isQ = 0 :=
      List.countP_eq_zero.mpr (fun I hI => by simp [updP_noQ _ _ _ _ _ _ I hI])
    have h3 : (if s1 then ([] : List Ins) else [Ins.not (c + n * ℓ)]).countP Ins.isQ = 0 := by
      split_ifs <;> simp [Ins.isQ]
    rw [h1, h2, h3]; simp [Ins.isQ]; omega

theorem rP_length (Lm : ℕ) (m : ℕ) (Ts : List (List ℕ)) (c : ℕ)
    (hl : ∀ R ∈ Ts.take n, R.length = ℓ) (hL : ∀ R ∈ Ts, R.length ≤ Lm) :
    (rP n ℓ s1 u m Ts c).length ≤ m * (2 * ℓ * n + 2 + 8 * Lm * Ts.length) := by
  induction m generalizing Ts c with
  | zero => simp [rP]
  | succ m ih =>
    have h1 := copyRegs_length ℓ (Ts.take n) hl c
    have h1' : (Ts.take n).length ≤ n := List.length_take_le _ _
    have h2 := updP_length Lm (c + n * ℓ) m u 0 Ts hL (c + n * ℓ + 1)
    have h3 := ih (updT Ts (c + n * ℓ + 1)) (updE Ts (c + n * ℓ + 1)) (take_len_of n ℓ Ts hl _)
      (fun R h => by
        obtain ⟨R0, h0, e⟩ := updT_len 0 Ts _ R h
        rw [e]; exact hL R0 h0)
    rw [updT_length] at h3
    have h4 : (if s1 then ([] : List Ins) else [Ins.not (c + n * ℓ)]).length ≤ 1 := by
      split_ifs <;> simp
    simp only [rP, List.length_append, List.length_cons]
    have : 2 * ℓ * (Ts.take n).length ≤ 2 * ℓ * n := Nat.mul_le_mul_left _ h1'
    nlinarith

/-! ### Semantics of the rounds -/

theorem rP_sem (f q : ℕ) (s : ℤ) (p x' : EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → ℤ) (hg : ∀ y, g y = 1 ∨ g y = -1)
    (hs1 : s1 = decide (s = 1))
    (htil : ℝ) (len fr : ℕ → ℕ) (val : ℕ → ℝ → ℝ) (slope : ℕ → ℝ)
    (hlen : ∀ j, j < n → len j = ℓ) (hfr : ∀ j, j < n → fr j = f)
    (hval : ∀ j (hj : j < n) mid, val j mid = x' ⟨j, hj⟩ + mid * p ⟨j, hj⟩)
    (haff : ∀ j, j < n + 1 → ∀ mid δ, val j (mid + δ) = val j mid + δ * slope j)
    (hu : ∀ j, j < n + 1 → (u j : ℝ) = 2 ^ (fr j) * slope j / 2 ^ (q + 2))
    (hrange : ∀ j, j < n + 1 → ∀ mid, htil - 1 / 4 ≤ mid → mid ≤ htil + 1 / 4 →
      |2 ^ (fr j) * val j mid| < 2 ^ (len j) / 2) :
    ∀ m, m ≤ q → ∀ (lo L : ℝ) (Ts : List (List ℕ)) (c : ℕ) (Z : ℕ → Bool),
      L = 2 ^ m / 2 ^ (q + 1) → htil - 1 / 4 ≤ lo → lo + L ≤ htil + 1 / 4 →
      Ts.length = n + 1 →
      (∀ j, j < n + 1 → (Ts.getD j []).length = len j ∧
        (valLE ((Ts.getD j []).map Z) : ℝ) = 2 ^ (len j) / 2 + 2 ^ (fr j) * val j (lo + L / 2)) →
      (∀ R ∈ Ts, ∀ a ∈ R, a < c) → Fresh Z c →
      let O : Qubits (n * ℓ) → Bool := fun y => decide (g (addrOf n ℓ f y) = -1)
      (∀ w, w < c → evalP (n * ℓ) O (rP n ℓ s1 u m Ts c) Z w = Z w) ∧
      Fresh (evalP (n * ℓ) O (rP n ℓ s1 u m Ts c) Z) (rE n ℓ m Ts c) ∧
      ∀ j, j < n + 1 →
        (valLE (((rT n ℓ m Ts c).getD j []).map (evalP (n * ℓ) O (rP n ℓ s1 u m Ts c) Z)) : ℝ) =
          2 ^ (len j) / 2 + 2 ^ (fr j) *
            val j ((affineBoundaryBisect p x' s m lo (lo + L)).run g) := by
  intro m
  induction m with
  | zero =>
    intro _ lo L Ts c Z _ _ _ _ hTs _ hF O
    refine ⟨fun _ _ => rfl, hF, fun j hj => ?_⟩
    have : (lo + (lo + L)) / 2 = lo + L / 2 := by ring
    simp only [rP, rT, affineBoundaryBisect, QueryTree.run, this]
    exact (hTs j hj).2
  | succ m ih =>
    intro hm lo L Ts c Z hL hlo1 hlo2 hTl hTs hTw hF O
    -- the take-n tracks have length ℓ
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
    -- the query block
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
    -- step 2: query (and flip)
    set bit := xor (decide (g (x' + mid • p) = -1)) (!s1) with hbit
    have hZ1d : Z1 d = false := C2 d (by omega)
    have e2 : evalP (n * ℓ) O (Ins.qry c :: (if s1 then [] else [Ins.not d])) Z1 =
        Function.update Z1 d bit := by
      have hq : (Ins.qry c).eval (n * ℓ) O Z1 =
          Function.update Z1 d (decide (g (x' + mid • p) = -1)) := by
        simp only [Ins.eval, Ins.tgt, Ins.fn]
        rw [← hd, hZ1d, Bool.false_xor]
        congr 2
        simp only [O]
        rw [hblock]
      rw [evalP_cons, hq]
      cases s1
      · simp [evalP, bit]
      · simp [evalP, bit]
    -- step 3: update tracks
    set Z2 := Function.update Z1 d bit with hZ2
    have hF2 : Fresh Z2 (d + 1) := by
      intro w hw; rw [hZ2, Function.update_of_ne (by omega)]; exact C2 w (by omega)
    have hZ2lt : ∀ w, w < c → Z2 w = Z w := by
      intro w hw; rw [hZ2, Function.update_of_ne (by omega), C1 w hw]
    obtain ⟨D1, D2, D3⟩ := updP_sem (n * ℓ) O d m u 0 Ts (d + 1) Z2 (by omega)
      (fun R h a ha => by have := hTw R h a ha; omega) hF2
    set Z3 := evalP (n * ℓ) O (updP d m u 0 Ts (d + 1)) Z2 with hZ3
    -- step 4: induction hypothesis
    set lo' := if bit then lo + L / 2 else lo with hlo'
    have hL' : L / 2 = 2 ^ m / 2 ^ (q + 1) := by rw [hL, pow_succ]; ring
    have hlo'1 : htil - 1 / 4 ≤ lo' := by
      have : 0 ≤ L := by rw [hL]; positivity
      simp only [hlo']; split_ifs <;> linarith
    have hlo'2 : lo' + L / 2 ≤ htil + 1 / 4 := by
      have : 0 ≤ L := by rw [hL]; positivity
      simp only [hlo']; split_ifs <;> linarith
    have hTs' : ∀ j, j < n + 1 → ((updT Ts (d + 1)).getD j []).length = len j ∧
        (valLE (((updT Ts (d + 1)).getD j []).map Z3) : ℝ) =
          2 ^ (len j) / 2 + 2 ^ (fr j) * val j (lo' + L / 2 / 2) := by
      intro j hj
      refine ⟨by rw [updT_getD_length]; exact (hTs j hj).1, ?_⟩
      rw [D3 j (by omega), (hTs j hj).1]
      have hmap : (Ts.getD j []).map Z2 = (Ts.getD j []).map Z := by
        apply List.map_congr_left
        intro w hw
        apply hZ2lt
        have hmem : Ts.getD j [] ∈ Ts := by rw [hgetD j hj]; exact List.getElem_mem _
        exact hTw _ hmem w hw
      have hZ2d : Z2 d = bit := by simp [hZ2]
      rw [hmap, hZ2d, Nat.zero_add]
      have hval0 := (hTs j hj).2
      set z : ℤ := if bit then u j * 2 ^ m else -(u j * 2 ^ m) with hz
      have hK : (if bit then Kc (u j * 2 ^ m) (len j) else Kc (-(u j * 2 ^ m)) (len j)) =
          Kc z (len j) := by simp only [hz]; split_ifs <;> rfl
      rw [hK]
      have hmid' : lo' + L / 2 / 2 = mid + (if bit then L / 4 else -(L / 4)) := by
        simp only [hlo', hmid]; split_ifs <;> ring
      have hrng := hrange j hj (lo' + L / 2 / 2) (by
          have : 0 ≤ L := by rw [hL]; positivity
          linarith) (by
          have : 0 ≤ L := by rw [hL]; positivity
          linarith)
      apply track_step
      · rw [hval0, hmid', haff j hj mid, hz]
        have hu' := hu j hj
        have hL4 : L / 4 = 2 ^ m / 2 ^ (q + 2) := by
          rw [hL, pow_succ, pow_succ, pow_succ]; ring
        split_ifs
        · push_cast; rw [hu', hL4]; ring
        · push_cast; rw [hu', hL4]; ring
      · have := (abs_lt.mp hrng).1; linarith
      · have := (abs_lt.mp hrng).2
        have h2 : (2 : ℝ) ^ (len j) / 2 + 2 ^ (len j) / 2 = 2 ^ len j := by ring
        linarith
    obtain ⟨E1, E2, E3⟩ := ih (by omega) lo' (L / 2) (updT Ts (d + 1)) (updE Ts (d + 1)) Z3 hL'
      hlo'1 hlo'2 (by rw [updT_length, hTl]) hTs'
      (fun R h a ha => (updT_bound Ts (d + 1) R h a ha).2) D2
    -- assemble
    have hP : rP n ℓ s1 u (m + 1) Ts c = (copyRegs (Ts.take n) c ++
        (Ins.qry c :: (if s1 then [] else [Ins.not d]))) ++
        (updP d m u 0 Ts (d + 1) ++ rP n ℓ s1 u m (updT Ts (d + 1)) (updE Ts (d + 1))) := rfl
    have hev : evalP (n * ℓ) O (rP n ℓ s1 u (m + 1) Ts c) Z =
        evalP (n * ℓ) O (rP n ℓ s1 u m (updT Ts (d + 1)) (updE Ts (d + 1))) Z3 := by
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

end LTFA

-- ===== Q5.lean =====

namespace LTFA
open QAlgorithms QuantumLTF.Membership

noncomputable section

/-! ### Initial address tracks -/

def xLE (b i : ℕ) : List ℕ := ((List.range b).map (fun j => j + b * i)).reverse

def shiftSpecs (b ℓ o i : ℕ) : List Spec :=
  List.replicate o (false, none) ++ copySpecs (xLE b i) ++ List.replicate (ℓ - o - b) (false, none)

def trackInit (b ℓ o : ℕ) (Ki : ℕ → ℕ) (i c : ℕ) : List Ins :=
  fill (shiftSpecs b ℓ o i) c ++ addSpec (List.range' c ℓ) (constSpecs (Ki i) ℓ) (c + ℓ)

def trackOut (ℓ c : ℕ) : List ℕ := addOut (List.range' c ℓ) (c + ℓ)

def initP (b ℓ o : ℕ) (Ki : ℕ → ℕ) : ℕ → ℕ → List Ins
  | 0, _ => []
  | k + 1, c => initP b ℓ o Ki k c ++ trackInit b ℓ o Ki k (c + k * (4 * ℓ + 1))

def initT (ℓ : ℕ) : ℕ → ℕ → List (List ℕ)
  | 0, _ => []
  | k + 1, c => initT ℓ k c ++ [trackOut ℓ (c + k * (4 * ℓ + 1))]

theorem xLE_length (b i : ℕ) : (xLE b i).length = b := by simp [xLE]

theorem shiftSpecs_length (b ℓ o i : ℕ) (h : o + b ≤ ℓ) : (shiftSpecs b ℓ o i).length = ℓ := by
  simp [shiftSpecs, copySpecs, xLE_length]; omega

theorem trackOut_length (ℓ c : ℕ) : (trackOut ℓ c).length = ℓ := by
  simp [trackOut, addOut_length]

theorem trackOut_bound (ℓ c : ℕ) : ∀ w ∈ trackOut ℓ c, c ≤ w ∧ w < c + 4 * ℓ + 1 := by
  intro w hw
  have := addOut_bound (List.range' c ℓ) (c + ℓ) w hw
  simp at this; omega

section
variable (A : ℕ) (O : Qubits A → Bool)

theorem shiftSpecs_val (b ℓ o i : ℕ) (Z : ℕ → Bool) :
    valLE ((shiftSpecs b ℓ o i).map (specVal Z)) = 2 ^ o * valLE ((xLE b i).map Z) := by
  simp only [shiftSpecs, List.map_append, List.map_replicate]
  have e : specVal Z (false, none) = false := rfl
  rw [e, List.append_assoc, valLE_replicate_append, valLE_append_replicate, copySpecs_map]

theorem trackInit_sem (b ℓ o : ℕ) (Ki : ℕ → ℕ) (i c : ℕ) (Z : ℕ → Bool) (hob : o + b ≤ ℓ)
    (hx : ∀ a ∈ xLE b i, a < c) (hF : Fresh Z c) :
    (∀ w, w < c → evalP A O (trackInit b ℓ o Ki i c) Z w = Z w) ∧
    Fresh (evalP A O (trackInit b ℓ o Ki i c) Z) (c + 4 * ℓ + 1) ∧
    valLE ((trackOut ℓ c).map (evalP A O (trackInit b ℓ o Ki i c) Z)) =
      (2 ^ o * valLE ((xLE b i).map Z) + Ki i % 2 ^ ℓ) % 2 ^ ℓ := by
  have hs : SrcLt (shiftSpecs b ℓ o i) c := by
    intro sp hsp a ha
    simp only [shiftSpecs, List.mem_append, List.mem_replicate] at hsp
    rcases hsp with (⟨_, rfl⟩ | hsp) | ⟨_, rfl⟩
    · simp at ha
    · exact hx a (copySpecs_src _ sp hsp a ha)
    · simp at ha
  obtain ⟨F1, F2, _⟩ := fill_sem A O _ c Z hF hs
  have Fm := fill_map A O _ c Z hF hs
  rw [shiftSpecs_length b ℓ o i hob] at F2 Fm
  set Z1 := evalP A O (fill (shiftSpecs b ℓ o i) c) Z
  obtain ⟨G1, G2, G3⟩ := addSpec_sem A O (List.range' c ℓ) (constSpecs (Ki i) ℓ) (c + ℓ) Z1
    (by simp [constSpecs_length]) (fun a ha => by simp [List.mem_range'] at ha; omega)
    (fun sp hsp a ha => by rw [constSpecs_src _ _ sp hsp] at ha; simp at ha) F2
  simp only [List.length_range'] at G2 G3
  simp only [trackInit, evalP_append]
  refine ⟨fun w hw => by rw [G1 w (by omega), F1 w hw], fun w hw => G2 w (by omega), ?_⟩
  rw [trackOut, G3, Fm, shiftSpecs_val, constSpecs_val]

theorem trackInit_good (S : ℕ → Prop) (b ℓ o : ℕ) (Ki : ℕ → ℕ) (i c : ℕ) (hob : o + b ≤ ℓ)
    (hx : ∀ a ∈ xLE b i, a < c ∧ S a) (hS : ∀ w, c ≤ w → S w) :
    ∀ I ∈ trackInit b ℓ o Ki i c, Good A S c (c + 4 * ℓ + 1) I := by
  intro I hI
  simp only [trackInit, List.mem_append] at hI
  rcases hI with hI | hI
  · have := fill_good A S (shiftSpecs b ℓ o i) c (by
      intro sp hsp a ha
      simp only [shiftSpecs, List.mem_append, List.mem_replicate] at hsp
      rcases hsp with (⟨_, rfl⟩ | hsp) | ⟨_, rfl⟩
      · simp at ha
      · exact hx a (copySpecs_src _ sp hsp a ha)
      · simp at ha) I hI
    rw [shiftSpecs_length b ℓ o i hob] at this
    exact this.mono le_rfl (by omega)
  · have := addSpec_good A S (List.range' c ℓ) (constSpecs (Ki i) ℓ) (c + ℓ)
      (by simp [constSpecs_length])
      (fun a ha => by simp [List.mem_range'] at ha; exact ⟨by omega, hS a (by omega)⟩)
      (fun sp hsp a ha => by rw [constSpecs_src _ _ sp hsp] at ha; simp at ha)
      (fun w hw => hS w (by omega)) I hI
    simp only [List.length_range'] at this
    exact this.mono (by omega) (by omega)

theorem trackInit_noQ (b ℓ o : ℕ) (Ki : ℕ → ℕ) (i c : ℕ) :
    ∀ I ∈ trackInit b ℓ o Ki i c, I.isQ = false := by
  intro I hI
  simp only [trackInit, List.mem_append] at hI
  rcases hI with hI | hI
  · exact fill_noQ _ _ I hI
  · exact addSpec_noQ _ _ _ I hI

theorem trackInit_length (b ℓ o : ℕ) (Ki : ℕ → ℕ) (i c : ℕ) (hob : o + b ≤ ℓ) :
    (trackInit b ℓ o Ki i c).length ≤ 10 * ℓ := by
  have h1 := fill_length (shiftSpecs b ℓ o i) c
  rw [shiftSpecs_length b ℓ o i hob] at h1
  have h2 := addSpec_length (List.range' c ℓ) (constSpecs (Ki i) ℓ) (c + ℓ)
    (by simp [constSpecs_length])
  simp only [List.length_range'] at h2
  simp only [trackInit, List.length_append]; omega

theorem initT_length (ℓ k c : ℕ) : (initT ℓ k c).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [initT, ih]

theorem initT_getD (ℓ k c i : ℕ) (hi : i < k) :
    (initT ℓ k c).getD i [] = trackOut ℓ (c + i * (4 * ℓ + 1)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [initT]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [List.getD_append _ _ _ _ (by rw [initT_length]; exact h), ih h]
    · subst h
      rw [List.getD_append_right _ _ _ _ (by rw [initT_length]), initT_length]
      simp

theorem initT_mem (ℓ k c : ℕ) : ∀ R ∈ initT ℓ k c, ∃ i < k, R = trackOut ℓ (c + i * (4 * ℓ + 1)) := by
  induction k with
  | zero => simp [initT]
  | succ k ih =>
    intro R hR
    simp only [initT, List.mem_append, List.mem_singleton] at hR
    rcases hR with hR | rfl
    · obtain ⟨i, hi, e⟩ := ih R hR; exact ⟨i, by omega, e⟩
    · exact ⟨k, by omega, rfl⟩

theorem initP_sem (b ℓ o : ℕ) (Ki : ℕ → ℕ) (k c : ℕ) (Z : ℕ → Bool) (hob : o + b ≤ ℓ)
    (hx : ∀ i, i < k → ∀ a ∈ xLE b i, a < c) (hF : Fresh Z c) :
    (∀ w, w < c → evalP A O (initP b ℓ o Ki k c) Z w = Z w) ∧
    Fresh (evalP A O (initP b ℓ o Ki k c) Z) (c + k * (4 * ℓ + 1)) ∧
    ∀ i, i < k → valLE ((trackOut ℓ (c + i * (4 * ℓ + 1))).map
        (evalP A O (initP b ℓ o Ki k c) Z)) =
      (2 ^ o * valLE ((xLE b i).map Z) + Ki i % 2 ^ ℓ) % 2 ^ ℓ := by
  induction k with
  | zero => exact ⟨fun _ _ => rfl, by simpa [initP, evalP] using hF, fun i hi => by omega⟩
  | succ k ih =>
    obtain ⟨P1, P2, P3⟩ := ih (fun i hi => hx i (by omega))
    set Zk := evalP A O (initP b ℓ o Ki k c) Z
    obtain ⟨Q1, Q2, Q3⟩ := trackInit_sem A O b ℓ o Ki k (c + k * (4 * ℓ + 1)) Zk hob
      (fun a ha => by have := hx k (by omega) a ha; omega) P2
    have e : (k + 1) * (4 * ℓ + 1) = k * (4 * ℓ + 1) + (4 * ℓ + 1) := by ring
    simp only [initP, evalP_append]
    refine ⟨fun w hw => by rw [Q1 w (by omega), P1 w hw], fun w hw => Q2 w (by
      omega), fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [← P3 i h]
      congr 1
      apply List.map_congr_left
      intro w hw
      have := trackOut_bound ℓ _ w hw
      have : i * (4 * ℓ + 1) + (4 * ℓ + 1) ≤ k * (4 * ℓ + 1) := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h
      exact Q1 w (by omega)
    · subst h
      rw [Q3]
      have : (xLE b i).map Zk = (xLE b i).map Z :=
        List.map_congr_left (fun a ha => P1 a (hx i (by omega) a ha))
      rw [this]

theorem initP_good (S : ℕ → Prop) (b ℓ o : ℕ) (Ki : ℕ → ℕ) (k c : ℕ) (hob : o + b ≤ ℓ)
    (hx : ∀ i, i < k → ∀ a ∈ xLE b i, a < c ∧ S a) (hS : ∀ w, c ≤ w → S w) :
    ∀ I ∈ initP b ℓ o Ki k c, Good A S c (c + k * (4 * ℓ + 1)) I := by
  induction k with
  | zero => simp [initP]
  | succ k ih =>
    intro I hI
    have e : (k + 1) * (4 * ℓ + 1) = k * (4 * ℓ + 1) + (4 * ℓ + 1) := by ring
    simp only [initP, List.mem_append] at hI
    rcases hI with hI | hI
    · exact (ih (fun i hi => hx i (by omega)) I hI).mono le_rfl
        (by omega)
    · have := trackInit_good A S b ℓ o Ki k _ hob
        (fun a ha => by have := hx k (by omega) a ha; exact ⟨by omega, this.2⟩)
        (fun w hw => hS w (by omega)) I hI
      exact this.mono (by omega) (by omega)

theorem initP_noQ (b ℓ o : ℕ) (Ki : ℕ → ℕ) (k c : ℕ) :
    ∀ I ∈ initP b ℓ o Ki k c, I.isQ = false := by
  induction k with
  | zero => simp [initP]
  | succ k ih =>
    intro I hI
    simp only [initP, List.mem_append] at hI
    rcases hI with hI | hI
    · exact ih I hI
    · exact trackInit_noQ _ _ _ _ _ _ I hI

theorem initP_length (b ℓ o : ℕ) (Ki : ℕ → ℕ) (k c : ℕ) (hob : o + b ≤ ℓ) :
    (initP b ℓ o Ki k c).length ≤ k * (10 * ℓ) := by
  induction k with
  | zero => simp [initP]
  | succ k ih =>
    have := trackInit_length b ℓ o Ki k (c + k * (4 * ℓ + 1)) hob
    have e : (k + 1) * (10 * ℓ) = k * (10 * ℓ) + 10 * ℓ := by ring
    simp only [initP, List.length_append]; omega

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

end

end LTFA

-- ===== Q6.lean =====

namespace LTFA
open QAlgorithms QuantumLTF.Membership

noncomputable section

theorem regBasis_ext (n b Vb W : ℕ) (x : Fin n → Qubits b) (v : Qubits Vb) (Z : ℕ → Bool)
    (hx : ∀ (i : Fin n) (j : Fin b), Z (j + b * i) = x i j)
    (hv : ∀ m : Fin Vb, Z (n * b + m) = v m)
    (hw : ∀ w, n * b + Vb ≤ w → Z w = false) :
    toQ (n * b + Vb + W) Z = regBasis n b Vb W x v := by
  funext ⟨w, hw'⟩
  simp only [toQ, regBasis]
  by_cases h1 : w < n * b + Vb
  · have e : (⟨w, hw'⟩ : Fin (n * b + Vb + W)) = Fin.castAdd W ⟨w, h1⟩ := rfl
    rw [e, Fin.append_left]
    by_cases h2 : w < n * b
    · have e2 : (⟨w, h1⟩ : Fin (n * b + Vb)) = Fin.castAdd Vb ⟨w, h2⟩ := rfl
      rw [e2, Fin.append_left]
      simp only [flatReg]
      set k : Fin (n * b) := ⟨w, h2⟩
      have h3 := hx (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
      have e3 : ((finProdFinEquiv.symm k).2 : ℕ) + b * (finProdFinEquiv.symm k).1 = w := by
        have := congrArg Fin.val (finProdFinEquiv.apply_symm_apply k)
        simpa [finProdFinEquiv_apply_val] using this
      rw [← h3, e3]
    · have e2 : (⟨w, h1⟩ : Fin (n * b + Vb)) = Fin.natAdd (n * b) ⟨w - n * b, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e2, Fin.append_right, ← hv]
      congr 1; simp; omega
  · have e : (⟨w, hw'⟩ : Fin (n * b + Vb + W)) =
        Fin.natAdd (n * b + Vb) ⟨w - (n * b + Vb), by omega⟩ := Fin.ext (by simp; omega)
    rw [e, Fin.append_right]
    exact (hw w (by omega))

def Z0 (n b : ℕ) (x : Fin n → Qubits b) (w : ℕ) : Bool :=
  if h : w < n * b then
    x ⟨w / b, by
      have hb : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · subst h0; simp at h
        · exact h0
      exact (Nat.div_lt_iff_lt_mul hb).mpr h⟩ ⟨w % b, Nat.mod_lt _ (by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · subst h0; simp at h
      · exact h0)⟩
  else false

theorem Z0_x (n b : ℕ) (x : Fin n → Qubits b) (i : Fin n) (j : Fin b) :
    Z0 n b x (j + b * i) = x i j := by
  have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have h : (j : ℕ) + b * i < n * b := by
    have := i.isLt; have := j.isLt; nlinarith
  rw [Z0, dif_pos h]
  have e1 : ((j : ℕ) + b * i) / b = i := by
    rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have e2 : ((j : ℕ) + b * i) % b = j := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  congr 1
  · exact Fin.ext e1
  · exact Fin.ext e2

theorem Z0_ge (n b : ℕ) (x : Fin n → Qubits b) (w : ℕ) (hw : n * b ≤ w) : Z0 n b x w = false := by
  rw [Z0, dif_neg (by omega)]

theorem xLE_val (n b : ℕ) (x : Fin n → Qubits b) (i : Fin n) :
    valLE ((xLE b i).map (Z0 n b x)) = bitsToNat (x i) := by
  symm
  apply bitsToNat_eq_valLE
  · simp [xLE]
  · intro j
    have hj := j.isLt
    simp only [xLE, List.map_reverse, List.reverse_reverse, List.map_map]
    rw [List.getD_eq_getElem _ _ (by simp <;> omega)]
    simp only [List.getElem_map, List.getElem_range, Function.comp]
    exact (Z0_x n b x i j).symm

theorem xLE_lt (n b : ℕ) (i : ℕ) (hi : i < n) : ∀ a ∈ xLE b i, a < n * b := by
  intro a ha
  simp only [xLE, List.mem_reverse, List.mem_map, List.mem_range] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  have : i + 1 ≤ n := hi
  have : b * (i + 1) ≤ b * n := Nat.mul_le_mul_left _ this
  rw [Nat.mul_comm n b]; nlinarith

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

end

end LTFA

-- ===== Q7.lean =====

namespace LTFA
open QAlgorithms QuantumLTF.Membership

noncomputable section

structure Prm where
  n : ℕ
  b : ℕ
  q : ℕ
  r : ℕ
  fh : ℕ
  fp : ℕ
  Bh : ℕ
  Bp : ℕ
  kh : ℤ
  kp : ℕ → ℤ
  s1 : Bool

namespace Prm
variable (G : Prm)

def o' : ℕ := G.fh + G.fp + G.q + 2
def o : ℕ := G.o' + 1
def f : ℕ := G.r + G.b + G.o
def ℓ' : ℕ := G.f + G.Bh + G.Bp + 2
def ℓ : ℕ := G.ℓ' + 1
def T : ℕ := G.fh + G.q + 2
def Vb' : ℕ := G.T + G.Bh + 1
def Vb : ℕ := G.Vb' + 1
def nb : ℕ := G.n * G.b
def base : ℕ := G.nb + G.Vb
def Kint (i : ℕ) : ℤ := 2 ^ G.ℓ' + 2 ^ G.o' * (1 - 2 ^ G.b) + G.kh * G.kp i * 2 ^ (G.r + G.b + G.q + 3)
def Ki (i : ℕ) : ℕ := Kc (G.Kint i) G.ℓ
def KoutI : ℤ := 2 ^ G.Vb' + G.kh * 2 ^ (G.q + 2)
def Kout : ℕ := Kc G.KoutI G.Vb
def u (j : ℕ) : ℤ := if j < G.n then G.kp j * 2 ^ (G.r + G.b + G.fh + 1) else 2 ^ G.fh
def cA : ℕ := G.base + G.n * (4 * G.ℓ + 1)
def Ts0 : List (List ℕ) := initT G.ℓ G.n G.base ++ [List.range' G.cA G.Vb]
def c0 : ℕ := G.cA + G.Vb
def prog : List Ins :=
  initP G.b G.ℓ G.o G.Ki G.n G.base ++ fill (constSpecs G.Kout G.Vb) G.cA ++
    rP G.n G.ℓ G.s1 G.u G.q G.Ts0 G.c0
def cEnd : ℕ := rE G.n G.ℓ G.q G.Ts0 G.c0
def outR : List ℕ := (rT G.n G.ℓ G.q G.Ts0 G.c0).getD G.n []
def Pfull : List Ins := G.prog ++ copyOut G.outR G.nb G.Vb ++ G.prog.reverse
def W : ℕ := G.cEnd - G.base

def S (w : ℕ) : Prop := w < G.nb ∨ G.base ≤ w

theorem hob : G.o + G.b ≤ G.ℓ := by simp only [ℓ, ℓ', f]; omega

theorem Vb_le : G.Vb ≤ G.ℓ := by simp only [Vb, Vb', T, ℓ, ℓ', f, o, o']; omega

theorem Ts0_length : G.Ts0.length = G.n + 1 := by simp [Ts0, initT_length]

theorem Ts0_getD_lt (j : ℕ) (hj : j < G.n) :
    G.Ts0.getD j [] = trackOut G.ℓ (G.base + j * (4 * G.ℓ + 1)) := by
  rw [Ts0, List.getD_append _ _ _ _ (by rw [initT_length]; exact hj), initT_getD _ _ _ _ hj]

theorem Ts0_getD_n : G.Ts0.getD G.n [] = List.range' G.cA G.Vb := by
  rw [Ts0, List.getD_append_right _ _ _ _ (by rw [initT_length]), initT_length]; simp

theorem Ts0_take : G.Ts0.take G.n = initT G.ℓ G.n G.base := by
  rw [Ts0, List.take_append_of_le_length (by rw [initT_length]),
    List.take_of_length_le (by rw [initT_length])]

theorem Ts0_wires : ∀ R ∈ G.Ts0, ∀ a ∈ R, G.base ≤ a ∧ a < G.c0 := by
  intro R hR a ha
  simp only [Ts0, List.mem_append, List.mem_singleton] at hR
  rcases hR with hR | rfl
  · obtain ⟨i, hi, rfl⟩ := initT_mem _ _ _ R hR
    have := trackOut_bound _ _ a ha
    have : i * (4 * G.ℓ + 1) + (4 * G.ℓ + 1) ≤ G.n * (4 * G.ℓ + 1) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    simp only [c0, cA]; omega
  · simp [List.mem_range'] at ha; simp only [c0, cA] at *; omega

theorem Ts0_take_len : ∀ R ∈ G.Ts0.take G.n, R.length = G.ℓ := by
  rw [Ts0_take]
  intro R hR
  obtain ⟨i, _, rfl⟩ := initT_mem _ _ _ R hR
  exact trackOut_length _ _

theorem Ts0_len_le : ∀ R ∈ G.Ts0, R.length ≤ G.ℓ := by
  intro R hR
  simp only [Ts0, List.mem_append, List.mem_singleton] at hR
  rcases hR with hR | rfl
  · obtain ⟨i, _, rfl⟩ := initT_mem _ _ _ R hR
    rw [trackOut_length]
  · simp; exact G.Vb_le

theorem c0_le_cEnd : G.c0 ≤ G.cEnd := rE_ge _ _ _ _ _

theorem outR_length : G.outR.length = G.Vb := by
  rw [outR, rT_getD_length, Ts0_getD_n]; simp

theorem outR_wires : ∀ a ∈ G.outR, G.base ≤ a ∧ a < G.cEnd := by
  intro a ha
  have hmem : G.outR ∈ rT G.n G.ℓ G.q G.Ts0 G.c0 := by
    rw [outR, List.getD_eq_getElem _ _ (by rw [rT_length, Ts0_length]; omega)]
    exact List.getElem_mem _
  have := G.c0_le_cEnd
  rcases rT_bound G.n G.ℓ G.q G.Ts0 G.c0 G.outR hmem a ha with ⟨R0, h0, ha0⟩ | h
  · have := G.Ts0_wires R0 h0 a ha0
    simp only [cEnd] at *; omega
  · have : G.base ≤ G.c0 := by simp only [c0, cA]; omega
    simp only [cEnd] at *; omega

theorem prog_good (A : ℕ) (hA : A = G.n * G.ℓ) : ∀ I ∈ G.prog, Good A G.S G.base G.cEnd I := by
  subst hA
  have hc0 := G.c0_le_cEnd
  have hS : ∀ w, G.base ≤ w → G.S w := fun w h => Or.inr h
  intro I hI
  simp only [prog, List.mem_append] at hI
  rcases hI with (hI | hI) | hI
  · have := initP_good (G.n * G.ℓ) G.S G.b G.ℓ G.o G.Ki G.n G.base G.hob
      (fun i hi a ha => by
        have := xLE_lt G.n G.b i hi a ha
        exact ⟨by simp only [base, nb] at *; omega, Or.inl this⟩) hS I hI
    exact this.mono le_rfl (by simp only [c0, cA] at *; omega)
  · have := fill_good (G.n * G.ℓ) G.S (constSpecs G.Kout G.Vb) G.cA
      (fun sp hsp a ha => by rw [constSpecs_src _ _ sp hsp] at ha; simp at ha) I hI
    rw [constSpecs_length] at this
    exact this.mono (by simp only [cA]; omega) (by simp only [c0] at *; omega)
  · have := rP_good G.n G.ℓ G.s1 G.u G.S G.q G.Ts0 G.c0 G.Ts0_take_len
      (fun R h a ha => by
        have := G.Ts0_wires R h a ha
        exact ⟨this.2, hS a this.1⟩)
      (fun w hw => hS w (by simp only [c0, cA] at hw; omega)) I hI
    exact this.mono (by simp only [c0, cA]; omega) le_rfl

theorem prog_countQ : G.prog.countP Ins.isQ = G.q := by
  have h1 : (initP G.b G.ℓ G.o G.Ki G.n G.base).countP Ins.isQ = 0 :=
    List.countP_eq_zero.mpr (fun I hI => by simp [initP_noQ _ _ _ _ _ _ I hI])
  have h2 : (fill (constSpecs G.Kout G.Vb) G.cA).countP Ins.isQ = 0 :=
    List.countP_eq_zero.mpr (fun I hI => by simp [fill_noQ _ _ I hI])
  simp only [prog, List.countP_append, h1, h2, rP_countQ]; omega

theorem Pfull_countQ : G.Pfull.countP Ins.isQ = 2 * G.q := by
  have h3 : (copyOut G.outR G.nb G.Vb).countP Ins.isQ = 0 :=
    List.countP_eq_zero.mpr (fun I hI => by simp [copyOut_noQ _ _ _ I hI])
  simp only [Pfull, List.countP_append, List.countP_reverse, h3, prog_countQ]; omega

theorem Pfull_length (hn : 2 ≤ G.n) : G.Pfull.length ≤ 30 * G.n * G.ℓ * (G.q + 1) := by
  have h1 := initP_length G.b G.ℓ G.o G.Ki G.n G.base G.hob
  have h2 := fill_length (constSpecs G.Kout G.Vb) G.cA
  rw [constSpecs_length] at h2
  have h3 := rP_length G.n G.ℓ G.s1 G.u G.ℓ G.q G.Ts0 G.c0 G.Ts0_take_len G.Ts0_len_le
  rw [Ts0_length] at h3
  have hV := G.Vb_le
  have hl : 1 ≤ G.ℓ := by simp [ℓ]
  have hP : G.prog.length ≤ G.n * (10 * G.ℓ) + 2 * G.Vb +
      G.q * (2 * G.ℓ * G.n + 2 + 8 * G.ℓ * (G.n + 1)) := by
    simp only [prog, List.length_append]; omega
  simp only [Pfull, List.length_append, List.length_reverse, copyOut_length]
  have e1 : G.q * (2 * G.ℓ * G.n + 2 + 8 * G.ℓ * (G.n + 1)) ≤ G.q * (15 * G.n * G.ℓ) := by
    apply Nat.mul_le_mul_left
    nlinarith
  have e2 : G.n * (10 * G.ℓ) + 2 * G.Vb ≤ 11 * G.n * G.ℓ := by nlinarith
  nlinarith

end Prm

end

end LTFA

-- ===== Q8.lean =====

namespace LTFA
open QAlgorithms QuantumLTF.Membership

noncomputable section

namespace Prm
variable (G : Prm)

def Oc (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) : Qubits (G.n * G.ℓ) → Bool :=
  fun y => decide (ltf w θ (addrOf G.n G.ℓ G.f y) = -1)

def Z1 (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) (x : Fin G.n → Qubits G.b) : ℕ → Bool :=
  evalP (G.n * G.ℓ) (G.Oc w θ) G.prog (Z0 G.n G.b x)

def Htil (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) (x : Fin G.n → Qubits G.b) : Qubits G.Vb :=
  fun m => G.Z1 w θ x (G.outR.reverse.getD m 0)

structure Hyp (p : EuclideanSpace ℝ (Fin G.n)) (htil : ℝ) (s : ℤ) : Prop where
  hs1 : G.s1 = decide (s = 1)
  hp : ∀ i : Fin G.n, p i = (G.kp i : ℝ) / 2 ^ G.fp
  hkp : ∀ i : Fin G.n, |(G.kp i : ℝ)| < 2 ^ G.Bp
  hh : htil = (G.kh : ℝ) / 2 ^ G.fh
  hkh : |(G.kh : ℝ)| < 2 ^ G.Bh
  hfh : G.fh ≤ G.Bh
  hfp : G.fp ≤ G.Bp
  hr : rho G.n = (2 : ℝ)⁻¹ ^ G.r

theorem sem_val (p : EuclideanSpace ℝ (Fin G.n)) (htil : ℝ) (s : ℤ) (H : G.Hyp p htil s)
    (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) (x : Fin G.n → Qubits G.b) :
    (valLE (G.outR.map (G.Z1 w θ x)) : ℝ) = 2 ^ G.Vb / 2 + 2 ^ G.T *
      (affineBoundaryBisect p (rho G.n • gridVec G.n G.b x) s G.q (htil - 1 / 4)
        (htil + 1 / 4)).run (ltf w θ) ∧
    ∀ v, v < G.base → G.Z1 w θ x v = Z0 G.n G.b x v := by
  set x' := rho G.n • gridVec G.n G.b x with hx'
  have hx'i : ∀ i : Fin G.n, x' i = (2 : ℝ)⁻¹ ^ G.r * gridPoint G.b (x i) := by
    intro i; simp [hx', gridVec, H.hr]
  set A := G.n * G.ℓ
  set O := G.Oc w θ
  -- bounds
  have hpi : ∀ i : Fin G.n, |p i| < 2 ^ G.Bp := by
    intro i
    rw [H.hp i, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ G.fp)]
    have h1 : (1 : ℝ) ≤ 2 ^ G.fp := one_le_pow₀ (by norm_num)
    calc |(G.kp i : ℝ)| / 2 ^ G.fp ≤ |(G.kp i : ℝ)| := div_le_self (abs_nonneg _) h1
      _ < 2 ^ G.Bp := H.hkp i
  have hht : |htil| < 2 ^ G.Bh := by
    rw [H.hh, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ G.fh)]
    have h1 : (1 : ℝ) ≤ 2 ^ G.fh := one_le_pow₀ (by norm_num)
    calc |(G.kh : ℝ)| / 2 ^ G.fh ≤ |(G.kh : ℝ)| := div_le_self (abs_nonneg _) h1
      _ < 2 ^ G.Bh := H.hkh
  -- track data
  let len : ℕ → ℕ := fun j => if j < G.n then G.ℓ else G.Vb
  let fr : ℕ → ℕ := fun j => if j < G.n then G.f else G.T
  let val : ℕ → ℝ → ℝ := fun j mid => if h : j < G.n then x' ⟨j, h⟩ + mid * p ⟨j, h⟩ else mid
  let slope : ℕ → ℝ := fun j => if h : j < G.n then p ⟨j, h⟩ else 1
  have hrange : ∀ j, j < G.n + 1 → ∀ mid, htil - 1 / 4 ≤ mid → mid ≤ htil + 1 / 4 →
      |2 ^ (fr j) * val j mid| < 2 ^ (len j) / 2 := by
    intro j hj mid h1 h2
    have hmid : |mid| ≤ 2 ^ G.Bh + 1 / 4 := by
      rw [abs_le]; constructor <;> [have := neg_abs_le htil; have := le_abs_self htil] <;>
        linarith
    by_cases h : j < G.n
    · simp only [fr, len, val, h, if_true, dif_pos h]
      have hxj : |x' ⟨j, h⟩| ≤ 1 / 2 := by rw [hx'i]; exact abs_rho_grid_le _ _ _
      have hpj := hpi ⟨j, h⟩
      have hB : (1 : ℝ) ≤ 2 ^ G.Bh := one_le_pow₀ (by norm_num)
      have hB' : (1 : ℝ) ≤ 2 ^ G.Bp := one_le_pow₀ (by norm_num)
      have hsum : |x' ⟨j, h⟩ + mid * p ⟨j, h⟩| < 2 ^ G.Bh * 2 ^ G.Bp * 4 := by
        calc |x' ⟨j, h⟩ + mid * p ⟨j, h⟩| ≤ |x' ⟨j, h⟩| + |mid| * |p ⟨j, h⟩| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ 1 / 2 + (2 ^ G.Bh + 1 / 4) * 2 ^ G.Bp := by
              gcongr
          _ < 2 ^ G.Bh * 2 ^ G.Bp * 4 := by nlinarith
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ G.f)]
      have e : (2 : ℝ) ^ G.ℓ / 2 = 2 ^ G.f * (2 ^ G.Bh * 2 ^ G.Bp * 4) := by
        simp only [ℓ, ℓ', pow_succ, pow_add]; ring
      rw [e]
      exact mul_lt_mul_of_pos_left hsum (by positivity)
    · simp only [fr, len, val, h, if_false, dif_neg h, not_false_eq_true]
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ G.T)]
      have hB : (1 : ℝ) ≤ 2 ^ G.Bh := one_le_pow₀ (by norm_num)
      have e : (2 : ℝ) ^ G.Vb / 2 = 2 ^ G.T * (2 ^ G.Bh * 2) := by
        simp only [Vb, Vb', pow_succ, pow_add]; ring
      rw [e]
      exact mul_lt_mul_of_pos_left (by linarith) (by positivity)
  -- initial state
  set Z00 := Z0 G.n G.b x
  have hF0 : Fresh Z00 G.base := fun w hw => Z0_ge _ _ _ _ (by simp only [base, nb] at hw; omega)
  obtain ⟨I1, I2, I3⟩ := initP_sem A O G.b G.ℓ G.o G.Ki G.n G.base Z00 G.hob
    (fun i hi a ha => by have := xLE_lt G.n G.b i hi a ha; simp only [base, nb] at *; omega) hF0
  set ZA := evalP A O (initP G.b G.ℓ G.o G.Ki G.n G.base) Z00
  have I2' : Fresh ZA G.cA := I2
  obtain ⟨J1, J2, _⟩ := fill_sem A O (constSpecs G.Kout G.Vb) G.cA ZA I2'
    (fun sp hsp a ha => by rw [constSpecs_src _ _ sp hsp] at ha; simp at ha)
  have Jm := fill_map A O (constSpecs G.Kout G.Vb) G.cA ZA I2'
    (fun sp hsp a ha => by rw [constSpecs_src _ _ sp hsp] at ha; simp at ha)
  rw [constSpecs_length] at J2 Jm
  set ZB := evalP A O (fill (constSpecs G.Kout G.Vb) G.cA) ZA
  have hL : (1 / 2 : ℝ) = 2 ^ G.q / 2 ^ (G.q + 1) := by rw [pow_succ]; field_simp
  have hlomid : htil - 1 / 4 + 1 / 2 / 2 = htil := by ring
  obtain ⟨R1, _, R3⟩ := rP_sem G.n G.ℓ G.s1 G.u G.f G.q s p x' (ltf w θ) (ltf_pm w θ) H.hs1
    htil len fr val slope
    (fun j hj => by simp [len, hj]) (fun j hj => by simp [fr, hj])
    (fun j hj mid => by simp [val, hj])
    (fun j hj mid δ => by
      by_cases h : j < G.n
      · simp only [val, slope, dif_pos h]; ring
      · simp only [val, slope, dif_neg h]; ring)
    (fun j hj => by
      by_cases h : j < G.n
      · simp only [u, fr, slope, if_pos h, dif_pos h, H.hp ⟨j, h⟩]
        simp only [f, o, o', pow_add, pow_succ]
        push_cast
        field_simp
        try ring
      · simp only [u, fr, slope, if_neg h, dif_neg h, T, pow_add]
        push_cast
        field_simp)
    hrange G.q le_rfl (htil - 1 / 4) (1 / 2) G.Ts0 G.c0 ZB hL (by linarith) (by linarith)
    G.Ts0_length
    (by
      intro j hj
      rw [hlomid]
      by_cases h : j < G.n
      · rw [G.Ts0_getD_lt j h]
        refine ⟨by simp [len, h, trackOut_length], ?_⟩
        have hmap : (trackOut G.ℓ (G.base + j * (4 * G.ℓ + 1))).map ZB =
            (trackOut G.ℓ (G.base + j * (4 * G.ℓ + 1))).map ZA := by
          apply List.map_congr_left
          intro a ha
          have := trackOut_bound _ _ a ha
          have : j * (4 * G.ℓ + 1) + (4 * G.ℓ + 1) ≤ G.n * (4 * G.ℓ + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h
          exact J1 a (by simp only [cA]; omega)
        rw [hmap, I3 j h, xLE_val G.n G.b x ⟨j, h⟩, Nat.add_mod_mod]
        simp only [len, fr, val, h, if_true, dif_pos h]
        apply track_step
        · rw [hx'i, H.hp, H.hh]
          have hg := gridPoint_scaled G.b G.r G.o' (x ⟨j, h⟩)
          simp only [Kint, Ki, if_pos h]
          have ef : (2 : ℝ) ^ G.f = 2 ^ (G.r + G.b + (G.o' + 1)) := rfl
          rw [ef, mul_add, hg]
          simp only [ℓ, ℓ', f, o, o', pow_add, pow_succ]
          push_cast
          field_simp
          ring
        · have := hrange j hj htil (by linarith) (by linarith)
          simp only [len, fr, val, h, if_true, dif_pos h] at this
          have := (abs_lt.mp this).1; linarith
        · have := hrange j hj htil (by linarith) (by linarith)
          simp only [len, fr, val, h, if_true, dif_pos h] at this
          have := (abs_lt.mp this).2; linarith
      · have hjn : j = G.n := by omega
        subst hjn
        rw [G.Ts0_getD_n]
        refine ⟨by simp [len], ?_⟩
        rw [Jm, constSpecs_val]
        simp only [len, fr, val, lt_irrefl, if_false, dif_neg (lt_irrefl _)]
        rw [show G.Kout % 2 ^ G.Vb = (0 + Kc G.KoutI G.Vb) % 2 ^ G.Vb by simp [Kout]]
        apply track_step
        · rw [H.hh]
          simp only [KoutI, Vb, Vb', T, pow_add, pow_succ]
          push_cast
          field_simp
          ring
        · have := hrange G.n hj htil (by linarith) (by linarith)
          simp only [len, fr, val, lt_irrefl, if_false, dif_neg (lt_irrefl _)] at this
          have := (abs_lt.mp this).1; linarith
        · have := hrange G.n hj htil (by linarith) (by linarith)
          simp only [len, fr, val, lt_irrefl, if_false, dif_neg (lt_irrefl _)] at this
          have := (abs_lt.mp this).2; linarith)
    (fun R h a ha => (G.Ts0_wires R h a ha).2) J2
  have hZ1 : G.Z1 w θ x = evalP A O (rP G.n G.ℓ G.s1 G.u G.q G.Ts0 G.c0) ZB := by
    simp only [Z1, prog, evalP_append]; rfl
  have hhi : htil - 1 / 4 + 1 / 2 = htil + 1 / 4 := by ring
  constructor
  · have := R3 G.n (by omega)
    rw [hhi] at this
    simp only [len, fr, val, lt_irrefl, if_false, dif_neg (lt_irrefl _)] at this
    rw [outR, hZ1]
    exact this
  · intro v hv
    rw [hZ1]
    exact (R1 v (by simp only [c0, cA]; omega)).trans ((J1 v (by simp only [cA]; omega)).trans
      (I1 v hv))

end Prm

end

end LTFA

-- ===== Q9.lean =====

namespace LTFA
open QAlgorithms QuantumLTF.Membership

noncomputable section

theorem Good.WF {A : ℕ} {S : ℕ → Prop} {lo hi : ℕ} {I : Ins} (h : Good A S lo hi I) (N : ℕ)
    (hN : hi ≤ N) : I.WF N A :=
  ⟨by have := h.2.1; omega, fun s hs => by have := (h.2.2 s hs).1; have := h.2.1; omega⟩

namespace Prm
variable (G : Prm)

theorem sem_circuit (p : EuclideanSpace ℝ (Fin G.n)) (htil : ℝ) (s : ℤ) (H : G.Hyp p htil s)
    (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) (x : Fin G.n → Qubits G.b) :
    act ((toCP (G.n * G.b + G.Vb + G.W) (G.n * G.ℓ) G.Pfull).unitary
        (fun _ => memOracle G.n G.ℓ G.f w θ))
      (ket (regBasis G.n G.b G.Vb G.W x fun _ => false)) =
    ket (regBasis G.n G.b G.Vb G.W x (G.Htil w θ x)) := by
  have hc0 := G.c0_le_cEnd
  have hN : G.n * G.b + G.Vb + G.W = G.cEnd := by
    simp only [W, base, nb, c0, cA] at *; omega
  set N := G.n * G.b + G.Vb + G.W
  set A := G.n * G.ℓ
  set O := G.Oc w θ
  have hgood := G.prog_good A rfl
  have hZ0 : toQ N (Z0 G.n G.b x) = regBasis G.n G.b G.Vb G.W x (fun _ => false) :=
    regBasis_ext _ _ _ _ _ _ _ (Z0_x _ _ x) (fun m => Z0_ge _ _ _ _ (by omega))
      (fun w hw => Z0_ge _ _ _ _ (by omega))
  have hbase : G.base = G.n * G.b + G.Vb := rfl
  have hwf : ∀ I ∈ G.Pfull, I.WF N A := by
    intro I hI
    simp only [Pfull, List.mem_append, List.mem_reverse] at hI
    rcases hI with (hI | hI) | hI
    · exact (hgood I hI).WF N (by omega)
    · simp only [copyOut, List.mem_map, List.mem_range] at hI
      obtain ⟨m, hm, rfl⟩ := hI
      have hm' : m < G.outR.reverse.length := by simp [outR_length, hm]
      have hmem : G.outR.reverse.getD m 0 ∈ G.outR := by
        rw [List.getD_eq_getElem _ _ hm']; exact List.mem_reverse.mp (List.getElem_mem _)
      have := G.outR_wires _ hmem
      refine ⟨by simp only [Ins.tgt, nb] at *; omega, fun s hs => ?_⟩
      simp only [Ins.src, Ins.tgt] at hs ⊢
      subst hs
      constructor
      · omega
      · simp only [nb] at *; omega
    · exact (hgood I hI).WF N (by omega)
  rw [← hZ0, act_toCP N A O _ (memOracle_eq G.n G.ℓ G.f w θ) G.Pfull hwf]
  congr 1
  -- classical reasoning
  obtain ⟨_, hpres⟩ := G.sem_val p htil s H w θ x
  set Z00 := Z0 G.n G.b x
  set Z1 := evalP A O G.prog Z00 with hZ1
  have hZ1' : Z1 = G.Z1 w θ x := rfl
  set Z2 := evalP A O (copyOut G.outR G.nb G.Vb) Z1 with hZ2
  have hcopy := copyOut_sem A O G.outR G.nb G.base (fun a ha => (G.outR_wires a ha).1) Z1 G.Vb
    (by rw [outR_length]) (by simp [hbase, nb]) (fun m hm => by
      rw [hZ1', hpres _ (by simp only [hbase, nb]; omega)]; exact Z0_ge _ _ _ _ (by simp [nb]))
  let V : ℕ → Prop := fun w => G.nb ≤ w ∧ w < G.base
  have hP : ∀ I ∈ G.prog.reverse, ¬ V (I.tgt A) ∧ ∀ s, I.src A s → ¬ V s := by
    intro I hI
    have hg := hgood I (List.mem_reverse.mp hI)
    refine ⟨fun h => by have := hg.1; simp only [V] at h; omega, fun s hs h => ?_⟩
    have := (hg.2.2 s hs).2
    simp only [V, S] at h this; omega
  obtain ⟨Fr1, Fr2⟩ := evalP_frame A O V G.prog.reverse hP Z2 Z1 (fun w hw => by
    rw [hZ2, hcopy w, if_neg]
    simp only [V, hbase, nb] at hw ⊢; omega)
  have hrev := evalP_reverse A O G.prog (fun I hI h => by
    have := ((hgood I hI).2.2 _ h).1; omega) Z00
  have hfull : evalP A O G.Pfull Z00 = evalP A O G.prog.reverse Z2 := by
    simp only [Pfull, evalP_append]; rfl
  rw [hfull]
  apply regBasis_ext
  · intro i j
    have hlt : (j : ℕ) + G.b * i < G.nb := by
      have := xLE_lt G.n G.b i i.isLt ((j : ℕ) + G.b * i) (by
        simp only [xLE, List.mem_reverse, List.mem_map, List.mem_range]
        exact ⟨j, j.isLt, rfl⟩)
      simpa [nb] using this
    rw [Fr1 _ (by simp only [V]; omega), hrev]
    exact Z0_x _ _ x i j
  · intro m
    have hV : V (G.n * G.b + m) := by simp only [V, hbase, nb]; omega
    rw [Fr2 _ hV, hZ2, hcopy, if_pos (by simp only [nb]; omega)]
    simp only [Htil, nb, Nat.add_sub_cancel_left]
    rfl
  · intro w hw
    rw [Fr1 _ (by simp only [V, hbase, nb]; omega), hrev]
    exact Z0_ge _ _ _ _ (by omega)

theorem sem_fp (p : EuclideanSpace ℝ (Fin G.n)) (htil : ℝ) (s : ℤ) (H : G.Hyp p htil s)
    (w : EuclideanSpace ℝ (Fin G.n)) (θ : ℝ) (x : Fin G.n → Qubits G.b) :
    fpVal G.Vb G.T (G.Htil w θ x) =
      (affineBoundaryBisect p (rho G.n • gridVec G.n G.b x) s G.q (htil - 1 / 4)
        (htil + 1 / 4)).run (ltf w θ) := by
  obtain ⟨hv, _⟩ := G.sem_val p htil s H w θ x
  have hb : bitsToNat (G.Htil w θ x) = valLE (G.outR.map (G.Z1 w θ x)) := by
    apply bitsToNat_eq_valLE
    · simp [outR_length]
    · intro i
      have h1 : (i : ℕ) < G.outR.reverse.length := by simp [outR_length]
      have h2 : (i : ℕ) < (G.outR.map (G.Z1 w θ x)).reverse.length := by simp [outR_length]
      rw [List.getD_eq_getElem _ _ h2]
      simp only [Htil]
      rw [List.getD_eq_getElem _ _ h1]
      simp
  simp only [fpVal, hb, hv]
  field_simp
  ring

end Prm

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

theorem main_thm (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (b q : ℕ) (p : EuclideanSpace ℝ (Fin n)) (Bp fp : ℕ), (Bp : ℝ) ≤ C₁ * Real.log n →
        (∀ i, IsFp Bp fp (p i)) →
      ∀ (s : ℤ) (htil : ℝ) (Bh fh : ℕ), (Bh : ℝ) ≤ C₂ * Real.log (1 / ε) → IsFp Bh fh htil →
        ∃ (ℓ f Vb Vf W : ℕ)
          (c : OracleCircuit gatesRev (fun _ : Fin 1 => n * ℓ + 1) (n * b + Vb + W)),
          Uncontrolled c ∧
          c.queryCount 0 ≤ 2 * q ∧
          (c.gateCount : ℝ) ≤ C * n * (b + Real.log n + Real.log (1 / ε) + q) ^ 2 * (q + 1) ∧
          (Vb : ℝ) ≤ C * (Real.log (1 / ε) + q + 1) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 → s = sgn (inner ℝ w p) →
            |htil - height w θ p 0| ≤ ε / 100 →
            ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, act (c.unitary fun _ => memOracle n ℓ f w θ)
                  (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) ∧
              ∀ x, fpVal Vb Vf (Htil x) =
                (affineBoundaryBisect p (rho n • gridVec n b x) s q
                  (htil - 1 / 4) (htil + 1 / 4)).run (ltf w θ) := by
  set K : ℝ := 31 + 2 * C₁ + 2 * C₂ with hK
  have hK1 : 31 ≤ K := by rw [hK]; linarith
  refine ⟨60 * K + 2 * C₂ + 4, by positivity, ?_⟩
  intro n hn ε hε hε2 b q p Bp fp hBp hp s htil Bh fh hBh hh
  obtain ⟨hfh, kh, hkh1, hkh2⟩ := hh
  choose hfpB kp hkp1 hkp2 using hp
  have hfp : fp ≤ Bp := hfpB ⟨0, by omega⟩
  let kp' : ℕ → ℤ := fun i => if h : i < n then kp ⟨i, h⟩ else 0
  let G : Prm := ⟨n, b, q, ⌈Real.logb 2 (40 * Real.sqrt n)⌉₊, fh, fp, Bh, Bp, kh, kp',
    decide (s = 1)⟩
  have H : G.Hyp p htil s :=
    { hs1 := rfl
      hp := fun i => by
        have : kp' i = kp i := by
          show (if h : (i : ℕ) < n then kp ⟨i, h⟩ else 0) = kp i
          rw [dif_pos i.isLt]
        show p i = ((kp' i : ℤ) : ℝ) / 2 ^ fp
        rw [this]; exact hkp2 i
      hkp := fun i => by
        have : kp' i = kp i := by
          show (if h : (i : ℕ) < n then kp ⟨i, h⟩ else 0) = kp i
          rw [dif_pos i.isLt]
        show |((kp' i : ℤ) : ℝ)| < 2 ^ Bp
        rw [this, ← Int.cast_abs]
        exact_mod_cast hkp1 i
      hh := hkh2
      hkh := by
        show |((kh : ℤ) : ℝ)| < 2 ^ Bh
        rw [← Int.cast_abs]; exact_mod_cast hkh1
      hfh := hfh
      hfp := hfp
      hr := rfl }
  -- real bounds
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogn : 1 / 2 ≤ Real.log n := le_trans hl2 (Real.log_le_log (by norm_num) hn1)
  have hlogε : 0 ≤ Real.log (1 / ε) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hε]; linarith
  have hr := rceil_bound n (by omega)
  have hℓN : G.ℓ ≤ G.r + b + q + 2 * Bh + 2 * Bp + 6 := by
    simp only [Prm.ℓ, Prm.ℓ', Prm.f, Prm.o, Prm.o', G]; omega
  set X : ℝ := b + Real.log n + Real.log (1 / ε) + q with hX
  have hX2 : 1 / 2 ≤ X := by
    have : (0 : ℝ) ≤ b := by positivity
    have : (0 : ℝ) ≤ q := by positivity
    linarith
  have hℓX : (G.ℓ : ℝ) ≤ K * X := by
    have h1 : (G.ℓ : ℝ) ≤ G.r + b + q + 2 * Bh + 2 * Bp + 6 := by exact_mod_cast hℓN
    have h2 : (G.r : ℝ) ≤ 9 + Real.log n := hr
    have hb0 : (0 : ℝ) ≤ b := by positivity
    have hq0 : (0 : ℝ) ≤ q := by positivity
    rw [hX, hK]
    nlinarith
  refine ⟨G.ℓ, G.f, G.Vb, G.T, G.W, toCP (n * b + G.Vb + G.W) (n * G.ℓ) G.Pfull,
    uncontrolled_toCP _ _ _, ?_, ?_, ?_, ?_⟩
  · have := queryCount_toCP (n * b + G.Vb + G.W) (n * G.ℓ) G.Pfull
    rw [G.Pfull_countQ] at this
    exact this
  · have h1 := gateCount_toCP (n * b + G.Vb + G.W) (n * G.ℓ) G.Pfull
    have h2 := G.Pfull_length hn
    have h3 : ((toCP (n * b + G.Vb + G.W) (n * G.ℓ) G.Pfull).gateCount : ℝ) ≤
        30 * n * G.ℓ * (q + 1) := by
      have := le_trans h1 h2
      exact_mod_cast this
    refine le_trans h3 ?_
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hq1 : (0 : ℝ) ≤ q + 1 := by positivity
    have hXX : X ≤ 2 * X ^ 2 := by nlinarith
    have hK0 : 0 ≤ K := by linarith
    calc (30 : ℝ) * n * G.ℓ * (q + 1) ≤ 30 * n * (K * X) * (q + 1) := by gcongr
      _ ≤ 30 * n * (K * (2 * X ^ 2)) * (q + 1) := by gcongr
      _ = 60 * K * n * X ^ 2 * (q + 1) := by ring
      _ ≤ (60 * K + 2 * C₂ + 4) * n * X ^ 2 * (q + 1) := by
          have : 0 ≤ (2 * C₂ + 4) * n * X ^ 2 * (q + 1) := by positivity
          nlinarith
  · have hV : G.Vb ≤ 2 * Bh + q + 4 := by
      simp only [Prm.Vb, Prm.Vb', Prm.T, G]; omega
    have hV' : (G.Vb : ℝ) ≤ 2 * Bh + q + 4 := by exact_mod_cast hV
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hK0 : 0 ≤ K := by linarith
    have : (G.Vb : ℝ) ≤ (2 * C₂ + 4) * (Real.log (1 / ε) + q + 1) := by nlinarith
    have : (2 * C₂ + 4) * (Real.log (1 / ε) + q + 1) ≤
        (60 * K + 2 * C₂ + 4) * (Real.log (1 / ε) + q + 1) := by
      have : 0 ≤ Real.log (1 / ε) + q + 1 := by positivity
      nlinarith
    linarith
  · intro w θ _ _ _ _ _
    exact ⟨G.Htil w θ, fun x => G.sem_circuit p htil s H w θ x,
      fun x => G.sem_fp p htil s H w θ x⟩

end

end LTFA

open QAlgorithms QuantumLTF.Membership

theorem solution (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (b q : ℕ) (p : EuclideanSpace ℝ (Fin n)) (Bp fp : ℕ), (Bp : ℝ) ≤ C₁ * Real.log n →
        (∀ i, IsFp Bp fp (p i)) →
      ∀ (s : ℤ) (htil : ℝ) (Bh fh : ℕ), (Bh : ℝ) ≤ C₂ * Real.log (1 / ε) → IsFp Bh fh htil →
        ∃ (ℓ f Vb Vf W : ℕ)
          (c : OracleCircuit gatesRev (fun _ : Fin 1 => n * ℓ + 1) (n * b + Vb + W)),
          Uncontrolled c ∧
          c.queryCount 0 ≤ 2 * q ∧
          (c.gateCount : ℝ) ≤ C * n * (b + Real.log n + Real.log (1 / ε) + q) ^ 2 * (q + 1) ∧
          (Vb : ℝ) ≤ C * (Real.log (1 / ε) + q + 1) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 → s = sgn (inner ℝ w p) →
            |htil - height w θ p 0| ≤ ε / 100 →
            ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, act (c.unitary fun _ => memOracle n ℓ f w θ)
                  (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) ∧
              ∀ x, fpVal Vb Vf (Htil x) =
                (affineBoundaryBisect p (rho n • gridVec n b x) s q
                  (htil - 1 / 4) (htil + 1 / 4)).run (ltf w θ) :=
  LTFA.main_thm C₁ C₂ hC₁ hC₂

