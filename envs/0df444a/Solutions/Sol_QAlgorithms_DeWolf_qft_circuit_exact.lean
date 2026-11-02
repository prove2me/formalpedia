-- Prove2me | solution 1 for QAlgorithms.DeWolf.qft_circuit_exact
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:20:32.472714+00:00
-- url     : https://prove2.me/submissions/574f267d-70e8-417a-81da-58cae2f35605

import Definitions.Def_QAlgorithms_Defs_Fourier
set_option autoImplicit false

open QAlgorithms
open scoped Matrix BigOperators

namespace SolQFTCircuitExact

/-- The single wire `q` as an embedding `Fin 1 ↪ Fin n`. -/
def wire1 {n : ℕ} (q : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => q, fun a b _ => Subsingleton.elim a b⟩

/-- The wires `(c, t)`, `c ≠ t`, as an embedding `Fin 2 ↪ Fin n`. -/
def wire2 {n : ℕ} (c t : Fin n) (hct : c ≠ t) : Fin 2 ↪ Fin n :=
  ⟨Fin.cons c fun _ : Fin 1 => t,
    Fin.cons_injective_iff.2 ⟨by rintro ⟨_, h⟩; exact hct h.symm,
      fun a b _ => Subsingleton.elim a b⟩⟩

@[simp]
lemma init_snoc_qubits {n : ℕ} (u : Qubits n) (b : Bool) :
    Fin.init (Fin.snoc u b : Qubits (n + 1)) = u := by
  simp

@[simp]
lemma snoc_last_qubits {n : ℕ} (u : Qubits n) (b : Bool) :
    (Fin.snoc u b : Qubits (n + 1)) (Fin.last n) = b := by
  simp

@[simp]
lemma snoc_castSucc_qubits {n : ℕ} (u : Qubits n) (b : Bool) (i : Fin n) :
    (Fin.snoc u b : Qubits (n + 1)) (Fin.castSucc i) = u i := by
  simp

/-- Embed a circuit on `n` wires into `n + 1` wires on the first `n` wires `Fin.castSuccEmb`. -/
def liftGateApp {S : Set Gate} {n : ℕ} (g : GateApp S n) : GateApp S (n + 1) :=
  ⟨g.gate, g.mem, g.wires.trans Fin.castSuccEmb⟩

def liftCircuit {S : Set Gate} {n : ℕ} (c : Circuit S n) : Circuit S (n + 1) :=
  c.map liftGateApp

@[simp]
lemma liftCircuit_size {S : Set Gate} {n : ℕ} (c : Circuit S n) :
    Circuit.size (liftCircuit c) = Circuit.size c := by
  simp [Circuit.size, liftCircuit]

/-- Block-diagonal extension of an `n`-qubit operator to `n + 1` qubits acting on `Fin.init`. -/
def liftInit {n : ℕ} (A : Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ :=
  Matrix.of fun y z =>
    if y (Fin.last n) = z (Fin.last n) then A (Fin.init y) (Fin.init z) else 0

@[simp]
lemma liftInit_apply {n : ℕ} (A : Matrix (Qubits n) (Qubits n) ℂ) (y z : Qubits (n + 1)) :
    liftInit A y z = if y (Fin.last n) = z (Fin.last n) then A (Fin.init y) (Fin.init z) else 0 :=
  rfl

lemma eq_iff_init_eq_and_last_eq {n : ℕ} (y z : Qubits (n + 1)) :
    y = z ↔ Fin.init y = Fin.init z ∧ y (Fin.last n) = z (Fin.last n) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext i
    refine Fin.lastCases h2 (fun j => ?_) i
    exact congrFun h1 j

lemma liftInit_one (n : ℕ) : liftInit (1 : Matrix (Qubits n) (Qubits n) ℂ) = 1 := by
  ext y z
  simp only [liftInit_apply, Matrix.one_apply]
  by_cases hlast : y (Fin.last n) = z (Fin.last n)
  · rw [if_pos hlast]
    by_cases hinit : Fin.init y = Fin.init z
    · have hyz : y = z := (eq_iff_init_eq_and_last_eq y z).2 ⟨hinit, hlast⟩
      simp [hyz]
    · have hyz : y ≠ z := fun h => hinit (congrArg Fin.init h)
      simp [hinit, hyz]
  · have hyz : y ≠ z := fun h => hlast (congrFun h (Fin.last n))
    simp [hlast, hyz]

lemma liftInit_mul {n : ℕ} (A B : Matrix (Qubits n) (Qubits n) ℂ) :
    liftInit (A * B) = liftInit A * liftInit B := by
  ext y z
  simp only [liftInit_apply, Matrix.mul_apply]
  let e : Qubits n × Bool ≃ Qubits (n + 1) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun x => (Fin.init x, x (Fin.last n))
      left_inv := fun p => by ext <;> simp
      right_inv := fun x => Fin.snoc_init_self x }
  rw [← Equiv.sum_comp e]
  simp only [e, Equiv.coe_fn_mk, init_snoc_qubits, snoc_last_qubits, Fintype.sum_prod_type]
  by_cases hlast : y (Fin.last n) = z (Fin.last n)
  · rw [if_pos hlast]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_eq_single (y (Fin.last n))]
    · simp [hlast]
    · intro b hb
      rw [if_neg (Ne.symm hb), zero_mul]
  · rw [if_neg hlast]
    symm
    refine Finset.sum_eq_zero fun x _ => ?_
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : y (Fin.last n) = b
    · subst hb
      rw [if_neg hlast, mul_zero]
    · rw [if_neg hb, zero_mul]

lemma embedOp_trans_castSuccEmb {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin n) :
    embedOp M (w.trans Fin.castSuccEmb) = liftInit (embedOp M w) := by
  ext y z
  simp only [embedOp, liftInit_apply, Matrix.of_apply]
  have hcomp : ∀ x : Qubits (n + 1), x ∘ w.trans Fin.castSuccEmb = Fin.init x ∘ w := by
    intro x; funext i; rfl
  rw [hcomp y, hcomp z]
  have hcond : (∀ a : Fin (n + 1), a ∉ Set.range (w.trans Fin.castSuccEmb) → y a = z a) ↔
      y (Fin.last n) = z (Fin.last n) ∧ ∀ a : Fin n, a ∉ Set.range w → Fin.init y a = Fin.init z a := by
    constructor
    · intro h
      refine ⟨h (Fin.last n) ?_, fun a ha => h (Fin.castSucc a) ?_⟩
      · rintro ⟨i, hi⟩
        exact Fin.castSucc_ne_last (w i) hi
      · rintro ⟨i, hi⟩
        exact ha ⟨i, Fin.castSucc_inj.1 hi⟩
    · rintro ⟨hlast, hinit⟩ a
      refine Fin.lastCases (fun _ => hlast) (fun j ha => hinit j ?_) a
      rintro ⟨i, rfl⟩
      exact ha ⟨i, rfl⟩
  by_cases hlast : y (Fin.last n) = z (Fin.last n)
  · rw [if_pos hlast]
    by_cases hinit : ∀ a : Fin n, a ∉ Set.range w → Fin.init y a = Fin.init z a
    · rw [if_pos (hcond.2 ⟨hlast, hinit⟩), if_pos hinit]
    · rw [if_neg (fun h => hinit (hcond.1 h).2), if_neg hinit]
  · rw [if_neg hlast, if_neg (fun h => hlast (hcond.1 h).1)]

lemma liftInit_list_prod {n : ℕ} (L : List (Matrix (Qubits n) (Qubits n) ℂ)) :
    (L.map liftInit).prod = liftInit L.prod := by
  induction L with
  | nil => simp [liftInit_one]
  | cons A L ih => simp [List.prod_cons, ih, liftInit_mul]

lemma liftCircuit_unitary {S : Set Gate} {n : ℕ} (c : Circuit S n) :
    Circuit.unitary (liftCircuit c) = liftInit (Circuit.unitary c) := by
  simp only [Circuit.unitary, liftCircuit, ← List.map_reverse]
  rw [List.map_map]
  have hmap : ((fun g => embedOp g.gate.mat g.wires) ∘ liftGateApp) =
      liftInit ∘ (fun g : GateApp S n => embedOp g.gate.mat g.wires) := by
    funext g
    simp [liftGateApp, embedOp_trans_castSuccEmb]
  rw [hmap, ← List.map_map, liftInit_list_prod]

lemma circuit_unitary_append {S : Set Gate} {n : ℕ} (c1 c2 : Circuit S n) :
    Circuit.unitary (c1 ++ c2) = Circuit.unitary c2 * Circuit.unitary c1 := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma circuit_size_append {S : Set Gate} {n : ℕ} (c1 c2 : Circuit S n) :
    Circuit.size (c1 ++ c2) = Circuit.size c1 + Circuit.size c2 := by
  simp [Circuit.size]

/-- Diagonal gate embedding lemma. -/
lemma embedOp_diagonal {k n : ℕ} (d : Qubits k → ℂ) (w : Fin k ↪ Fin n) :
    embedOp (Matrix.diagonal d) w = Matrix.diagonal (fun y => d (y ∘ w)) := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz
    simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso
      apply hyz
      funext a
      by_cases ha : a ∈ Set.range w
      · rcases ha with ⟨i, rfl⟩
        exact congrFun h2 i
      · exact h1 a ha
    · rfl
    · rfl

/-- Controlled-`R_s` gate application on wires `c ≠ t`. -/
noncomputable def ctrlRotApp {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (c t : Fin n) (hct : c ≠ t) :
    GateApp qftGateSet n :=
  ⟨Gate.ofMatrix2 (controlled (rotR s)),
    Or.inl (Or.inr ⟨s, hs, rfl⟩),
    wire2 c t hct⟩

lemma embedOp_ctrlRotApp {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (c t : Fin n) (hct : c ≠ t) :
    embedOp (ctrlRotApp s hs c t hct).gate.mat (ctrlRotApp s hs c t hct).wires =
      Matrix.diagonal (fun y : Qubits n =>
        if y c && y t then Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ s) else 1) := by
  change embedOp ((controlled (rotR s)).submatrix (fun b : Qubits 2 => (b 0, b 1))
    (fun b : Qubits 2 => (b 0, b 1))) (wire2 c t hct) = _
  have hmat : (controlled (rotR s)).submatrix (fun b : Qubits 2 => (b 0, b 1))
      (fun b : Qubits 2 => (b 0, b 1)) =
      Matrix.diagonal (fun b : Qubits 2 =>
        if b 0 && b 1 then Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ s) else 1) := by
    ext y z
    simp only [Matrix.submatrix_apply, controlled, rotR, Matrix.of_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hyz : y = z
    · subst hyz
      cases y 0 <;> cases y 1 <;> simp
    · rw [if_neg hyz]
      by_cases h0 : y 0 = z 0
      · have h1 : y 1 ≠ z 1 := by
          intro h1
          apply hyz
          funext i
          fin_cases i
          · exact h0
          · exact h1
        simp [h0, h1]
      · simp [h0]
  rw [hmat, embedOp_diagonal]
  rfl

/-- Phase circuit of `n` controlled-`R_{m+2}` gates on `(castSucc m, last n)`. -/
noncomputable def phaseCircuit (n : ℕ) : Circuit qftGateSet (n + 1) :=
  List.ofFn fun m : Fin n =>
    ctrlRotApp ((m : ℕ) + 2) (by omega) (Fin.castSucc m) (Fin.last n) (Fin.castSucc_ne_last m)

@[simp]
lemma phaseCircuit_size (n : ℕ) : Circuit.size (phaseCircuit n) = n := by
  simp [Circuit.size, phaseCircuit]

lemma list_prod_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    (L : List α) (f : α → ι → ℂ) :
    (L.map (fun a => Matrix.diagonal (f a))).prod =
      Matrix.diagonal (fun y => (L.map (fun a => f a y)).prod) := by
  induction L with
  | nil =>
      ext y z
      by_cases h : y = z <;> simp [Matrix.diagonal, h]
  | cons a L ih =>
      rw [List.map_cons, List.prod_cons, ih, Matrix.diagonal_mul_diagonal]
      rfl

lemma phaseCircuit_unitary (n : ℕ) :
    Circuit.unitary (phaseCircuit n) =
      Matrix.diagonal (fun y : Qubits (n + 1) =>
        ∏ m : Fin n,
          if y (Fin.castSucc m) && y (Fin.last n) then
            Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ ((m : ℕ) + 2))
          else 1) := by
  simp only [Circuit.unitary, phaseCircuit, List.map_ofFn]
  let f : Fin n → Qubits (n + 1) → ℂ := fun m y =>
    if y (Fin.castSucc m) && y (Fin.last n) then
      Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ ((m : ℕ) + 2))
    else 1
  have hfun : (fun g => embedOp g.gate.mat g.wires) ∘
      (fun m : Fin n => ctrlRotApp ((m : ℕ) + 2) (by omega) (Fin.castSucc m) (Fin.last n)
        (Fin.castSucc_ne_last m)) =
      fun m : Fin n => Matrix.diagonal (f m) := by
    funext m
    exact embedOp_ctrlRotApp ((m : ℕ) + 2) (by omega) (Fin.castSucc m) (Fin.last n)
      (Fin.castSucc_ne_last m)
  rw [hfun]
  have hofFn : List.ofFn (fun m : Fin n => Matrix.diagonal (f m)) =
      (List.finRange n).map (fun m : Fin n => Matrix.diagonal (f m)) := by
    rw [List.ofFn_eq_map]
  rw [hofFn, ← List.map_reverse, list_prod_diagonal]
  congr 1
  funext y
  rw [List.map_reverse, List.prod_reverse, ← List.ofFn_eq_map, Fin.prod_ofFn]

/-- Hadamard gate application on wire `q`. -/
noncomputable def hadApp {n : ℕ} (q : Fin n) : GateApp qftGateSet n :=
  ⟨Gate.ofMatrix1 hadamard, Or.inl (Or.inl rfl), wire1 q⟩

lemma embedOp_hadApp_last (n : ℕ) (y z : Qubits (n + 1)) :
    embedOp (hadApp (Fin.last n)).gate.mat (hadApp (Fin.last n)).wires y z =
      if Fin.init y = Fin.init z then hadamard (y (Fin.last n)) (z (Fin.last n)) else 0 := by
  change embedOp (hadamard.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0))
    (wire1 (Fin.last n)) y z = _
  simp only [embedOp, Matrix.of_apply, Matrix.submatrix_apply]
  have hcond : (∀ a : Fin (n + 1), a ∉ Set.range (wire1 (Fin.last n)) → y a = z a) ↔
      Fin.init y = Fin.init z := by
    constructor
    · intro h
      funext j
      refine h (Fin.castSucc j) ?_
      rintro ⟨i, hi⟩
      exact Fin.castSucc_ne_last j hi.symm
    · intro h a
      refine Fin.lastCases (fun ha => absurd ⟨0, rfl⟩ ha) (fun j _ => congrFun h j) a
  by_cases hinit : Fin.init y = Fin.init z
  · rw [if_pos (hcond.2 hinit), if_pos hinit]
    rfl
  · rw [if_neg (fun h => hinit (hcond.1 h)), if_neg hinit]

/-- SWAP gate application on wires `c ≠ t`. -/
def swapApp {n : ℕ} (c t : Fin n) (hct : c ≠ t) : GateApp qftGateSet n :=
  ⟨Gate.ofMatrix2 swapGate, Or.inr rfl, wire2 c t hct⟩

lemma embedOp_swapApp {n : ℕ} (c t : Fin n) (hct : c ≠ t) (y z : Qubits n) :
    embedOp (swapApp c t hct).gate.mat (swapApp c t hct).wires y z =
      if y ∘ Equiv.swap c t = z then 1 else 0 := by
  change embedOp (swapGate.submatrix (fun b : Qubits 2 => (b 0, b 1))
    (fun b : Qubits 2 => (b 0, b 1))) (wire2 c t hct) y z = _
  simp only [embedOp, swapGate, Matrix.of_apply, Matrix.submatrix_apply]
  have h0 : wire2 c t hct 0 = c := rfl
  have h1 : wire2 c t hct 1 = t := rfl
  simp only [Function.comp_apply, h0, h1]
  by_cases hswap : y ∘ Equiv.swap c t = z
  · subst hswap
    have hcond : ∀ a : Fin n, a ∉ Set.range (wire2 c t hct) →
        y a = (y ∘ Equiv.swap c t) a := by
      intro a ha
      have hac : a ≠ c := fun h => ha ⟨0, h.symm⟩
      have hat : a ≠ t := fun h => ha ⟨1, h.symm⟩
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hac hat]
    rw [if_pos hcond]
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rw [if_neg hswap]
    split_ifs with hcond hpair
    · exfalso
      apply hswap
      funext a
      by_cases hac : a = c
      · subst hac
        simpa [Equiv.swap_apply_left] using (Prod.mk.inj hpair).2
      · by_cases hat : a = t
        · subst hat
          simpa [Equiv.swap_apply_right] using (Prod.mk.inj hpair).1
        · have ha : a ∉ Set.range (wire2 c t hct) := by
            rintro ⟨i, hi⟩
            fin_cases i
            · exact hac hi.symm
            · exact hat hi.symm
          simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hac hat]
          exact hcond a ha
    · rfl
    · rfl

lemma embedOp_swapApp_mul {n : ℕ} (c t : Fin n) (hct : c ≠ t)
    (A : Matrix (Qubits n) (Qubits n) ℂ) (y k : Qubits n) :
    (embedOp (swapApp c t hct).gate.mat (swapApp c t hct).wires * A) y k =
      A (y ∘ Equiv.swap c t) k := by
  rw [Matrix.mul_apply]
  rw [Fintype.sum_eq_single (y ∘ Equiv.swap c t)]
  · rw [embedOp_swapApp, if_pos rfl, one_mul]
  · intro z hz
    rw [embedOp_swapApp, if_neg hz.symm, zero_mul]

/-- Sequence of `n` SWAP gates cycling `(0, 1, ..., n)`. -/
def cycleSwaps : (n : ℕ) → Circuit qftGateSet (n + 1)
  | 0 => []
  | m + 1 =>
      [swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) (Fin.castSucc_ne_last _)] ++
        liftCircuit (cycleSwaps m)

@[simp]
lemma cycleSwaps_size (n : ℕ) : Circuit.size (cycleSwaps n) = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [cycleSwaps, circuit_size_append, liftCircuit_size, ih]
      simp [Circuit.size]
      omega

lemma snoc_snoc_comp_swap {m : ℕ} (y : Qubits (m + 2)) :
    Fin.snoc (Fin.snoc (Fin.tail (Fin.init y)) (Fin.init y 0)) (y (Fin.last (m + 1))) ∘
      Equiv.swap (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) =
      Fin.snoc (Fin.tail y) (y 0) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Equiv.swap_apply_right, Fin.snoc_castSucc, Fin.snoc_last, Fin.init]
  · refine Fin.lastCases ?_ (fun j0 => ?_) j
    · simp [Equiv.swap_apply_left, Fin.snoc_last, Fin.snoc_castSucc, Fin.tail]
    · have hne1 : Fin.castSucc (Fin.castSucc j0) ≠ Fin.castSucc (Fin.last m) := by
        intro h
        exact Fin.castSucc_ne_last j0 (Fin.castSucc_inj.1 h)
      have hne2 : Fin.castSucc (Fin.castSucc j0) ≠ Fin.last (m + 1) :=
        Fin.castSucc_ne_last _
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      simp only [Fin.snoc_castSucc, Fin.tail, Fin.init]
      rfl

lemma cycleSwaps_unitary_mul (n : ℕ) (A : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ)
    (y k : Qubits (n + 1)) :
    (Circuit.unitary (cycleSwaps n) * A) y k = A (Fin.snoc (Fin.tail y) (y 0)) k := by
  induction n with
  | zero =>
      have hy : Fin.snoc (Fin.tail y) (y 0) = y := by
        funext i
        fin_cases i
        rfl
      simp [cycleSwaps, Circuit.unitary, hy]
  | succ m ih =>
      rw [cycleSwaps, circuit_unitary_append, liftCircuit_unitary, Matrix.mul_assoc]
      have hsingle : Circuit.unitary
          [swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) (Fin.castSucc_ne_last _)] =
          embedOp (swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1))
            (Fin.castSucc_ne_last _)).gate.mat
            (swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1))
              (Fin.castSucc_ne_last _)).wires := by
        simp [Circuit.unitary]
      rw [hsingle]
      let B := embedOp (swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1))
        (Fin.castSucc_ne_last _)).gate.mat
        (swapApp (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) (Fin.castSucc_ne_last _)).wires * A
      let C : Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ :=
        Matrix.of fun u _ => B (Fin.snoc u (y (Fin.last (m + 1)))) k
      have hBC : (liftInit (Circuit.unitary (cycleSwaps m)) * B) y k =
          (Circuit.unitary (cycleSwaps m) * C) (Fin.init y) (Fin.init y) := by
        simp only [Matrix.mul_apply, liftInit_apply, C, Matrix.of_apply]
        let e : Qubits (m + 1) × Bool ≃ Qubits (m + 2) :=
          { toFun := fun p => Fin.snoc p.1 p.2
            invFun := fun x => (Fin.init x, x (Fin.last (m + 1)))
            left_inv := fun p => by ext <;> simp
            right_inv := fun x => Fin.snoc_init_self x }
        rw [← Equiv.sum_comp e]
        simp only [e, Equiv.coe_fn_mk, init_snoc_qubits, snoc_last_qubits, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Fintype.sum_eq_single (y (Fin.last (m + 1)))]
        · simp
        · intro b hb
          rw [if_neg (Ne.symm hb), zero_mul]
      rw [hBC, ih C (Fin.init y) (Fin.init y)]
      simp only [C, Matrix.of_apply, B]
      rw [embedOp_swapApp_mul, snoc_snoc_comp_swap]

/-- Decomposition of `bitsToNat` via `j 0` and `Fin.tail j`. -/
lemma bitsToNat_cons {n : ℕ} (j : Qubits (n + 1)) :
    bitsToNat j = (if j 0 then 2 ^ n else 0) + bitsToNat (Fin.tail j) := by
  simp only [bitsToNat, Fin.sum_univ_succ, Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero,
    Fin.tail]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : n - (i.succ : ℕ) = n - 1 - (i : ℕ) := by
    rw [Fin.val_succ]
    omega
  rw [hsub]
  rfl

/-- Decomposition of `bitsToNat` via `Fin.init k` and `k (Fin.last n)`. -/
lemma bitsToNat_snoc {n : ℕ} (k : Qubits (n + 1)) :
    bitsToNat k = 2 * bitsToNat (Fin.init k) + (if k (Fin.last n) then 1 else 0) := by
  simp only [bitsToNat, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    Nat.add_sub_cancel, Nat.sub_self, pow_zero, Fin.init, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  have hsub : n - (i : ℕ) = (n - 1 - (i : ℕ)) + 1 := by omega
  rw [hsub, pow_succ']
  by_cases h : k i.castSucc = true <;> simp [h]

lemma phaseDiag_eq_exp {n : ℕ} (u : Qubits n) (b : Bool) :
    (∏ m : Fin n,
      if u m && b then
        Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ ((m : ℕ) + 2))
      else 1) =
    Complex.exp (2 * Real.pi * Complex.I *
      ((bitsToNat u : ℂ) * (if b then 1 else 0)) / (2 ^ (n + 1) : ℂ)) := by
  have hterm : ∀ m : Fin n,
      (if u m && b then
        Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ ((m : ℕ) + 2))
      else 1) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((if u m then 2 ^ (n - 1 - (m : ℕ)) else 0 : ℕ) : ℂ) * (if b then 1 else 0)) /
          (2 ^ (n + 1) : ℂ)) := by
    intro m
    have hm := m.isLt
    have hpow : (2 : ℂ) ^ (n + 1) = (2 : ℂ) ^ (n - 1 - (m : ℕ)) * (2 : ℂ) ^ ((m : ℕ) + 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hne : (2 : ℂ) ^ (n - 1 - (m : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
    cases u m <;> cases b <;> simp
    congr 1
    rw [hpow, mul_comm ((2 : ℂ) ^ (n - 1 - (m : ℕ))) ((2 : ℂ) ^ ((m : ℕ) + 2)),
      mul_div_mul_right _ _ hne]
  simp_rw [hterm, ← Complex.exp_sum]
  congr 1
  simp only [bitsToNat, Nat.cast_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_div]

lemma hadamard_eq_exp (n : ℕ) (a b : Bool) :
    hadamard a b =
      Complex.exp (2 * Real.pi * Complex.I *
        (((if a then 2 ^ n else 0 : ℕ) : ℂ) * (if b then 1 else 0)) / (2 ^ (n + 1) : ℂ)) /
        (Real.sqrt 2 : ℂ) := by
  have hpow : (2 : ℂ) ^ (n + 1) = 2 * (2 : ℂ) ^ n := by
    rw [pow_succ']
  have hne : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpi : Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ n / (2 ^ (n + 1) : ℂ)) = -1 := by
    rw [hpow, mul_div_mul_right _ _ hne]
    rw [show (2 * Real.pi * Complex.I / 2 : ℂ) = Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  cases a <;> cases b <;>
    simp only [hadamard, Matrix.of_apply, Bool.and_self, Bool.and_false, Bool.false_and,
      ↓reduceIte, Bool.false_eq_true, Nat.cast_zero, mul_zero, zero_div,
      Complex.exp_zero, one_div, Nat.cast_pow, Nat.cast_ofNat, mul_one]
  · rw [hpi]
    ring

lemma exp_two_pi_I_nat (m : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (m : ℂ)) = 1 := by
  rw [show 2 * Real.pi * Complex.I * (m : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_nat_mul_two_pi_mul_I m

lemma qftQubits_apply (n : ℕ) (j k : Qubits n) :
    qftQubits n j k =
      Complex.exp (2 * Real.pi * Complex.I * ((bitsToNat j : ℂ) * (bitsToNat k : ℂ)) /
        (2 ^ n : ℂ)) / (Real.sqrt (2 ^ n) : ℂ) := by
  simp [qftQubits, qftMatrix, bitsEquivFin_apply]

lemma qftQubits_step (n : ℕ) (j k : Qubits (n + 1)) :
    hadamard (j 0) (k (Fin.last n)) *
      ((∏ m : Fin n,
          if Fin.tail j m && k (Fin.last n) then
            Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ ((m : ℕ) + 2))
          else 1) *
        qftQubits n (Fin.tail j) (Fin.init k)) =
      qftQubits (n + 1) j k := by
  rw [hadamard_eq_exp n (j 0) (k (Fin.last n)), phaseDiag_eq_exp (Fin.tail j) (k (Fin.last n)),
    qftQubits_apply n (Fin.tail j) (Fin.init k), qftQubits_apply (n + 1) j k]
  have hsqrt : (Real.sqrt 2 : ℂ) * (Real.sqrt (2 ^ n) : ℂ) = (Real.sqrt (2 ^ (n + 1)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]
    congr 2
    ring
  have hdiv : ∀ a b c s1 s2 : ℂ, (a / s1) * (b * (c / s2)) = (a * b * c) / (s1 * s2) := by
    intro a b c s1 s2
    ring
  rw [hdiv, hsqrt, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h1 : Complex.exp (2 * Real.pi * Complex.I *
      (((if j 0 then 2 ^ n else 0 : ℕ) : ℂ) * (bitsToNat (Fin.init k) : ℂ) * 2) /
        (2 ^ (n + 1) : ℂ)) = 1 := by
    have hpow : (2 : ℂ) ^ (n + 1) = (2 : ℂ) ^ n * 2 := by rw [pow_succ]
    cases j 0
    · simp
    · simp only [↓reduceIte, Nat.cast_pow, Nat.cast_ofNat]
      have hne : (2 : ℂ) ^ n * 2 ≠ 0 := pow_ne_zero (n + 1) (by norm_num)
      rw [hpow,
        show 2 * Real.pi * Complex.I * ((2 : ℂ) ^ n * (bitsToNat (Fin.init k) : ℂ) * 2) =
          (2 * Real.pi * Complex.I * (bitsToNat (Fin.init k) : ℂ)) * ((2 : ℂ) ^ n * 2) by ring,
        mul_div_cancel_right₀ _ hne]
      exact exp_two_pi_I_nat (bitsToNat (Fin.init k))
  let A : ℂ :=
    2 * Real.pi * Complex.I *
      (((if j 0 then 2 ^ n else 0 : ℕ) : ℂ) * (if k (Fin.last n) then 1 else 0)) / (2 ^ (n + 1) : ℂ) +
    2 * Real.pi * Complex.I *
      ((bitsToNat (Fin.tail j) : ℂ) * (if k (Fin.last n) then 1 else 0)) / (2 ^ (n + 1) : ℂ) +
    2 * Real.pi * Complex.I *
      ((bitsToNat (Fin.tail j) : ℂ) * (bitsToNat (Fin.init k) : ℂ)) / (2 ^ n : ℂ)
  let C : ℂ :=
    2 * Real.pi * Complex.I *
      (((if j 0 then 2 ^ n else 0 : ℕ) : ℂ) * (bitsToNat (Fin.init k) : ℂ) * 2) /
      (2 ^ (n + 1) : ℂ)
  calc Complex.exp A
    _ = Complex.exp A * 1 := (mul_one _).symm
    _ = Complex.exp A * Complex.exp C := by rw [h1]
    _ = Complex.exp (A + C) := (Complex.exp_add A C).symm
    _ = Complex.exp (2 * Real.pi * Complex.I * ((bitsToNat j : ℂ) * (bitsToNat k : ℂ)) /
          (2 ^ (n + 1) : ℂ)) := by
      congr 1
      dsimp only [A, C]
      have hj : (bitsToNat j : ℂ) =
          ((if j 0 then 2 ^ n else 0 : ℕ) : ℂ) + (bitsToNat (Fin.tail j) : ℂ) := by
        exact_mod_cast bitsToNat_cons j
      have hk : (bitsToNat k : ℂ) =
          2 * (bitsToNat (Fin.init k) : ℂ) + ((if k (Fin.last n) then 1 else 0 : ℕ) : ℂ) := by
        exact_mod_cast bitsToNat_snoc k
      have hpow : (2 : ℂ) ^ (n + 1) = (2 : ℂ) ^ n * 2 := by rw [pow_succ]
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      have hscale :
          2 * Real.pi * Complex.I * ((bitsToNat (Fin.tail j) : ℂ) * (bitsToNat (Fin.init k) : ℂ)) /
            (2 ^ n : ℂ) =
          2 * Real.pi * Complex.I *
            ((bitsToNat (Fin.tail j) : ℂ) * (2 * (bitsToNat (Fin.init k) : ℂ))) /
            (2 ^ (n + 1) : ℂ) := by
        rw [hpow,
          show 2 * Real.pi * Complex.I *
              ((bitsToNat (Fin.tail j) : ℂ) * (2 * (bitsToNat (Fin.init k) : ℂ))) =
            (2 * Real.pi * Complex.I * ((bitsToNat (Fin.tail j) : ℂ) * (bitsToNat (Fin.init k) : ℂ))) * 2 by ring,
          mul_div_mul_right _ _ h2ne]
      rw [hj, hk, hscale]
      cases k (Fin.last n) <;>
        simp only [↓reduceIte, Bool.false_eq_true, Nat.cast_one, Nat.cast_zero] <;>
        ring

/-- Full QFT circuit on `n` qubits. -/
noncomputable def qftCircuit : (n : ℕ) → Circuit qftGateSet n
  | 0 => []
  | n + 1 =>
      liftCircuit (qftCircuit n) ++ phaseCircuit n ++ [hadApp (Fin.last n)] ++ cycleSwaps n

lemma qftCircuit_size (n : ℕ) : Circuit.size (qftCircuit n) ≤ n ^ 2 := by
  induction n with
  | zero => simp [qftCircuit, Circuit.size]
  | succ n ih =>
      rw [qftCircuit, circuit_size_append, circuit_size_append, circuit_size_append,
        liftCircuit_size, phaseCircuit_size, cycleSwaps_size]
      have hhad : Circuit.size ([hadApp (Fin.last n)] : Circuit qftGateSet (n + 1)) = 1 := rfl
      rw [hhad]
      nlinarith

lemma diagonal_mul_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (M : Matrix ι ι ℂ) (i j : ι) :
    (Matrix.diagonal d * M) i j = d i * M i j := by
  simp [Matrix.mul_apply, Matrix.diagonal]

lemma qftCircuit_unitary (n : ℕ) : Circuit.unitary (qftCircuit n) = qftQubits n := by
  induction n with
  | zero =>
      ext j k
      have hj : j = k := Subsingleton.elim j k
      subst hj
      simp [qftCircuit, Circuit.unitary, qftQubits_apply, bitsToNat]
  | succ n ih =>
      rw [qftCircuit, circuit_unitary_append, circuit_unitary_append, circuit_unitary_append,
        liftCircuit_unitary, ih]
      ext j k
      rw [cycleSwaps_unitary_mul]
      have hhad : Circuit.unitary ([hadApp (Fin.last n)] : Circuit qftGateSet (n + 1)) =
          embedOp (hadApp (Fin.last n)).gate.mat (hadApp (Fin.last n)).wires := by
        simp [Circuit.unitary]
      rw [hhad, phaseCircuit_unitary]
      let y0 : Qubits (n + 1) := Fin.snoc (Fin.tail j) (j 0)
      let z0 : Qubits (n + 1) := Fin.snoc (Fin.tail j) (k (Fin.last n))
      rw [Matrix.mul_apply]
      rw [Fintype.sum_eq_single z0]
      · dsimp only [z0]
        rw [embedOp_hadApp_last, init_snoc_qubits, init_snoc_qubits, if_pos rfl,
          snoc_last_qubits, snoc_last_qubits, diagonal_mul_apply, liftInit_apply,
          snoc_last_qubits, if_pos rfl, init_snoc_qubits]
        simp_rw [snoc_castSucc_qubits]
        exact qftQubits_step n j k
      · intro z hz
        rw [embedOp_hadApp_last, diagonal_mul_apply, liftInit_apply]
        by_cases hinit : Fin.init y0 = Fin.init z
        · by_cases hlast : z (Fin.last n) = k (Fin.last n)
          · exfalso
            apply hz
            apply (eq_iff_init_eq_and_last_eq z z0).2
            refine ⟨?_, ?_⟩
            · dsimp only [y0, z0] at hinit ⊢
              rw [← hinit, init_snoc_qubits, init_snoc_qubits]
            · dsimp only [z0]
              rw [hlast, snoc_last_qubits]
          · rw [if_neg hlast, mul_zero, mul_zero]
        · rw [if_neg hinit, zero_mul]

end SolQFTCircuitExact

theorem solution (n : ℕ) :
    ∃ c : Circuit qftGateSet n, c.unitary = qftQubits n ∧ c.size ≤ n ^ 2 :=
  ⟨SolQFTCircuitExact.qftCircuit n,
    SolQFTCircuitExact.qftCircuit_unitary n,
    SolQFTCircuitExact.qftCircuit_size n⟩
