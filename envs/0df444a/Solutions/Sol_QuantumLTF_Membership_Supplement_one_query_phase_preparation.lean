-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.one_query_phase_preparation
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T23:23:17.971822+00:00
-- url     : https://prove2.me/submissions/4d5df980-4e25-4e40-95a6-e43eb4c5698f

import Mathlib
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_Supplement_ForwardOnly

set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

noncomputable def section5_snoc_equiv (N : ℕ) :
    Qubits (N+1) ≃ Qubits N × Bool where
  toFun z := (Fin.init z,z (Fin.last N))
  invFun p := Fin.snoc p.1 p.2
  left_inv z := Fin.snoc_init_self z
  right_inv p := by
    apply Prod.ext <;> simp

noncomputable def section5_label_hadamard (N : ℕ) :
    Matrix (Qubits (N+1)) (Qubits (N+1)) ℂ :=
  fun z z' => if Fin.init z = Fin.init z' then hadamard (z (Fin.last N)) (z' (Fin.last N)) else 0

theorem section5_label_hadamard_action (N : ℕ)
    (ψ : EuclideanSpace ℂ (Qubits (N+1))) (x : Qubits N) (b : Bool) :
    act (section5_label_hadamard N) ψ (Fin.snoc x b) =
      hadamard b false * ψ (Fin.snoc x false) + hadamard b true * ψ (Fin.snoc x true) := by
  classical
  let f : Qubits (N+1) → ℂ := fun z =>
    section5_label_hadamard N (Fin.snoc x b) z * ψ z
  change (∑ z : Qubits (N+1), f z) = _
  rw [(Equiv.sum_comp (section5_snoc_equiv N).symm f).symm]
  simp [f,section5_label_hadamard,Fintype.sum_prod_type, section5_snoc_equiv, Fintype.sum_bool,
    ite_mul, Finset.sum_ite_eq]
  ring

noncomputable def section5_grid_amplitude {n q : ℕ} (x : Qubits (n*q)) : ℂ :=
  (Real.sqrt (gridWeight x / ∑ z : Qubits (n*q), gridWeight z):ℂ)

theorem section5_ltf_label_value {n : ℕ} (w x : EuclideanSpace ℝ (Fin n)) :
    ((ltf w 0 x : ℤ):ℂ) = if decide (ltf w 0 x = -1) then -1 else 1 := by
  unfold ltf sgn
  simp only [sub_zero]
  by_cases h : 0 ≤ inner ℝ w x
  · simp [h,not_lt_of_ge h]
  · simp [h,lt_of_not_ge h]

theorem section5_example_phase_identity {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (x : Qubits (n*q)) (b : Bool) :
    act (section5_label_hadamard (n*q)) (qexKet (q := q) w) (Fin.snoc x b) =
      (1/Real.sqrt 2:ℂ)*
        (if b then (ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x
          else section5_grid_amplitude x) := by
  classical
  rw [section5_label_hadamard_action]
  have hket (t : Bool) : qexKet (q := q) w (Fin.snoc x t) =
      if t = decide (ltf w 0 (gridPoint x) = -1) then section5_grid_amplitude x else 0 := by
    simp [qexKet, section5_grid_amplitude]
  rw [hket,hket,section5_ltf_label_value]
  cases b <;> cases h : decide (ltf w 0 (gridPoint x) = -1) <;> simp [hadamard,h,one_div]

theorem section5_grid_amplitude_norm {n q : ℕ} :
    ‖(WithLp.toLp 2 (section5_grid_amplitude (n := n) (q := q)) :
      EuclideanSpace ℂ (Qubits (n*q)))‖ = 1 := by
  have hpos (x : Qubits (n*q)) : 0 < gridWeight x := Real.exp_pos _
  have hZ : 0 < ∑ z : Qubits (n*q), gridWeight z :=
    Finset.sum_pos (fun z _ => hpos z) Finset.univ_nonempty
  have hsq : ‖(WithLp.toLp 2 (section5_grid_amplitude (n := n) (q := q)) :
      EuclideanSpace ℂ (Qubits (n*q)))‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [section5_grid_amplitude, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (div_nonneg (hpos _).le hZ.le)]
    rw [← Finset.sum_div,div_self hZ.ne']
  nlinarith [norm_nonneg (WithLp.toLp 2 (section5_grid_amplitude (n := n) (q := q)) :
      EuclideanSpace ℂ (Qubits (n*q)))]

theorem section5_phase_amplitude_norm {n q : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    ‖(WithLp.toLp 2 (fun x : Qubits (n*q) =>
      (ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x) :
      EuclideanSpace ℂ (Qubits (n*q)))‖ = 1 := by
  have hn : ∀ x : Qubits (n*q), ‖(ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x‖ =
      ‖section5_grid_amplitude x‖ := by
    intro x
    rw [norm_mul,section5_ltf_label_value]
    split_ifs <;> simp
  have hsq : ‖(WithLp.toLp 2 (fun x : Qubits (n*q) =>
      (ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x) :
      EuclideanSpace ℂ (Qubits (n*q)))‖^2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hn]
    exact (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (section5_grid_amplitude (n := n) (q := q)))).symm.trans
      (by rw [section5_grid_amplitude_norm]; norm_num)
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun x : Qubits (n*q) =>
      (ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x) :
      EuclideanSpace ℂ (Qubits (n*q)))]


set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix ComplexOrder MatrixOrder

noncomputable def section5_reindex_hom {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Matrix α α ℂ ≃⋆ₐ[ℂ] Matrix β β ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_smul' := by intro r A; ext i j; rfl
    map_star' := by intro A; ext i j; rfl }

theorem section5_trace_size_reindex {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (A : Matrix α α ℂ) :
    (cfc Real.sqrt ((A.submatrix e.symm e.symm).conjTranspose *
      A.submatrix e.symm e.symm)).trace.re =
      (cfc Real.sqrt (A.conjTranspose * A)).trace.re := by
  let F := section5_reindex_hom e
  have hmul : (A.submatrix e.symm e.symm).conjTranspose * A.submatrix e.symm e.symm =
      F (A.conjTranspose * A) := by
    exact (F.map_mul (star A) A).symm.trans (by rfl)
  rw [hmul]
  have hfc : F (cfc Real.sqrt (A.conjTranspose * A)) = cfc Real.sqrt (F (A.conjTranspose * A)) :=
    F.toStarAlgHom.map_cfc Real.sqrt (A.conjTranspose * A)
      Real.continuous_sqrt.continuousOn F.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
      (by change star (star A * A) = star A * A; simp)
      (by change star (F (star A * A)) = F (star A * A)
          rw [← map_star]; congr 1; simp)
  rw [← hfc]
  exact congrArg Complex.re (Equiv.sum_comp e.symm
    (fun i : α => cfc Real.sqrt (A.conjTranspose * A) i i))

theorem section5_trace_size_diagonal {α : Type*} [Fintype α] [DecidableEq α] (r : α → ℝ) :
    (cfc Real.sqrt ((Matrix.diagonal (fun i => (r i : ℂ))).conjTranspose *
      Matrix.diagonal (fun i => (r i : ℂ)))).trace.re = ∑ i, |r i| := by
  have hm : (Matrix.diagonal (fun i => (r i : ℂ))).conjTranspose *
      Matrix.diagonal (fun i => (r i : ℂ)) =
        Matrix.diagonal (fun i => (((r i)^2 : ℝ) : ℂ)) := by
    simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, pow_two]
  rw [hm]
  have hdiag : cfc Real.sqrt (Matrix.diagonal (fun i => (((r i)^2 : ℝ) : ℂ))) =
      Matrix.diagonal (fun i => ((|r i| : ℝ) : ℂ)) := by
    have hA : 0 ≤ Matrix.diagonal (fun i : α => (((r i)^2 : ℝ) : ℂ)) :=
      (Matrix.PosSemidef.diagonal (fun i => by
        change (0 : ℂ) ≤ (((r i)^2 : ℝ) : ℂ)
        exact Complex.zero_le_real.mpr (sq_nonneg (r i)))).nonneg
    have hB : 0 ≤ Matrix.diagonal (fun i : α => ((|r i| : ℝ) : ℂ)) :=
      (Matrix.PosSemidef.diagonal (fun i => by
        change (0 : ℂ) ≤ ((|r i| : ℝ) : ℂ)
        exact Complex.zero_le_real.mpr (abs_nonneg (r i)))).nonneg
    have hcfc : CFC.sqrt (Matrix.diagonal (fun i : α => (((r i)^2 : ℝ) : ℂ))) =
        cfc Real.sqrt (Matrix.diagonal (fun i : α => (((r i)^2 : ℝ) : ℂ))) := by
      rw [CFC.sqrt_eq_real_sqrt _ hA, cfcₙ_eq_cfc (hf0 := by simp)]
    rw [← hcfc]
    apply CFC.sqrt_unique (hb := hB)
    simp only [Matrix.diagonal_mul_diagonal, ← Complex.ofReal_mul]
    congr 1
    funext i
    congr 1
    exact (pow_two (|r i|)).symm.trans (sq_abs (r i))
  rw [hdiag]
  simp [Matrix.trace_diagonal, Real.sqrt_sq_eq_abs]


set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example QuantumLTF.Membership.Supplement

def section5_one_bit_equiv : Qubits 1 ≃ Bool where
  toFun z := z 0
  invFun b := fun _ => b
  left_inv z := by funext i; fin_cases i; rfl
  right_inv b := rfl

theorem section5_hadamard_gate_valid : Gate.ofMatrix1 hadamard ∈ gates12 := by
  have hstar : star hadamard = hadamard := by
    ext a b
    cases a <;> cases b <;> simp [hadamard,Matrix.star_apply]
  have hunit : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [hstar]
    exact hadamard_mul_self
  refine ⟨?_,by decide,by decide⟩
  exact Unitary.map_mem (section5_reindex_hom section5_one_bit_equiv.symm).toStarAlgHom hunit

noncomputable def section5_last_hadamard_gate (N : ℕ) : GateApp gates12 (N+1) where
  gate := Gate.ofMatrix1 hadamard
  mem := section5_hadamard_gate_valid
  wires := show Fin 1 ↪ Fin (N+1) from
    ⟨fun _ => Fin.last N, fun i j _ => Subsingleton.elim i j⟩

theorem section5_last_hadamard_embedded (N : ℕ) :
    embedOp (section5_last_hadamard_gate N).gate.mat (section5_last_hadamard_gate N).wires =
      section5_label_hadamard N := by
  classical
  ext y z
  have heq : (∀ a : Fin (N+1), a ∉ Set.range (section5_last_hadamard_gate N).wires → y a = z a) ↔
      Fin.init y = Fin.init z := by
    constructor
    · intro h
      funext i
      apply h i.castSucc
      rintro ⟨j,hj⟩
      change Fin.last N = i.castSucc at hj
      exact Fin.castSucc_ne_last i hj.symm
    · intro h a ha
      cases a using Fin.lastCases with
      | last => exact False.elim (ha ⟨(0 : Fin 1),rfl⟩)
      | cast i => exact congrFun h i
  change (if ∀ a : Fin (N+1), a ∉ Set.range (section5_last_hadamard_gate N).wires → y a = z a then
    hadamard (y (Fin.last N)) (z (Fin.last N)) else 0) = _
  simp only [heq]
  rfl

noncomputable def section5_example_phase_circuit (N : ℕ) :
    OracleCircuit gates12 (fun _ : Fin 1 => N+1) (N+1) :=
  [OracleStep.query 0 false none (Function.Embedding.refl _) (by simp),
    OracleStep.gate (section5_last_hadamard_gate N)]

theorem section5_example_phase_resources (N : ℕ) :
    Uncontrolled (section5_example_phase_circuit N) ∧
    ForwardOnly (section5_example_phase_circuit N) ∧
    (section5_example_phase_circuit N).queryCount 0 = 1 ∧
    (section5_example_phase_circuit N).gateCount = 1 := by
  simp [section5_example_phase_circuit,Uncontrolled,ForwardOnly,
    OracleCircuit.queryCount,OracleCircuit.gateCount,OracleStep.IsQueryTo]

theorem section5_example_phase_unitary (N : ℕ)
    (U : Matrix (Qubits (N+1)) (Qubits (N+1)) ℂ) :
    (section5_example_phase_circuit N).unitary (fun _ => U) = section5_label_hadamard N * U := by
  classical
  have hfull : embedOp U (Function.Embedding.refl _) = U := by
    ext y z
    simp [embedOp,Function.comp_def]
  simp [section5_example_phase_circuit,OracleCircuit.unitary,OracleStep.mat,
    section5_last_hadamard_embedded,hfull]

theorem section5_example_phase_prepares {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (U : Matrix (Qubits (n*q+1)) (Qubits (n*q+1)) ℂ) (hU : IsQEX (q := q) w U)
    (x : Qubits (n*q)) (b : Bool) :
    act ((section5_example_phase_circuit (n*q)).unitary (fun _ => U)) (zeroKet (n*q+1))
      (Fin.snoc x b) =
      (1/Real.sqrt 2:ℂ)*
        (if b then (ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x
          else section5_grid_amplitude x) := by
  rw [section5_example_phase_unitary]
  have heq : act U (zeroKet (n*q+1)) = qexKet (q := q) w := by
    exact congrArg (WithLp.toLp 2) hU.2
  have hmul : act (section5_label_hadamard (n*q)*U) (zeroKet (n*q+1)) =
      act (section5_label_hadamard (n*q)) (act U (zeroKet (n*q+1))) := by
    exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec _ _ _).symm
  rw [hmul,heq]
  exact section5_example_phase_identity w x b

theorem solution (n q : ℕ) :
    ∃ (c : OracleCircuit gates12 (fun _ : Fin 1 => n*q+1) (n*q+1))
      (F0 : EuclideanSpace ℂ (Qubits (n*q))),
      ‖F0‖ = 1 ∧ Uncontrolled c ∧ ForwardOnly c ∧ c.queryCount 0 = 1 ∧ c.gateCount = 1 ∧
      ∀ w : EuclideanSpace ℝ (Fin n),
      ∀ U : Matrix (Qubits (n*q+1)) (Qubits (n*q+1)) ℂ, IsQEX (q := q) w U →
        ∃ Fw : EuclideanSpace ℂ (Qubits (n*q)), ‖Fw‖ = 1 ∧
          ∀ (x : Qubits (n*q)) (b : Bool),
            act (c.unitary (fun _ => U)) (zeroKet (n*q+1)) (Fin.snoc x b) =
              (1/Real.sqrt 2:ℂ)*(if b then Fw x else F0 x) := by
  obtain ⟨hunc,hfwd,hquery,hgate⟩ := section5_example_phase_resources (n*q)
  refine ⟨section5_example_phase_circuit (n*q), WithLp.toLp 2 section5_grid_amplitude,
    section5_grid_amplitude_norm,hunc,hfwd,hquery,hgate,?_⟩
  intro w U hU
  refine ⟨WithLp.toLp 2 (fun x => (ltf w 0 (gridPoint x):ℂ)*section5_grid_amplitude x),
    section5_phase_amplitude_norm w,?_⟩
  exact section5_example_phase_prepares w U hU
