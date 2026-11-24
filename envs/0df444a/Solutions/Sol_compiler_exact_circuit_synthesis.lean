-- Prove2me | solution 1 for compiler_exact_circuit_synthesis
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T12:18:53.836801+00:00
-- url     : https://prove2.me/submissions/367b23ec-6f78-4f31-9e96-d8f42cc7bb74

import Definitions.Def_QuantumLTF_Membership_gates12
import Theorems.Thm_SuperconductingQC_closure_singleQubit_CNOT_eq_top

set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

theorem compiler_embedOp_star {k n : ℕ}
    (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (star M) w = star (embedOp M w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.star_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range w → y a = z a) ↔
      (∀ a : Fin n, a ∉ Set.range w → z a = y a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · simp only [if_pos h, if_pos (hiff.mp h)]
  · simp only [if_neg h, if_neg (mt hiff.mpr h), star_zero]

noncomputable def compiler_adjoint_gate {n : ℕ} (g : GateApp gates12 n) : GateApp gates12 n where
  gate := ⟨g.gate.arity, star g.gate.mat⟩
  mem := by
    rcases g.mem with ⟨hU, hlo, hhi⟩
    exact ⟨Unitary.star_mem hU, hlo, hhi⟩
  wires := g.wires

noncomputable def compiler_adjoint_circuit {n : ℕ} (c : Circuit gates12 n) : Circuit gates12 n :=
  c.reverse.map compiler_adjoint_gate

theorem compiler_circuit_append {n : ℕ} (c d : Circuit gates12 n) :
    (c ++ d).unitary = d.unitary * c.unitary := by
  simp [Circuit.unitary, List.reverse_append, List.prod_append]

theorem compiler_circuit_adjoint {n : ℕ} (c : Circuit gates12 n) :
    (compiler_adjoint_circuit c).unitary = star c.unitary := by
  induction c with
  | nil => simp [compiler_adjoint_circuit, Circuit.unitary]
  | cons g c ih =>
    simp only [compiler_adjoint_circuit, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, compiler_circuit_append] at *
    simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one] at *
    rw [star_mul]
    rw [← ih]
    simp only [compiler_adjoint_gate, compiler_embedOp_star]

theorem compiler_unitary_submatrix_equiv {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : β ≃ α) (M : Matrix α α ℂ) (hM : M ∈ Matrix.unitaryGroup α ℂ) :
    M.submatrix e e ∈ Matrix.unitaryGroup β ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change M.submatrix e e * (star M).submatrix e e = 1
  rw [Matrix.submatrix_mul_equiv M (star M) e e e,
    Matrix.mem_unitaryGroup_iff.mp hM]
  ext a b
  simp [Matrix.one_apply, e.injective.eq_iff]

def compiler_binary_index (n : ℕ) : Qubits n ≃ (Fin n → Fin 2) :=
  Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm

@[simp] theorem compiler_binary_index_apply {n : ℕ} (x : Qubits n) (i : Fin n) :
    compiler_binary_index n x i = finTwoEquiv.symm (x i) := rfl

def compiler_single_index : Qubits 1 ≃ Fin 2 where
  toFun x := finTwoEquiv.symm (x 0)
  invFun a := fun _ => finTwoEquiv a
  left_inv x := by ext i; fin_cases i; simp
  right_inv a := by simp

noncomputable def compiler_one_qubit_placement {n : ℕ} (i : Fin n)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    GateApp gates12 n where
  gate := ⟨1, M.submatrix compiler_single_index compiler_single_index⟩
  mem := ⟨compiler_unitary_submatrix_equiv compiler_single_index M hM, by norm_num, by norm_num⟩
  wires := ⟨fun _ => i, by intro a b _; exact Subsingleton.elim _ _⟩

theorem compiler_one_qubit_placement_matrix {n : ℕ} (i : Fin n)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    embedOp (compiler_one_qubit_placement i M hM).gate.mat
      (compiler_one_qubit_placement i M hM).wires =
    (SuperconductingQC.onQubit i M).submatrix (compiler_binary_index n)
      (compiler_binary_index n) := by
  ext y z
  simp only [compiler_one_qubit_placement, embedOp, Matrix.of_apply,
    Matrix.submatrix_apply, SuperconductingQC.onQubit, compiler_single_index,
    compiler_binary_index_apply, Function.comp_apply]
  have hc : (∀ a : Fin n, a ∉ Set.range (fun _ : Fin 1 => i) → y a = z a) ↔
      (∀ j : Fin n, j ≠ i → finTwoEquiv.symm (y j) = finTwoEquiv.symm (z j)) := by
    simp only [Set.range_const, Set.mem_singleton_iff, Equiv.apply_eq_iff_eq]
  change (if ∀ a : Fin n, a ∉ Set.range (fun _ : Fin 1 => i) → y a = z a then
      M (finTwoEquiv.symm (y i)) (finTwoEquiv.symm (z i)) else 0) =
    (if ∀ j : Fin n, j ≠ i → finTwoEquiv.symm (y j) = finTwoEquiv.symm (z j) then
      M (finTwoEquiv.symm (y i)) (finTwoEquiv.symm (z i)) else 0)
  simp only [hc]

def compiler_pair_index : Qubits 2 ≃ (Fin 2 × Fin 2) where
  toFun x := (finTwoEquiv.symm (x 0), finTwoEquiv.symm (x 1))
  invFun a := ![finTwoEquiv a.1, finTwoEquiv a.2]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv a := by rcases a with ⟨a,b⟩; simp

theorem compiler_cnot_unitary :
    SuperconductingQC.CNOT ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  have hone : (1 + 1 : Fin 2) = 0 := by decide
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [SuperconductingQC.CNOT, Matrix.mul_apply, Matrix.star_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, hone]

noncomputable def compiler_two_qubit_placement {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    GateApp gates12 n where
  gate := ⟨2, SuperconductingQC.CNOT.submatrix compiler_pair_index compiler_pair_index⟩
  mem := ⟨compiler_unitary_submatrix_equiv compiler_pair_index _ compiler_cnot_unitary,
    by norm_num, by norm_num⟩
  wires := ⟨![i,j], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

theorem compiler_two_qubit_placement_matrix {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    embedOp (compiler_two_qubit_placement i j hij).gate.mat
      (compiler_two_qubit_placement i j hij).wires =
    (SuperconductingQC.onPair i j SuperconductingQC.CNOT).submatrix
      (compiler_binary_index n) (compiler_binary_index n) := by
  ext y z
  change (if ∀ a : Fin n, a ∉ Set.range (![i,j] : Fin 2 → Fin n) → y a = z a then
      SuperconductingQC.CNOT (finTwoEquiv.symm (y i), finTwoEquiv.symm (y j))
        (finTwoEquiv.symm (z i), finTwoEquiv.symm (z j)) else 0) =
    (if ∀ a : Fin n, a ≠ i → a ≠ j →
      finTwoEquiv.symm (y a) = finTwoEquiv.symm (z a) then
      SuperconductingQC.CNOT (finTwoEquiv.symm (y i), finTwoEquiv.symm (y j))
        (finTwoEquiv.symm (z i), finTwoEquiv.symm (z j)) else 0)
  congr 1
  simp [Set.mem_range, Fin.exists_fin_two, eq_comm, and_imp]
  exact ⟨fun h a hi hj => h a hj hi, fun h a hi hj => h a hj hi⟩

theorem compiler_binary_circuit_synthesis (n : ℕ) (hn : 1 ≤ n)
    (W : Matrix.unitaryGroup (Fin n → Fin 2) ℂ) :
    ∃ c : Circuit gates12 n,
      c.unitary = (W : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ).submatrix
        (compiler_binary_index n) (compiler_binary_index n) := by
  have hW : W ∈ Subgroup.closure
      (SuperconductingQC.singleQubitGates n ∪
        SuperconductingQC.twoQubitGateInstances n SuperconductingQC.CNOT) := by
    rw [SuperconductingQC.closure_singleQubit_CNOT_eq_top n hn]
    trivial
  induction hW using Subgroup.closure_induction with
  | mem W hW =>
    rcases hW with hsingle | hpair
    · obtain ⟨i, M, hM, hW⟩ := hsingle
      refine ⟨[compiler_one_qubit_placement i M hM], ?_⟩
      simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
      rw [hW]
      exact compiler_one_qubit_placement_matrix i M hM
    · obtain ⟨i, j, hij, hW⟩ := hpair
      refine ⟨[compiler_two_qubit_placement i j hij], ?_⟩
      simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
      rw [hW]
      exact compiler_two_qubit_placement_matrix i j hij
  | one =>
    refine ⟨[], ?_⟩
    ext y z
    simp [Circuit.unitary, Matrix.one_apply, (compiler_binary_index n).injective.eq_iff]
  | mul W V _ _ ihW ihV =>
    obtain ⟨c, hc⟩ := ihW
    obtain ⟨d, hd⟩ := ihV
    refine ⟨d ++ c, ?_⟩
    rw [compiler_circuit_append, hc, hd]
    exact Matrix.submatrix_mul_equiv _ _ (compiler_binary_index n)
      (compiler_binary_index n) (compiler_binary_index n)
  | inv W _ ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨compiler_adjoint_circuit c, ?_⟩
    rw [compiler_circuit_adjoint, hc]
    rfl

/-- Every finite qubit unitary has an exact realization with arbitrary
one-qubit and two-qubit gates, with no oracle calls. -/
theorem solution (n : ℕ) (hn : 1 ≤ n)
    (M : Matrix (Qubits n) (Qubits n) ℂ) (hM : M ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    ∃ c : Circuit gates12 n, c.unitary = M := by
  let e := compiler_binary_index n
  let W : Matrix.unitaryGroup (Fin n → Fin 2) ℂ :=
    ⟨M.submatrix e.symm e.symm, compiler_unitary_submatrix_equiv e.symm M hM⟩
  obtain ⟨c, hc⟩ := compiler_binary_circuit_synthesis n hn W
  refine ⟨c, hc.trans ?_⟩
  ext y z
  simp [W, e, Matrix.submatrix_apply]

