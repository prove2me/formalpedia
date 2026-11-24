-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.tomography_process_unitary
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T23:25:24.153691+00:00
-- url     : https://prove2.me/submissions/0e1df686-6f1e-467a-882d-bcde59d814ae

import Mathlib
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled

set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
open scoped Kronecker

noncomputable def section5_reindex_hom {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Matrix α α ℂ ≃⋆ₐ[ℂ] Matrix β β ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_smul' := by intro r A; ext i j; rfl
    map_star' := by intro A; ext i j; rfl }

noncomputable def section5_out_equiv {m o : ℕ} (out : Fin o ↪ Fin m) :
    Qubits m ≃ Qubits o × ({j : Fin m // ¬ ∃ i : Fin o, out i = j} → Bool) where
  toFun z := (z ∘ out, fun j => z j)
  invFun p j := if h : ∃ i : Fin o, out i = j then p.1 h.choose else p.2 ⟨j,h⟩
  left_inv z := by
    funext j
    change (if h : ∃ i : Fin o, out i = j then z (out h.choose) else z j) = z j
    split_ifs with h
    · change z (out h.choose) = z j
      rw [h.choose_spec]
    · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      have hi : ∃ i' : Fin o, out i' = out i := ⟨i,rfl⟩
      change (if h : ∃ i' : Fin o, out i' = out i then p.1 h.choose else _) = p.1 i
      rw [dif_pos hi, out.injective hi.choose_spec]
    · funext j
      change (if h : ∃ i : Fin o, out i = j.val then p.1 h.choose else _) = p.2 j
      rw [dif_neg j.property]

theorem section5_out_equiv_restrict {m o : ℕ} (out : Fin o ↪ Fin m)
    (p : Qubits o × ({j : Fin m // ¬ ∃ i : Fin o, out i = j} → Bool)) :
    (section5_out_equiv out).symm p ∘ out = p.1 :=
  congrArg Prod.fst ((section5_out_equiv out).apply_symm_apply p)

theorem section5_out_equiv_rest {m o : ℕ} (out : Fin o ↪ Fin m) (z z' : Qubits m) :
    (∀ j : Fin m, (∀ i : Fin o, out i ≠ j) → z j = z' j) ↔
      (section5_out_equiv out z).2 = (section5_out_equiv out z').2 := by
  constructor
  · intro h
    funext j
    exact h j.val (fun i hi => j.property ⟨i,hi⟩)
  · intro h j hj
    exact congrFun h ⟨j, by rintro ⟨i,hi⟩; exact hj i hi⟩

theorem section5_embed_unitary {k n : ℕ}
    (M : Matrix (Qubits k) (Qubits k) ℂ) (hM : M ∈ Matrix.unitaryGroup (Qubits k) ℂ)
    (wires : Fin k ↪ Fin n) : embedOp M wires ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  classical
  let Env := {j : Fin n // ¬ ∃ i : Fin k, wires i = j} → Bool
  let E := section5_out_equiv wires
  let H := M ⊗ₖ (1 : Matrix Env Env ℂ)
  have heq : embedOp M wires = H.submatrix E E := by
    ext y z
    have hr : (∀ j : Fin n, j ∉ Set.range wires → y j = z j) ↔ (E y).2 = (E z).2 := by
      simpa only [Set.mem_range, not_exists] using section5_out_equiv_rest wires y z
    change (if ∀ j : Fin n, j ∉ Set.range wires → y j = z j then M (y ∘ wires) (z ∘ wires) else 0) =
      M (y ∘ wires) (z ∘ wires) * (1 : Matrix Env Env ℂ) (E y).2 (E z).2
    rw [Matrix.one_apply]
    by_cases h : ∀ j : Fin n, j ∉ Set.range wires → y j = z j
    · rw [if_pos h, if_pos (hr.mp h), mul_one]
    · rw [if_neg h, if_neg (fun he => h (hr.mpr he)), mul_zero]
  rw [heq]
  exact Unitary.map_mem (section5_reindex_hom E.symm).toStarAlgHom
    (Matrix.kronecker_mem_unitary hM (one_mem _))

theorem section5_matrix_list_unitary {α : Type*} [Fintype α] [DecidableEq α]
    (l : List (Matrix α α ℂ)) (hl : ∀ U ∈ l, U ∈ Matrix.unitaryGroup α ℂ) :
    l.prod ∈ Matrix.unitaryGroup α ℂ := by
  induction l with
  | nil => exact one_mem _
  | cons U l ih =>
    exact mul_mem (hl U (List.mem_cons_self))
      (ih (fun A hA => hl A (List.mem_cons_of_mem U hA)))

theorem section5_circuit_unitary {S : Set Gate} (hS : ∀ g ∈ S, g.IsUnitary)
    {n : ℕ} (c : Circuit S n) : c.unitary ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  classical
  apply section5_matrix_list_unitary
  intro U hU
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hU)
  exact section5_embed_unitary g.gate.mat (hS g.gate g.mem) g.wires

theorem section5_uncontrolled_circuit_unitary {S : Set Gate} (hS : ∀ g ∈ S, g.IsUnitary)
    {r n : ℕ} {a : Fin r → ℕ} (c : OracleCircuit S a n) (hunc : Uncontrolled c)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (hU : ∀ k, orc k ∈ Matrix.unitaryGroup (Qubits (a k)) ℂ) :
    c.unitary orc ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  classical
  apply section5_matrix_list_unitary
  intro U hmem
  obtain ⟨st,hst,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hmem)
  cases st with
  | gate g => exact section5_embed_unitary _ (hS g.gate g.mem) _
  | query k adj ctrl wires hc =>
    have hctrl := hunc _ hst
    change ctrl = none at hctrl
    subst ctrl
    cases adj with
    | false => simpa [OracleStep.mat] using section5_embed_unitary (orc k) (hU k) wires
    | true => simpa [OracleStep.mat] using
        section5_embed_unitary (star (orc k)) (Unitary.star_mem (hU k)) wires

theorem section5_permutation_unitary {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) :
    (fun y z => if y = e z then (1:ℂ) else 0) ∈ Matrix.unitaryGroup α ℂ := by
  classical
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext y z
  change (∑ u : α, (if y = e u then (1:ℂ) else 0) *
    star (if z = e u then (1:ℂ) else 0)) = if y = z then 1 else 0
  rw [Finset.sum_eq_single (e.symm y)]
  · simp [eq_comm]
  · intro u hu hne
    have hh : y ≠ e u := by
      intro h
      exact hne (by rw [h, e.symm_apply_apply])
    rw [if_neg hh, zero_mul]
  · simp

def section5_bit_flip : Equiv.Perm (Qubits 1) where
  toFun z := fun _ => !(z 0)
  invFun z := fun _ => !(z 0)
  left_inv z := by funext i; fin_cases i; simp
  right_inv z := by funext i; fin_cases i; simp

def section5_cnot_perm : Equiv.Perm (Qubits 2) where
  toFun z := ![z 0, xor (z 1) (z 0)]
  invFun z := ![z 0, xor (z 1) (z 0)]
  left_inv z := by funext i; fin_cases i <;> simp
  right_inv z := by funext i; fin_cases i <;> simp

def section5_toffoli_perm : Equiv.Perm (Qubits 3) where
  toFun z := ![z 0, z 1, xor (z 2) (z 0 && z 1)]
  invFun z := ![z 0, z 1, xor (z 2) (z 0 && z 1)]
  left_inv z := by funext i; fin_cases i <;> simp
  right_inv z := by funext i; fin_cases i <;> simp

theorem section5_gatesRev_unitary : ∀ g ∈ gatesRev, g.IsUnitary := by
  classical
  have hx : (Gate.ofMatrix1 pauliX).IsUnitary := by
    have heq : (Gate.ofMatrix1 pauliX).mat =
        (fun y z => if y = section5_bit_flip z then (1:ℂ) else 0) := by
      change pauliX.submatrix (fun y : Qubits 1 => y 0) (fun z : Qubits 1 => z 0) = _
      ext y z
      have hh : y = section5_bit_flip z ↔ y 0 = !(z 0) := by
        constructor
        · intro h; exact congrFun h 0
        · intro h; funext i; fin_cases i; exact h
      change (if y 0 = z 0 then (0:ℂ) else 1) = _
      simp only [hh]
      cases hy : y 0 <;> cases hz : z 0 <;> simp [hy,hz]
    rw [Gate.IsUnitary, heq]
    exact section5_permutation_unitary section5_bit_flip
  have hc : (Gate.ofMatrix2 cnot).IsUnitary := by
    have heq : (Gate.ofMatrix2 cnot).mat =
        (fun y z => if y = section5_cnot_perm z then (1:ℂ) else 0) := by
      change cnot.submatrix (fun y : Qubits 2 => (y 0,y 1))
        (fun z : Qubits 2 => (z 0,z 1)) = _
      ext y z
      have hh : y = section5_cnot_perm z ↔ y 0 = z 0 ∧ y 1 = xor (z 1) (z 0) := by
        constructor
        · intro h
          exact ⟨congrFun h 0, congrFun h 1⟩
        · intro h; funext i; fin_cases i
          · exact h.1
          · exact h.2
      change (if y 0 = z 0 ∧ y 1 = xor (z 1) (z 0) then (1:ℂ) else 0) = _
      simp only [hh]
    rw [Gate.IsUnitary, heq]
    exact section5_permutation_unitary section5_cnot_perm
  have ht : (⟨3, Matrix.of fun y z =>
      if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) then 1 else 0⟩ : Gate).IsUnitary := by
    have heq : (Matrix.of fun y z : Qubits 3 =>
        if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) then (1:ℂ) else 0) =
        (fun y z => if y = section5_toffoli_perm z then (1:ℂ) else 0) := by
      ext y z
      have hh : y = section5_toffoli_perm z ↔
          y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) := by
        constructor
        · intro h
          exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
        · intro h; funext i; fin_cases i
          · exact h.1
          · exact h.2.1
          · exact h.2.2
      change (if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1)
        then (1:ℂ) else 0) = _
      simp only [hh]
    change (Matrix.of fun y z : Qubits 3 =>
      if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) then (1:ℂ) else 0) ∈ _
    rw [heq]
    exact section5_permutation_unitary section5_toffoli_perm
  intro g hg
  simp only [gatesRev, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact hx
  · exact hc
  · exact ht

theorem solution {r n : ℕ} {a : Fin r → ℕ}
    (cq : OracleCircuit gates12 a n) (hunc : Uncontrolled cq) (pp : Circuit gatesRev n)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (hU : ∀ k, orc k ∈ Matrix.unitaryGroup (Qubits (a k)) ℂ) :
    pp.unitary * cq.unitary orc ∈ Matrix.unitaryGroup (Qubits n) ℂ :=
  mul_mem (section5_circuit_unitary section5_gatesRev_unitary pp)
    (section5_uncontrolled_circuit_unitary (fun _ hg => hg.1) cq hunc orc hU)

