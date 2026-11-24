-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.probMixed_pad_stability
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T19:24:57.925862+00:00
-- url     : https://prove2.me/submissions/159a6ff0-0d06-41a9-9887-874db416d57d

import Mathlib
import Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_trace_norm_contraction
import Definitions.Def_QuantumLTF_Membership_Supplement_padDensity
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed

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
set_option linter.unusedSimpArgs false

open QAlgorithms
open scoped Matrix ComplexOrder MatrixOrder

noncomputable def section5_event_linear {α β : Type*} [Fintype α] [Fintype β]
    (B : Matrix β α ℂ) (P : β → Prop) [DecidablePred P] :
    Matrix α α ℂ →ₗ[ℂ] ℂ where
  toFun A := ∑ z ∈ Finset.univ.filter P, (B * A * B.conjTranspose) z z
  map_add' A C := by
    simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum]

noncomputable def section5_binary_measurement {α β : Type*} [Fintype α] [Fintype β]
    (B : Matrix β α ℂ) (P : β → Prop) [DecidablePred P] :
    Matrix α α ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ := by
  classical
  let f := section5_event_linear B P
  let g := section5_event_linear B (fun z => ¬ P z)
  exact
    { toFun := fun A => Matrix.diagonal ![f A, g A]
      map_add' := by intro A C; ext i j; fin_cases i <;> fin_cases j <;> simp
      map_smul' := by intro c A; ext i j; fin_cases i <;> fin_cases j <;> simp }

theorem section5_event_complement {α β : Type*} [Fintype α] [Fintype β]
    (B : Matrix β α ℂ) (P : β → Prop) [DecidablePred P] (A : Matrix α α ℂ) :
    section5_event_linear B P A + section5_event_linear B (fun z => ¬ P z) A =
      (B * A * B.conjTranspose).trace := by
  classical
  exact Finset.sum_filter_add_sum_filter_not Finset.univ _ _

theorem section5_binary_measurement_positive {α β : Type*} [Fintype α] [Fintype β]
    (B : Matrix β α ℂ) (P : β → Prop) [DecidablePred P] :
    QAlgorithms.Papers.Independent.Information100.P30.IsPositiveMap
      (section5_binary_measurement B P) := by
  classical
  intro A hA
  apply Matrix.PosSemidef.diagonal
  intro i
  have hBA := hA.mul_mul_conjTranspose_same B
  fin_cases i <;>
    exact Finset.sum_nonneg (fun z _ => hBA.diag_nonneg)

theorem section5_binary_measurement_trace {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (B : Matrix β α ℂ) (P : β → Prop) [DecidablePred P]
    (hB : B.conjTranspose * B = 1) :
    QAlgorithms.Papers.Independent.Dependency50.P26.TracePreserving
      (section5_binary_measurement B P) := by
  classical
  intro A
  change (Matrix.diagonal ![section5_event_linear B P A,
    section5_event_linear B (fun z => ¬ P z) A]).trace = A.trace
  simp only [Matrix.trace_diagonal, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [section5_event_complement, Matrix.trace_mul_cycle, hB, one_mul]

theorem section5_event_real {α β : Type*} [Fintype α] [Fintype β]
    (B : Matrix β α ℂ) (P : β → Prop) [DecidablePred P]
    (A : Matrix α α ℂ) (hA : A.IsHermitian) :
    ((section5_event_linear B P A).re : ℂ) = section5_event_linear B P A := by
  classical
  have hBA : (B * A * B.conjTranspose).IsHermitian := by
    change (B * A * B.conjTranspose).conjTranspose = _
    simp [Matrix.conjTranspose_mul, hA.eq, Matrix.mul_assoc]
  change ((∑ z ∈ Finset.univ.filter P, (B * A * B.conjTranspose) z z).re : ℂ) = _
  simp only [Complex.re_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact Complex.conj_eq_iff_re.mp (hBA.apply z z)

theorem section5_isometry_event_trace_bound {d : ℕ} {β : Type*} [Fintype β]
    (hd : 0 < d) (B : Matrix β (Fin d) ℂ) (hB : B.conjTranspose * B = 1)
    (P : β → Prop) [DecidablePred P] (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (ht : A.trace = 0) :
    |(section5_event_linear B P A).re| ≤ traceNorm A / 2 := by
  classical
  let p : ℝ := (section5_event_linear B P A).re
  have hp := section5_event_real B P A hA
  have hz : section5_event_linear B P A + section5_event_linear B (fun z => ¬ P z) A = 0 := by
    rw [section5_event_complement, Matrix.trace_mul_cycle, hB, one_mul, ht]
  have hg : section5_event_linear B (fun z => ¬ P z) A = -(p:ℂ) := by
    rw [hp]
    linear_combination hz
  have hmat : section5_binary_measurement B P A = Matrix.diagonal
      (fun i : Fin 2 => if i = 0 then (p:ℂ) else -(p:ℂ)) := by
    change Matrix.diagonal ![section5_event_linear B P A,
      section5_event_linear B (fun z => ¬ P z) A] = _
    congr 1
    funext i
    fin_cases i
    · change section5_event_linear B P A = (p:ℂ)
      exact hp.symm
    · simp [hg]
  have hnorm : traceNorm (section5_binary_measurement B P A) = 2 * |p| := by
    rw [hmat]
    change (cfc Real.sqrt ((Matrix.diagonal (fun i : Fin 2 => if i = 0 then (p:ℂ) else -(p:ℂ))).conjTranspose *
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then (p:ℂ) else -(p:ℂ)))).trace.re = _
    have he : (fun i : Fin 2 => if i = 0 then (p:ℂ) else -(p:ℂ)) =
        (fun i : Fin 2 => ((if i = 0 then p else -p : ℝ) : ℂ)) := by
      funext i
      split_ifs <;> simp
    rw [he]
    rw [section5_trace_size_diagonal]
    simp [Fin.sum_univ_two, two_mul]
  have hc := (QAlgorithms.Papers.Independent.Frontier30.P28.trace_norm_contraction
    d 2 hd (by norm_num) (section5_binary_measurement B P)
    (section5_binary_measurement_positive B P) (section5_binary_measurement_trace B P hB)).2 A
  rw [hnorm] at hc
  dsimp [p] at hc
  linarith

theorem section5_isometry_event_trace_bound_general {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [Nonempty α]
    (B : Matrix β α ℂ) (hB : B.conjTranspose * B = 1)
    (P : β → Prop) [DecidablePred P] (A : Matrix α α ℂ)
    (hA : A.IsHermitian) (ht : A.trace = 0) :
    |(section5_event_linear B P A).re| ≤ traceNorm A / 2 := by
  classical
  let e := (Fintype.equivFin α).symm
  let B' := B.submatrix (Equiv.refl β) e
  let A' := A.submatrix e e
  have hB' : B'.conjTranspose * B' = 1 := by
    change (B.conjTranspose * B).submatrix e e = 1
    rw [hB]
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff]
  have hm : B' * A' * B'.conjTranspose = B * A * B.conjTranspose := by
    change B.submatrix (Equiv.refl β) e * A.submatrix e e *
      B.conjTranspose.submatrix e (Equiv.refl β) = _
    rw [Matrix.submatrix_mul_equiv B A (Equiv.refl β) e e,
      Matrix.submatrix_mul_equiv (B*A) B.conjTranspose (Equiv.refl β) e (Equiv.refl β)]
    rfl
  have ht' : A'.trace = 0 := by
    change (∑ i, A (e i) (e i)) = 0
    exact (Equiv.sum_comp e (fun i : α => A i i)).trans ht
  have hn : traceNorm A' = traceNorm A := section5_trace_size_reindex e.symm A
  have hh := section5_isometry_event_trace_bound (Fintype.card_pos)
    B' hB' P A' (hA.submatrix e) ht'
  simpa only [section5_event_linear, LinearMap.coe_mk, AddHom.coe_mk, hm, hn] using hh

noncomputable def section5_injection_matrix {α β : Type*} [DecidableEq β]
    (e : α ↪ β) : Matrix β α ℂ := fun z x => if z = e x then 1 else 0

theorem section5_injection_matrix_isometry {α β : Type*} [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ↪ β) :
    (section5_injection_matrix e).conjTranspose * section5_injection_matrix e = 1 := by
  ext a b
  simp [section5_injection_matrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, e.injective.eq_iff, eq_comm]

def section5_zero_append (N a : ℕ) : Qubits N ↪ Qubits (N+a) where
  toFun x := Fin.append x (fun _ => false)
  inj' := by
    intro x y h
    funext i
    simpa using congrFun h (Fin.castAdd a i)

theorem section5_pad_density_matrix {N a : ℕ} (ρ : Matrix (Qubits N) (Qubits N) ℂ) :
    QuantumLTF.Membership.Supplement.padDensity a ρ =
      section5_injection_matrix (section5_zero_append N a) * ρ *
        (section5_injection_matrix (section5_zero_append N a)).conjTranspose := by
  classical
  have heq (z : Qubits (N+a)) (x : Qubits N) :
      z = Fin.append x (fun _ : Fin a => false) ↔
      (fun i => z (Fin.castAdd a i)) = x ∧ ∀ j : Fin a, z (Fin.natAdd N j) = false := by
    constructor
    · intro h
      subst z
      simp
    · rintro ⟨hx, ht⟩
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using congrFun hx j
      · simpa using ht j
  ext z z'
  change (if (∀ j : Fin a, z (Fin.natAdd N j) = false) ∧
      (∀ j : Fin a, z' (Fin.natAdd N j) = false) then
      ρ (fun i => z (Fin.castAdd a i)) (fun i => z' (Fin.castAdd a i)) else 0) =
    ∑ b : Qubits N, (∑ c : Qubits N,
      (if z = Fin.append c (fun _ : Fin a => false) then (1:ℂ) else 0) * ρ c b) *
      star (if z' = Fin.append b (fun _ : Fin a => false) then (1:ℂ) else 0)
  by_cases hz : ∀ j : Fin a, z (Fin.natAdd N j) = false <;>
    by_cases hz' : ∀ j : Fin a, z' (Fin.natAdd N j) = false <;>
    simp [heq, hz, hz']

theorem solution {N a : ℕ}
    (U : Matrix (Qubits (N+a)) (Qubits (N+a)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits (N+a)) ℂ)
    (ρ σ : Matrix (Qubits N) (Qubits N) ℂ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (ht : ρ.trace = σ.trace)
    (P : Qubits (N+a) → Prop) [DecidablePred P] :
    |QuantumLTF.Membership.Supplement.probMixed U
        (QuantumLTF.Membership.Supplement.padDensity a ρ) P -
      QuantumLTF.Membership.Supplement.probMixed U
        (QuantumLTF.Membership.Supplement.padDensity a σ) P| ≤ traceNorm (ρ-σ) / 2 := by
  classical
  let J := section5_injection_matrix (section5_zero_append N a)
  let B := U * J
  have hUs : U.conjTranspose * U = 1 := by
    simpa only [star_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      using Matrix.mem_unitaryGroup_iff.mp (Unitary.star_mem hU)
  have hB : B.conjTranspose * B = 1 := by
    dsimp [B]
    rw [Matrix.conjTranspose_mul]
    calc
      J.conjTranspose * U.conjTranspose * (U * J) = J.conjTranspose * (U.conjTranspose * U) * J := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUs, Matrix.mul_one]; exact section5_injection_matrix_isometry _
  have hmat (τ : Matrix (Qubits N) (Qubits N) ℂ) :
      U * QuantumLTF.Membership.Supplement.padDensity a τ * U.conjTranspose =
        B * τ * B.conjTranspose := by
    rw [section5_pad_density_matrix]
    simp [B, J, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hp (τ : Matrix (Qubits N) (Qubits N) ℂ) :
      QuantumLTF.Membership.Supplement.probMixed U
        (QuantumLTF.Membership.Supplement.padDensity a τ) P =
      (section5_event_linear B P τ).re := by
    simp only [QuantumLTF.Membership.Supplement.probMixed, hmat, section5_event_linear,
      LinearMap.coe_mk, AddHom.coe_mk, Complex.re_sum]
  rw [hp, hp, ← Complex.sub_re, ← map_sub]
  exact section5_isometry_event_trace_bound_general B hB P (ρ-σ) (hρ.sub hσ)
    (by rw [Matrix.trace_sub, ht, sub_self])
