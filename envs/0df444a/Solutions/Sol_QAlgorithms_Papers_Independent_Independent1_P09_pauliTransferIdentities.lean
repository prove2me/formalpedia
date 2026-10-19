-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.pauliTransferIdentities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:40:45.290122+00:00
-- url     : https://prove2.me/submissions/afb4c39e-0fe2-4852-9214-abec89f44cab

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
noncomputable section
open QAlgorithms QAlgorithms.ErrorMitigation QAlgorithms.Stabilizer
open scoped Matrix ComplexConjugate ComplexOrder

private lemma local_complete (a b c d : Bool) :
    (∑ p : Pauli, p.mat a b * p.mat c d) =
      if a = d ∧ b = c then (2 : ℂ) else 0 := by
  change (∑ p ∈ ({Pauli.I, Pauli.X, Pauli.Y, Pauli.Z} : Finset Pauli),
    p.mat a b * p.mat c d) = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [Pauli.mat, pauliX, pauliY, pauliZ, Matrix.one_apply]

private lemma pauli_entry {n : ℕ} (p : PauliIndex n) (a b : Qubits n) :
    pauliOps p a b = ∏ j, (p j).mat (a j) (b j) := by
  simp [pauliOps, PauliString.toMatrix]

private lemma tensor_complete {n : ℕ} (a b c d : Qubits n) :
    (∑ p : PauliIndex n, pauliOps p a b * pauliOps p c d) =
      if a = d ∧ b = c then (2 : ℂ)^n else 0 := by
  simp_rw [pauli_entry, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : Fin n) (p : Pauli) =>
    p.mat (a j) (b j) * p.mat (c j) (d j))]
  simp_rw [local_complete]
  by_cases h : a = d ∧ b = c
  · rcases h with ⟨rfl,rfl⟩
    simp
  · rw [if_neg h]
    have h' : ∃ j, ¬ (a j = d j ∧ b j = c j) := by
      by_contra! hh
      exact h ⟨funext fun j => (hh j).1, funext fun j => (hh j).2⟩
    obtain ⟨j,hj⟩ := h'
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

private lemma reconstruction_complex {n : ℕ} (X : Matrix (Qubits n) (Qubits n) ℂ) :
    (∑ p : PauliIndex n, (pauliOps p * X).trace • pauliOps p) = (2 : ℂ)^n • X := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  calc
    _ = ∑ c, ∑ d, (∑ p : PauliIndex n, pauliOps p a b * pauliOps p c d) * X d c := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      simp_rw [tensor_complete]
      simp [ite_and]

private lemma pauli_hermitian {n : ℕ} (p : PauliIndex n) : (pauliOps p).IsHermitian := by
  have local_conj (q : Pauli) (a b : Bool) : star (q.mat b a) = q.mat a b := by
    cases q <;> cases a <;> cases b <;>
      simp [Pauli.mat, pauliX, pauliY, pauliZ]
  ext a b
  simp only [Matrix.conjTranspose_apply, pauli_entry, star_prod, local_conj]

private lemma trace_real {I : Type*} [Fintype I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((A*B).trace.re : ℂ) = (A*B).trace := by
  have h : star (A*B).trace = (A*B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  have hi : (A*B).trace.im = 0 := by
    have hh := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at hh
    linarith
  exact Complex.ext (by simp) (by simpa using hi.symm)

private lemma reconstruction {n : ℕ} (X : Matrix (Qubits n) (Qubits n) ℂ)
    (hX : X.IsHermitian) :
    X = ∑ p : PauliIndex n,
      ((((2 : ℝ)^n)⁻¹ * pauliStateVector X p : ℝ) : ℂ) • pauliOps p := by
  have h := reconstruction_complex X
  have hreal (p : PauliIndex n) : (pauliOps p * X).trace =
      (pauliStateVector X p : ℂ) := (trace_real _ X (pauli_hermitian p) hX).symm
  simp_rw [hreal] at h
  have hc : ((2 : ℂ)^n) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    X = (((2 : ℂ)^n)⁻¹) • ((2 : ℂ)^n • X) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = _ := by
      rw [← h, Finset.smul_sum]
      simp only [smul_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
        Complex.ofReal_ofNat, pauliStateVector]


private lemma transfer_action {n : ℕ}
    (O : Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ] Matrix (Qubits n) (Qubits n) ℂ)
    (X : Matrix (Qubits n) (Qubits n) ℂ) (hX : X.IsHermitian) :
    pauliStateVector (O X) = (pauliTransferMatrix O).mulVec (pauliStateVector X) := by
  funext p
  have h := congrArg (fun Y => (pauliOps p * O Y).trace.re) (reconstruction X hX)
  change (pauliOps p * O X).trace.re = _
  rw [h]
  simp only [map_sum, map_smul, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change (∑ q, (((2 : ℝ)^n)⁻¹ * pauliStateVector X q) *
    (pauliOps p * O (pauliOps q)).trace.re) =
    ∑ q, (((2 : ℝ)^n)⁻¹ * (pauliOps p * O (pauliOps q)).trace.re) * pauliStateVector X q
  apply Finset.sum_congr rfl
  intro q _
  ring

private lemma observable_pairing {n : ℕ}
    (Q X : Matrix (Qubits n) (Qubits n) ℂ) (hX : X.IsHermitian) :
    (Q*X).trace.re = pauliObservableRow Q ⬝ᵥ pauliStateVector X := by
  have h := congrArg (fun Y => (Q*Y).trace.re) (reconstruction X hX)
  rw [h]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change (∑ p, (((2 : ℝ)^n)⁻¹ * pauliStateVector X p) * (Q*pauliOps p).trace.re) = _
  unfold dotProduct pauliObservableRow
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.trace_mul_comm Q]
  ring

private lemma kraus_hermitian {n r : ℕ}
    (K : Fin r → Matrix (Qubits n) (Qubits n) ℂ)
    (X : Matrix (Qubits n) (Qubits n) ℂ) (hX : X.IsHermitian) :
    (krausLinearMap K X).IsHermitian := by
  change (∑ j, K j*X*(K j)ᴴ)ᴴ = ∑ j, K j*X*(K j)ᴴ
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]

private lemma chronological {n : ℕ}
    (L : List (Matrix (Qubits n) (Qubits n) ℂ →ₗ[ℂ] Matrix (Qubits n) (Qubits n) ℂ))
    (hL : ∀ O ∈ L, ∀ X, X.IsHermitian → (O X).IsHermitian)
    (X : Matrix (Qubits n) (Qubits n) ℂ) (hX : X.IsHermitian) :
    (L.foldl (fun Y O => O Y) X).IsHermitian ∧
    pauliStateVector (L.foldl (fun Y O => O Y) X) =
      ((L.map pauliTransferMatrix).reverse.prod).mulVec (pauliStateVector X) := by
  induction L generalizing X with
  | nil => simpa using hX
  | cons O L ih =>
    have hO := hL O (by simp) X hX
    have ht := ih (fun P hP => hL P (by simp [hP])) (O X) hO
    refine ⟨ht.1, ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.reverse_cons,
      List.prod_append, List.prod_singleton]
    rw [← Matrix.mulVec_mulVec, ← transfer_action O X hX]
    exact ht.2

theorem solution {n t : ℕ}
    (rho Q : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsDensityMatrix rho)
    (hQ : Q.IsHermitian) (r : Fin t → ℕ)
    (K : (j : Fin t) → Fin (r j) → Matrix (Qubits n) (Qubits n) ℂ) :
    let maps := fun j => krausLinearMap (K j)
    let final := (List.ofFn maps).foldl (fun X O => O X) rho
    pauliStateVector final =
      ((List.ofFn fun j => pauliTransferMatrix (maps j)).reverse.prod).mulVec
        (pauliStateVector rho) ∧
    (Q * final).trace.re = pauliObservableRow Q ⬝ᵥ
      (((List.ofFn fun j => pauliTransferMatrix (maps j)).reverse.prod).mulVec
        (pauliStateVector rho)) := by
  dsimp only
  have hL : ∀ O ∈ (List.ofFn fun j => krausLinearMap (K j)),
      ∀ X, X.IsHermitian → (O X).IsHermitian := by
    intro O hO
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hO
    exact kraus_hermitian (K j)
  have h := chronological (List.ofFn fun j => krausLinearMap (K j)) hL rho hrho.1.isHermitian
  simp only [List.map_ofFn, Function.comp_def] at h
  refine ⟨h.2, ?_⟩
  rw [← h.2]
  exact observable_pairing Q _ h.1

#print axioms solution
