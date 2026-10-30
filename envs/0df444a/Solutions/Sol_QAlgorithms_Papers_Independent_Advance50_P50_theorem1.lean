-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:19:37.557984+00:00
-- url     : https://prove2.me/submissions/daea9b91-1af5-4155-94cd-1270b284eeb2

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

theorem s110k_response_eq {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (M : ExpectationModel I k) (rho : Mat I) :
    M.response rho = (tensorPower k rho * M.effective).trace.re := by
  unfold ExpectationModel.response ExpectationModel.effective
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

open scoped ComplexOrder in
theorem s110t_basis_density {n : ℕ} (b : ℝ) (i : Qubits n) :
    Matrix.diagonal (fun a => if a = i then (1:ℂ) else 0) ∈ purityDomain b := by
  refine ⟨⟨?_, ?_⟩, Or.inl ?_⟩
  · rw [Matrix.posSemidef_diagonal_iff]
    intro a; split_ifs <;> norm_num
  · rw [Matrix.trace_diagonal]; simp
  · simp only [purity, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp

theorem s110t_trace_basis {n : ℕ} (i : Qubits n) (X : Mat (Qubits n)) :
    (Matrix.diagonal (fun a => if a = i then (1:ℂ) else 0) * X).trace = X i i := by
  simp [Matrix.trace, Matrix.diagonal_mul]

def s110t_E {n : ℕ} (M : ExpectationModel (Qubits n) 1) : Mat (Qubits n) :=
  fun x y => M.effective (fun _ => x) (fun _ => y)

theorem s110t_resp1 {n : ℕ} (M : ExpectationModel (Qubits n) 1) (rho : Mat (Qubits n)) :
    M.response rho = (rho * s110t_E M).trace.re := by
  rw [s110k_response_eq]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, tensorPower, Fin.prod_univ_one]
  rw [← (Equiv.funUnique (Fin 1) (Qubits n)).symm.sum_comp]
  refine Fintype.sum_congr _ _ (fun x => ?_)
  rw [← (Equiv.funUnique (Fin 1) (Qubits n)).symm.sum_comp]
  rfl

theorem s110t_key {n : ℕ} (b : ℝ) (M : ExpectationModel (Qubits n) 1)
    (hinv : DomainInvariant (Matrix.unitaryGroup (Qubits n) ℂ : Set (Mat (Qubits n)))
      (purityDomain b) M.response)
    (U : Mat (Qubits n)) (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (i : Qubits n) :
    ((U.conjTranspose * s110t_E M * U) i i).re = (s110t_E M i i).re := by
  have h := hinv U hU _ (s110t_basis_density b i)
  rw [s110t_resp1, s110t_resp1] at h
  rw [s110t_trace_basis] at h
  rw [← h, ← s110t_trace_basis i (U.conjTranspose * s110t_E M * U)]
  simp only [conjSuperop]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm U]
  simp only [Matrix.mul_assoc]

theorem s110t_perm {n : ℕ} (E : Mat (Qubits n)) (i j : Qubits n) :
    ∃ V ∈ Matrix.unitaryGroup (Qubits n) ℂ, (V.conjTranspose * E * V) i i = E j j := by
  let σ := Equiv.swap i j
  let V : Mat (Qubits n) := Matrix.of fun a b => if a = σ b then (1:ℂ) else 0
  refine ⟨V, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext a b
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply, V,
      Matrix.one_apply, Matrix.of_apply]
    simp [apply_ite (star : ℂ → ℂ), ite_mul, Finset.sum_ite_eq', σ.injective.eq_iff, eq_comm]
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.of_apply]
    simp [apply_ite (star : ℂ → ℂ), ite_mul, mul_ite, Finset.sum_ite_eq', σ]

theorem s110t_obs_trace {n : ℕ} (M : ExpectationModel (Qubits n) 1) :
    M.observable.trace = (s110t_E M).trace := by
  have h1 : M.effective.trace = M.observable.trace := by
    unfold ExpectationModel.effective
    have hu := Matrix.mem_unitaryGroup_iff.mp M.unitary.2
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    rw [Matrix.star_eq_conjTranspose] at hu
    rw [hu, Matrix.mul_one]
  rw [← h1]
  simp only [Matrix.trace, Matrix.diag, s110t_E]
  rw [← (Equiv.funUnique (Fin 1) (Qubits n)).symm.sum_comp]
  rfl

end QAlgorithms.Papers.Independent.Advance50.P50

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P50
open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped ComplexOrder in
theorem solution {n : ℕ} (hn : 1 ≤ n) (b : ℝ)
    (hb : 1 / (2 : ℝ) ^ n ≤ b ∧ b < 1)
    (hpure : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = 1)
    (hmixed : ∃ rho : Mat (Qubits n), IsDensityMatrix rho ∧ purity rho = b)
    (M : ExpectationModel (Qubits n) 1)
    (hinv : DomainInvariant (Matrix.unitaryGroup (Qubits n) ℂ : Set (Mat (Qubits n)))
      (purityDomain b) M.response) :
    ∀ rho ∈ purityDomain b, M.response rho = M.observable.trace.re / (2 : ℝ) ^ n := by
  intro rho hrho
  set E := s110t_E M with hEdef
  let i0 : Qubits n := fun _ => false
  set c := (E i0 i0).re with hc
  have hall : ∀ i, (E i i).re = c := by
    intro i
    obtain ⟨V, hV, hVe⟩ := s110t_perm E i0 i
    rw [← hVe, s110t_key b M hinv V hV i0]
  have hrhs : M.observable.trace.re / (2 : ℝ) ^ n = c := by
    rw [s110t_obs_trace, Matrix.trace, Complex.re_sum]
    simp only [Matrix.diag, ← hEdef, hall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    field_simp
  rw [hrhs, s110t_resp1]
  have hD := hrho.1
  have hH : rho.IsHermitian := hD.1.isHermitian
  have hsum : ∑ k, hH.eigenvalues k = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [hD.2] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  set U : Mat (Qubits n) := (hH.eigenvectorUnitary : Mat (Qubits n)) with hU
  have hUmem : U ∈ Matrix.unitaryGroup (Qubits n) ℂ := hH.eigenvectorUnitary.2
  have hspec : rho = U * Matrix.diagonal (fun k => (hH.eigenvalues k : ℂ)) * U.conjTranspose := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have htr : (rho * E).trace = ∑ k, (hH.eigenvalues k : ℂ) * (U.conjTranspose * E * U) k k := by
    have : (U * Matrix.diagonal (fun k => (hH.eigenvalues k : ℂ)) * U.conjTranspose * E).trace
        = (Matrix.diagonal (fun k => (hH.eigenvalues k : ℂ)) * (U.conjTranspose * E * U)).trace := by
      rw [Matrix.trace_mul_comm (Matrix.diagonal _)]
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm U]
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm (Matrix.diagonal _)]
      simp only [Matrix.mul_assoc]
    rw [← hspec] at this
    rw [this]
    simp [Matrix.trace, Matrix.diagonal_mul]
  rw [htr, Complex.re_sum]
  have hk : ∀ k, ((U.conjTranspose * E * U) k k).re = c :=
    fun k => (s110t_key b M hinv U hUmem k).trans (hall k)
  simp only [Complex.re_ofReal_mul, hk]
  rw [← Finset.sum_mul, hsum, one_mul]
