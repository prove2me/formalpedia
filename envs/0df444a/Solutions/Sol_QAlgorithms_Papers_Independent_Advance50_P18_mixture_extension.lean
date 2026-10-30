-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P18.mixture_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:57:46.692351+00:00
-- url     : https://prove2.me/submissions/7ef868d2-19f2-472a-8cd6-4fc8ef71ad46

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P18
namespace QAlgorithms.Papers.Independent.Advance50.P18

open scoped ComplexConjugate

noncomputable section

variable {K I A : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

theorem s110p18_encrypt_sum {n : ℕ} (E : KeyedUnitaryEnsemble K I) (c : Fin n → ℂ)
    (X : Fin n → Matrix I I ℂ) :
    encrypt E (∑ j, c j • X j) = ∑ j, c j • encrypt E (X j) := by
  unfold encrypt
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [mul_comm]

theorem s110p18_kron_sum {n : ℕ} (c : Fin n → ℂ) (X : Fin n → Matrix I I ℂ) (anc : Matrix A A ℂ) :
    Matrix.kronecker (∑ j, c j • X j) anc = ∑ j, c j • Matrix.kronecker (X j) anc := by
  ext a b
  simp [Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_mul, mul_assoc]

end

end QAlgorithms.Papers.Independent.Advance50.P18

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P18

theorem solution (n a N : ℕ) (S : Set ((EuclideanSpace ℂ (Qubits n))))
    (E : KeyedUnitaryEnsemble (Fin N) (Qubits n × Qubits a))
    (anc : (Matrix (Qubits a) (Qubits a) ℂ)) (rho0 : (Matrix (Qubits n × Qubits a) (Qubits n × Qubits a) ℂ))
    (h : PQC S E anc rho0) (rho : (Matrix (Qubits n) (Qubits n) ℂ)) (hmix : IsSourceMixture S rho) :
    encrypt E (Matrix.kronecker rho anc) = rho0 ∧
    ∀ i : Fin N, (E.U i).conjTranspose *
      (E.U i * Matrix.kronecker rho anc * (E.U i).conjTranspose) * E.U i =
        Matrix.kronecker rho anc := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, q, psi, -, hq, hpsi, rfl⟩ := hmix
    rw [s110p18_kron_sum, s110p18_encrypt_sum]
    have : ∀ j, encrypt E (Matrix.kronecker (pureDensity (psi j)) anc) = rho0 :=
      fun j => (h.2.2.2 _ (hpsi j).1).2
    simp only [this, ← Finset.sum_smul]
    rw [← Complex.ofReal_sum, hq]; simp
  · intro i
    have hu := Matrix.mem_unitaryGroup_iff.mp (h.1.2.2 i)
    have hu' := Matrix.mem_unitaryGroup_iff'.mp (h.1.2.2 i)
    change star (E.U i) * (E.U i * _ * star (E.U i)) * E.U i = _
    simp only [Matrix.mul_assoc, hu', Matrix.mul_one]
    rw [← Matrix.mul_assoc, hu', Matrix.one_mul]
