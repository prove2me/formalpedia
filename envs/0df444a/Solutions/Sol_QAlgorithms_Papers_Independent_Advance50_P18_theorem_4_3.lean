-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P18.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:56:53.93698+00:00
-- url     : https://prove2.me/submissions/779cde91-0e53-4101-9342-728e4d4adae8

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

theorem s110p18_encrypt_mix (S : Set (EuclideanSpace ℂ I)) (E : KeyedUnitaryEnsemble K I)
    (rho0 rho : Matrix I I ℂ) (h : BarePQC S E rho0) (hmix : IsSourceMixture S rho) :
    encrypt E rho = rho0 := by
  obtain ⟨r, q, psi, -, hq, hpsi, rfl⟩ := hmix
  rw [s110p18_encrypt_sum]
  have : ∀ j, encrypt E (pureDensity (psi j)) = rho0 := fun j => (h.2.2 _ (hpsi j).1).2
  simp only [this, ← Finset.sum_smul]
  rw [← Complex.ofReal_sum, hq]; simp

theorem s110p18_encrypt_id (E : KeyedUnitaryEnsemble K I) (hE : E.Valid) (c : ℂ) :
    encrypt E (c • (1 : Matrix I I ℂ)) = c • 1 := by
  unfold encrypt
  have : ∀ k, E.U k * (c • (1 : Matrix I I ℂ)) * (E.U k).conjTranspose = c • 1 := by
    intro k
    have hu := Matrix.mem_unitaryGroup_iff.mp (hE.2.2 k)
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [show (E.U k).conjTranspose = star (E.U k) from rfl, hu]
  simp only [this, smul_smul, ← Finset.sum_smul]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, hE.2.1]; simp

end

end QAlgorithms.Papers.Independent.Advance50.P18

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P18

theorem solution (n N : ℕ) (S : Set ((EuclideanSpace ℂ (Qubits n))))
    (E : KeyedUnitaryEnsemble (Fin N) (Qubits n)) (rho0 : (Matrix (Qubits n) (Qubits n) ℂ))
    (h : BarePQC S E rho0) (hmix : IsSourceMixture S (sourceMixedIdentity (Qubits n))) :
    rho0 = sourceMixedIdentity (Qubits n) := by
  rw [← s110p18_encrypt_mix S E rho0 _ h hmix]
  exact s110p18_encrypt_id E h.1 _
