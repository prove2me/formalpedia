-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.noiseFactorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:52:55.722717+00:00
-- url     : https://prove2.me/submissions/d25d00b1-537e-47ac-8c05-4c6d3d2d9621

import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
set_option autoImplicit false

noncomputable section
open scoped Matrix ComplexOrder NNReal ENNReal
open QAlgorithms QAlgorithms.ErrorMitigation QAlgorithms.Papers.Independent.Independent1.P09

theorem solution {n : ℕ} (U : Matrix.unitaryGroup (Qubits n) ℂ)
    (G : Superop (Qubits n) (Qubits n)) (hG : IsChannel G) :
    let before : Superop (Qubits n) (Qubits n) := id
    let after := G ∘ conjSuperop (star (U : Matrix (Qubits n) (Qubits n) ℂ))
    IsChannel before ∧ IsChannel after ∧
    G = after ∘ conjSuperop (U : Matrix (Qubits n) (Qubits n) ℂ) ∘ before := by
  classical
  dsimp only
  simp only [Matrix.star_eq_conjTranspose]
  have hu : (U : Matrix (Qubits n) (Qubits n) ℂ) *
      (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem U.property
  have hv : (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ *
      (U : Matrix (Qubits n) (Qubits n) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mul_self_of_mem U.property
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨1, fun _ => 1, by simp [IsKrausFamily], fun X => by simp [krausApply]⟩
  · obtain ⟨m, E, hE, hmap⟩ := hG
    refine ⟨m, fun j => E j * (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ, ?_, ?_⟩
    · change (∑ j, (E j * (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ)ᴴ *
          (E j * (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ)) = 1
      calc
        _ = (U : Matrix (Qubits n) (Qubits n) ℂ) * (∑ j, (E j)ᴴ * E j) *
            (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]
        _ = 1 := by rw [hE, Matrix.mul_one, hu]
    · intro X
      simp only [Function.comp_apply, conjSuperop, hmap, krausApply,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.mul_assoc]
  · funext X
    simp only [Function.comp_apply, id_eq, conjSuperop]
    simp only [Matrix.conjTranspose_conjTranspose]
    symm
    congr 1
    change ((U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ *
      ((U : Matrix (Qubits n) (Qubits n) ℂ) * X * (U : Matrix (Qubits n) (Qubits n) ℂ)ᴴ)) *
      (U : Matrix (Qubits n) (Qubits n) ℂ) = X
    simp only [← Matrix.mul_assoc, hv, Matrix.one_mul]
    rw [Matrix.mul_assoc, hv, Matrix.mul_one]

#print axioms solution
