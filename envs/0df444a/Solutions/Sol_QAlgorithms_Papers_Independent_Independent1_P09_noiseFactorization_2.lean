-- Prove2me | solution 2 for QAlgorithms.Papers.Independent.Independent1.P09.noiseFactorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:53:07.923009+00:00
-- url     : https://prove2.me/submissions/d0056a52-f316-4e04-977b-ba3ed4249a2b

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MitigationTrials
import Definitions.Def_QAlgorithms_Defs_MitigationTomography
import Definitions.Def_QAlgorithms_Defs_MitigationDecompositions
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
set_option autoImplicit false

/-! Endo, Benjamin and Li, arXiv:1712.09271v2; citations use PDF pages.
Source defects and construction deferrals are recorded in the assigned chunk. -/

noncomputable section

open scoped Matrix ComplexOrder NNReal ENNReal

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P09
open ErrorMitigation

/-- PDF p.16, Appendix H: explicit before/after channel factorization around ideal unitary. -/


theorem solution {n : ℕ} (U : Matrix.unitaryGroup (Qubits n) ℂ)
    (G : Superop (Qubits n) (Qubits n)) (hG : IsChannel G) :
    let before : Superop (Qubits n) (Qubits n) := id
    let after := G ∘ conjSuperop (star (U : Matrix (Qubits n) (Qubits n) ℂ))
    IsChannel before ∧ IsChannel after ∧
    G = after ∘ conjSuperop (U : Matrix (Qubits n) (Qubits n) ℂ) ∘ before := by
  intro before after
  have hU1 : star (U : Matrix (Qubits n) (Qubits n) ℂ) * (U : Matrix (Qubits n) (Qubits n) ℂ) = 1 := U.2.1
  have hU2 : (U : Matrix (Qubits n) (Qubits n) ℂ) * star (U : Matrix (Qubits n) (Qubits n) ℂ) = 1 := U.2.2
  refine ⟨⟨1, fun _ => 1, by simp [IsKrausFamily], fun ρ => by simp [krausApply, before]⟩, ?_, ?_⟩
  · obtain ⟨m, E, hE, hGE⟩ := hG
    refine ⟨m, fun j => E j * star (U : Matrix (Qubits n) (Qubits n) ℂ), ?_, fun ρ => ?_⟩
    · unfold IsKrausFamily at hE ⊢
      simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star]
      have : ∑ j, (U : Matrix (Qubits n) (Qubits n) ℂ) * star (E j) * (E j * star (U : Matrix (Qubits n) (Qubits n) ℂ)) =
          (U : Matrix (Qubits n) (Qubits n) ℂ) * (∑ j, star (E j) * E j) * star (U : Matrix (Qubits n) (Qubits n) ℂ) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [Matrix.mul_assoc]
      rw [this]
      simp only [← Matrix.star_eq_conjTranspose] at hE
      rw [hE, Matrix.mul_one]
      exact hU2
    · simp only [after, Function.comp, hGE, krausApply, conjSuperop]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star, Matrix.mul_assoc]
  · funext ρ
    simp only [after, before, Function.comp, conjSuperop, id, ← Matrix.star_eq_conjTranspose, star_star]
    congr 1
    simp only [← Matrix.mul_assoc, hU1, Matrix.one_mul]
    rw [Matrix.mul_assoc, hU1, Matrix.mul_one]

