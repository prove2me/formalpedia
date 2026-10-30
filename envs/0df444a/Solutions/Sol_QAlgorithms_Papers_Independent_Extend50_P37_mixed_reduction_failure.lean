-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P37.mixed_reduction_failure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T15:10:23.099143+00:00
-- url     : https://prove2.me/submissions/73b99ebe-5cde-44ec-9ff8-ecf3c828b545

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37
noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

end QAlgorithms.Papers.Independent.Extend50.P37

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P37
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution :
    (∀ rho : Mat (Fin 2), IsDensityMatrix rho →
      ∀ U ∈ unitaryCentralizer ({1} : Set (Mat (Fin 2))),
        ((U * rho * Uᴴ) ^ 2).trace.re = (rho ^ 2).trace.re) ∧
    let rho : Mat (Fin 2) := Matrix.diagonal ![(1 : ℂ),0]
    let sigma : Mat (Fin 2) := (1/2 : ℂ) • 1
    IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      SameReduction (alg ({1} : Set (Mat (Fin 2)))) rho sigma ∧
      (rho ^ 2).trace.re = 1 ∧ (sigma ^ 2).trace.re = 1/2 := by
  refine ⟨?_, ?_⟩
  · intro rho _ U hU
    have hu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU.1
    have : (U * rho * Uᴴ) ^ 2 = U * (rho ^ 2) * Uᴴ := by
      rw [sq, sq]
      calc U * rho * Uᴴ * (U * rho * Uᴴ) = U * rho * (Uᴴ * U) * rho * Uᴴ := by
            simp only [Matrix.mul_assoc]
        _ = U * (rho * rho) * Uᴴ := by rw [hu]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [this, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hu, Matrix.mul_one]
  · intro rho sigma
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · show (Matrix.diagonal ![(1 : ℂ),0]).PosSemidef
      rw [Matrix.posSemidef_diagonal_iff]
      intro i; fin_cases i <;> simp
    · show (Matrix.diagonal ![(1 : ℂ),0]).trace = 1
      simp [Matrix.trace, Fin.sum_univ_two]
    · show ((1/2 : ℂ) • (1 : Mat (Fin 2))).PosSemidef
      exact Matrix.PosSemidef.one.smul (by rw [Complex.le_def]; norm_num)
    · show ((1/2 : ℂ) • (1 : Mat (Fin 2))).trace = 1
      simp [Matrix.trace]
    · intro X hX
      have hle : alg ({1} : Set (Mat (Fin 2))) ≤ ((⊥ : Subalgebra ℂ (Mat (Fin 2))) : Set _) := by
        unfold alg
        exact Algebra.adjoin_le (by
          intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact Subalgebra.one_mem _)
      obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp (hle hX)
      simp only [rho, sigma, Algebra.algebraMap_eq_smul_one]
      simp [Matrix.trace, Fin.sum_univ_two]; ring
    · simp [rho, sq, Matrix.trace, Fin.sum_univ_two]
    · simp [sigma, sq, Matrix.trace, Fin.sum_univ_two]
