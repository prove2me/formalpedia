-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P40.codeIsometryNoise
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:35:07.273265+00:00
-- url     : https://prove2.me/submissions/77594ef9-d29c-4698-8531-ca900f6f96ce

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

/-- PDF pp.4–5, (24)–(25): incorporating an isometric code into the noise preserves outputs. -/
theorem solution {h k m : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h ≤ k)
    (U : Matrix (Fin k) (Fin h) ℂ) (hU : Uᴴ * U = 1)
    (rho : Matrix (Fin k) (Fin k) ℂ) (hrho : IsDensityMatrix rho)
    (hsupp : rho = codeProjector U * rho * codeProjector U)
    (E : Fin m → Matrix (Fin k) (Fin k) ℂ) (hE : IsKrausFamily E) :
    codeProjector U = ∑ i, dyad (WithLp.toLp 2 (fun x => U x i))
      (WithLp.toLp 2 (fun x => U x i)) ∧
    IsDensityMatrix (Uᴴ * rho * U) ∧
    IsKrausFamily (fun j => E j * U) ∧
    krausApply (fun j => E j * U) (Uᴴ * rho * U) = krausApply E rho := by
  have hP2 : codeProjector U * codeProjector U = codeProjector U := by
    unfold codeProjector
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · ext x y
    simp [codeProjector, dyad, Matrix.mul_apply, Matrix.sum_apply]
  · simpa using hrho.1.conjTranspose_mul_mul_same U
  · have h1 : (Uᴴ * rho * U).trace = (rho * codeProjector U).trace := by
      unfold codeProjector
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
      exact Matrix.trace_mul_comm _ _
    have h2 : (codeProjector U * rho * codeProjector U).trace = (rho * codeProjector U).trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP2]
      exact Matrix.trace_mul_comm _ _
    rw [h1, ← h2, ← hsupp, hrho.2]
  · unfold QAlgorithms.IsKrausFamily at hE ⊢
    simp only [Matrix.conjTranspose_mul]
    have : ∀ j, Uᴴ * (E j)ᴴ * (E j * U) = Uᴴ * ((E j)ᴴ * E j) * U := by
      intro j; simp only [Matrix.mul_assoc]
    simp only [this]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hE, Matrix.mul_one, hU]
  · unfold QAlgorithms.krausApply
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [hsupp]
    simp only [codeProjector, Matrix.conjTranspose_mul, Matrix.mul_assoc]


end

