-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.block_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T18:44:02.042991+00:00
-- url     : https://prove2.me/submissions/130667ee-7624-44c2-ad4c-0fdd820cff04

import Definitions.Def_pme_quantum_basics

open Matrix ProjectiveMeasurementEquilibration

theorem solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (ρ : Matrix n n ℂ) :
    ∑ x ∈ eigenvalueSet hX, ∑ y ∈ eigenvalueSet hX,
      eigenproj hX x * ρ * eigenproj hX y = ρ := by
  classical
  have hdiag :
      (∑ x ∈ eigenvalueSet hX,
        diagonal (fun i => if hX.eigenvalues i = x then (1 : ℂ) else 0)) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hmem : hX.eigenvalues i ∈ eigenvalueSet hX :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      simp [Matrix.sum_apply, hmem]
    · simp [Matrix.sum_apply, hij]
  have hproj : (∑ x ∈ eigenvalueSet hX, eigenproj hX x) = 1 := by
    simp only [eigenproj]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hdiag, mul_one]
    exact Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.property
  calc
    (∑ x ∈ eigenvalueSet hX, ∑ y ∈ eigenvalueSet hX,
        eigenproj hX x * ρ * eigenproj hX y) =
        (∑ x ∈ eigenvalueSet hX, eigenproj hX x) * ρ *
          (∑ y ∈ eigenvalueSet hX, eigenproj hX y) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ρ := by rw [hproj, one_mul, mul_one]
