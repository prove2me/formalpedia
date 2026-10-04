-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.pinching_isDensityMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T18:48:21.856998+00:00
-- url     : https://prove2.me/submissions/4f53e798-85dd-4fda-a1f4-a5c963b948dd

import Definitions.Def_pme_quantum_basics

open Matrix ProjectiveMeasurementEquilibration
open scoped ComplexOrder

theorem solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (ρ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (pinching hX ρ) := by
  classical
  let U : Matrix n n ℂ := hX.eigenvectorUnitary
  let D : ℝ → Matrix n n ℂ := fun x =>
    diagonal (fun i => if hX.eigenvalues i = x then (1 : ℂ) else 0)
  have heq (x : ℝ) : eigenproj hX x = U * D x * Uᴴ := rfl
  have hD (x : ℝ) : (D x).PosSemidef := by
    apply PosSemidef.diagonal
    intro i
    dsimp [D]
    split_ifs <;> simp
  have hHerm (x : ℝ) : (eigenproj hX x).IsHermitian := by
    rw [heq]
    exact ((hD x).mul_mul_conjTranspose_same U).1
  have hDD (x : ℝ) : D x * D x = D x := by
    dsimp [D]
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  have hunit : Uᴴ * U = 1 :=
    Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.property
  have hPP (x : ℝ) : eigenproj hX x * eigenproj hX x = eigenproj hX x := by
    rw [heq]
    calc
      (U * D x * Uᴴ) * (U * D x * Uᴴ) = U * (D x * (Uᴴ * U) * D x) * Uᴴ := by
        simp only [mul_assoc]
      _ = U * D x * Uᴴ := by rw [hunit, mul_one, hDD]
  have hdiag : (∑ x ∈ eigenvalueSet hX, D x) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hmem : hX.eigenvalues i ∈ eigenvalueSet hX :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      simp [D, Matrix.sum_apply, hmem]
    · simp [D, Matrix.sum_apply, hij]
  have hproj : (∑ x ∈ eigenvalueSet hX, eigenproj hX x) = 1 := by
    simp only [heq]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hdiag, mul_one]
    exact Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.property
  constructor
  · apply Matrix.posSemidef_sum
    intro x hx
    simpa only [(hHerm x).eq] using hρ.1.mul_mul_conjTranspose_same (eigenproj hX x)
  · change (∑ x ∈ eigenvalueSet hX, eigenproj hX x * ρ * eigenproj hX x).trace = 1
    rw [Matrix.trace_sum]
    have htrace (x : ℝ) : (eigenproj hX x * ρ * eigenproj hX x).trace =
        (ρ * eigenproj hX x).trace := by
      rw [Matrix.trace_mul_cycle, hPP, Matrix.trace_mul_comm]
    simp only [htrace]
    rw [← Matrix.trace_sum, ← Finset.mul_sum, hproj, mul_one]
    exact hρ.2
