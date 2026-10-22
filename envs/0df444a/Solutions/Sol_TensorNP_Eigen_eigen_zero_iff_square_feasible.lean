-- Prove2me | solution 1 for TensorNP.Eigen.eigen_zero_iff_square_feasible
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:50:10.92279+00:00
-- url     : https://prove2.me/submissions/ad84423e-27c5-4995-bc07-f9321bf1c0e5

import Mathlib
import Definitions.Def_TensorNP_Eigen_Defs

set_option autoImplicit false
open Matrix TensorNP.Eigen

theorem solution {n : ℕ} (A : Fin n → Fin n → Fin n → ℚ) :
    IsEigenvalue (castTensor ℝ A) 0 ↔
      QuadSolvable (castMatrices ℝ (fun k : Fin n => Matrix.of fun i j => A i j k)) := by
  have key : ∀ (x : Fin n → ℝ) (k : Fin n),
      (∑ i, ∑ j, castTensor ℝ A i j k * x i * x j) =
        x ⬝ᵥ ((castMatrices ℝ (fun k : Fin n => Matrix.of fun i j => A i j k)) k *ᵥ x) := by
    intro x k
    simp only [dotProduct, mulVec, castTensor, castMatrices, Matrix.map_apply, Matrix.of_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun k => ?_⟩
    rw [← key]; simpa using h k
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun k => ?_⟩
    rw [key]; simpa using h k
