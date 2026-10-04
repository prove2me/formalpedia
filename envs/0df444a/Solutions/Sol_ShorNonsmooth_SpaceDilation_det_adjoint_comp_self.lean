-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.det_adjoint_comp_self
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:29:50.914948+00:00
-- url     : https://prove2.me/submissions/df26d5ab-9f46-440a-bc26-f0730c119575

import Mathlib

theorem solution {n : ℕ} (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    LinearMap.det ((LinearMap.adjoint A).comp A) = (LinearMap.det A) ^ 2 := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ)
  rw [LinearMap.det_comp, ← LinearMap.det_toMatrix b.toBasis (LinearMap.adjoint A),
    LinearMap.toMatrix_adjoint, ← LinearMap.det_toMatrix b.toBasis A]
  simp [Matrix.det_conjTranspose, sq]
