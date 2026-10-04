-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.trace_adjoint_comp_self_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:19:10.699957+00:00
-- url     : https://prove2.me/submissions/76b9ff5e-c31e-4b3c-a511-64b8c7437abf

import Mathlib

theorem solution {n : ℕ} (hn : 0 < n)
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    0 ≤ LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) ((LinearMap.adjoint A).comp A) := by
  exact (LinearMap.isPositive_adjoint_comp_self A).trace_nonneg
