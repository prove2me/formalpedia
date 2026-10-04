-- Prove2me | solution 1 for TegmarkDimensionality.laplacian_eq_mathlib
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T01:25:09.471526+00:00
-- url     : https://prove2.me/submissions/02e04cd5-2695-4929-801e-34312ef3e601

import Definitions.Def_tegmark_laplacian
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2

open InnerProductSpace Laplacian

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    TegmarkDimensionality.laplacian f x = Δ f x := by
  dsimp [TegmarkDimensionality.laplacian]
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp [EuclideanSpace.basisFun_apply]
