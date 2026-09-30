-- Prove2me | solution 1 for TraceEstimation.ProjectionRank.trace_eq_rank
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:54:46.882058+00:00
-- url     : https://prove2.me/submissions/9f4bbc5f-e234-4f13-8646-9fd55630c7d5

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Matrix.Spectrum

namespace TraceEstimation.ProjectionRank

open Matrix

/-- Avron–Toledo, Lemma 5.3, proof (p. 8:9), last paragraph: a projection matrix has
`trace(A) = rank(A)`. "Projection matrix" is read as an orthogonal projection: `A` symmetric
(`A.IsHermitian`) and idempotent (`A * A = A`), i.e. symmetric with eigenvalues in `{0, 1}`,
which is the form `A = Uᵀ diag(1,…,1,0,…,0) U` the proof uses. -/
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hA2 : A * A = A) :
    A.trace = (A.rank : ℝ) := by
  have he : IsIdempotentElem A.toLin' := by
    change A.toLin' ∘ₗ A.toLin' = A.toLin'
    rw [← Matrix.toLin'_mul, hA2]
  have hh := ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr he).trace
  rw [Matrix.trace_toLin'_eq] at hh
  simpa only [Matrix.rank, Matrix.toLin'_apply'] using! hh


end TraceEstimation.ProjectionRank
