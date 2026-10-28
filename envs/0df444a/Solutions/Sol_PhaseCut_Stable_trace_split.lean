-- Prove2me | solution 1 for PhaseCut.Stable.trace_split
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T10:47:15.783723+00:00
-- url     : https://prove2.me/submissions/9883ee5d-4925-4ee1-ac3b-518b28ddf635

import Mathlib
import Definitions.Def_PhaseCut_Stable_Defs

open Matrix PhaseCut.Stable
open scoped ComplexOrder

theorem solution {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (V : Matrix (Fin n) (Fin n) ℂ) :
    V.trace = (Vpar A V).trace + (Vperp A V).trace := by
  have hP : projRange A * projRange A = projRange A := by
    have e : projRange A = (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
        (LinearMap.range (Matrix.toEuclideanLin A)).starProjection := rfl
    rw [e, ← map_mul, (Submodule.isIdempotentElem_starProjection _).eq]
  set P := projRange A with hPdef
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, mul_sub, mul_sub, hP]; simp
  unfold Vpar Vperp
  rw [← hPdef]
  rw [Matrix.trace_mul_cycle P V P, Matrix.trace_mul_cycle (1 - P) V (1 - P), hP, hQ]
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul]
  ring
