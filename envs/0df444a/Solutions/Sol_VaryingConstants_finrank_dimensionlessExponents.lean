-- Prove2me | solution 1 for VaryingConstants.finrank_dimensionlessExponents
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:54:44.318975+00:00
-- url     : https://prove2.me/submissions/53037730-afab-4bd4-941f-3b1d9282cdf3

import Mathlib
import Definitions.Def_VaryingConstants_units

open VaryingConstants in
theorem solution {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) :
    Module.finrank ℝ (dimensionlessExponents D) = n - D.rank := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.vecMulLinear D)
  have h2 : LinearMap.range (Matrix.vecMulLinear D) = LinearMap.range (Matrix.mulVecLin D.transpose) := by
    congr 1
    ext x : 1
    simp
  have h3 : Module.finrank ℝ (LinearMap.range (Matrix.vecMulLinear D)) = D.rank := by
    rw [h2, ← Matrix.rank_transpose D]
    rfl
  simp only [Module.finrank_fin_fun] at h1
  unfold VaryingConstants.dimensionlessExponents
  omega
