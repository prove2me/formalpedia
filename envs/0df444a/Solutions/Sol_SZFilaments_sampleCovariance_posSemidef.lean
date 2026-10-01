-- Prove2me | solution 1 for SZFilaments.sampleCovariance_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:40:02.844261+00:00
-- url     : https://prove2.me/submissions/b69a58f3-339f-49e4-9393-12edcc38a2fd

import Definitions.Def_szStackStatistics

open Finset Matrix SZFilaments

theorem solution {N n : ℕ} (y : Fin N → Fin n → ℝ) :
    (sampleCovariance y).PosSemidef := by
  let desvios := fun k i => y k i - binMean y i
  have hforma : sampleCovariance y =
      (N : ℝ)⁻¹ • ∑ k, vecMulVec (desvios k) (star (desvios k)) := by
    ext i j
    simp [sampleCovariance, desvios, Matrix.vecMulVec, Matrix.sum_apply,
      div_eq_mul_inv, mul_comm]
  rw [hforma]
  exact (Matrix.posSemidef_sum univ fun k _ =>
    Matrix.posSemidef_vecMulVec_self_star (desvios k)).smul
      (inv_nonneg.mpr (Nat.cast_nonneg N))
