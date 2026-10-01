-- Prove2me | solution 1 for SZFilaments.jackknifeCovariance_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:40:05.567552+00:00
-- url     : https://prove2.me/submissions/35e07759-2e5a-4e19-829d-719c36a71916

import Definitions.Def_szStackStatistics

open Finset Matrix SZFilaments

theorem solution {Nsub n : ℕ} (y : Fin Nsub → Fin n → ℝ) :
    (jackknifeCovariance y).PosSemidef := by
  let desvios := fun k i => y k i - binMean y i
  have hforma : jackknifeCovariance y =
      (((Nsub : ℝ) - 1) / Nsub) • ∑ k, vecMulVec (desvios k) (star (desvios k)) := by
    ext i j
    simp [jackknifeCovariance, desvios, Matrix.vecMulVec, Matrix.sum_apply]
  have hfator : 0 ≤ ((Nsub : ℝ) - 1) / Nsub := by
    cases Nsub with
    | zero => norm_num
    | succ quantidade =>
        simp only [Nat.cast_succ, add_sub_cancel_right]
        positivity
  rw [hforma]
  exact (Matrix.posSemidef_sum univ fun k _ =>
    Matrix.posSemidef_vecMulVec_self_star (desvios k)).smul hfator
