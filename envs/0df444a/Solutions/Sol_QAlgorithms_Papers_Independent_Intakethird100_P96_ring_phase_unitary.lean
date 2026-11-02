-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P96.ring_phase_unitary
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:15:55.562202+00:00
-- url     : https://prove2.me/submissions/43abd180-bf04-461d-a336-71766fcc353e

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

open scoped BigOperators
open QAlgorithms.Papers.Independent.Intakethird100.P96

theorem solution (extra : ℕ) :
    ringPhase extra ∈ Matrix.unitaryGroup (RingConfiguration extra) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  simp only [ringPhase, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  simp only [Pi.star_apply, star_prod, apply_ite, star_neg, star_one,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro x _
  split_ifs <;> norm_num

end
