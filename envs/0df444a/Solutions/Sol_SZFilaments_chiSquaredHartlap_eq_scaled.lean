-- Prove2me | solution 1 for SZFilaments.chiSquaredHartlap_eq_scaled
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:41:53.205372+00:00
-- url     : https://prove2.me/submissions/07c31c20-7563-4be2-96aa-9c59c90ccdad

import Definitions.Def_szStackStatistics

open Finset Matrix SZFilaments

theorem solution {n : ℕ} (Nsub : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
    (ybar : Fin n → ℝ) :
    chiSquaredHartlap Nsub C ybar
      = (((Nsub : ℝ) - (n : ℝ) - 2) / ((Nsub : ℝ) - 1)) * chiSquared C ybar := by
  simp only [chiSquaredHartlap, chiSquared, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
