-- Prove2me | solution 1 for SZFilaments.chiSquared_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:40:07.527716+00:00
-- url     : https://prove2.me/submissions/211f8e86-1ef3-48dd-925b-11198998cf19

import Definitions.Def_szStackStatistics

open Finset Matrix SZFilaments

theorem solution {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (ybar : Fin n → ℝ) : 0 ≤ chiSquared C ybar := by
  simpa [chiSquared, dotProduct, mulVec, Finset.mul_sum, mul_assoc] using
    hC.inv.posSemidef.dotProduct_mulVec_nonneg ybar
