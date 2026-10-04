-- Prove2me | solution 1 for TaoFivePrimes.siftedVonMangoldt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-08T09:13:31.538443+00:00
-- url     : https://prove2.me/submissions/e8c90098-820d-406f-bc7a-69ef670d3353

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open TaoFivePrimes

theorem solution (N n : ℕ) : 0 ≤ siftedVonMangoldt N n := by
  unfold siftedVonMangoldt
  split
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl
