-- Prove2me | solution 1 for TaoFivePrimes.eta0_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-08T09:13:30.379528+00:00
-- url     : https://prove2.me/submissions/c889562d-c89c-40cd-9df8-31656595026d

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open TaoFivePrimes

theorem solution (t : ℝ) : 0 ≤ eta0 t := by
  unfold eta0
  split
  · have : (0 : ℝ) ≤ max 0 (Real.log 2 - |Real.log (2 * t)|) := le_max_left _ _
    linarith
  · exact le_rfl
