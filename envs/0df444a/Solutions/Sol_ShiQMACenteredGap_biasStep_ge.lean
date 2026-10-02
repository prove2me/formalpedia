-- Prove2me | solution 1 for ShiQMACenteredGap.biasStep_ge
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-02T01:24:52.122707+00:00
-- url     : https://prove2.me/submissions/7cbf4991-9c88-4eec-8a16-5884259afb04

import Definitions.Def_ShiQMACenteredGapDominatingSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem solution {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2) : d ≤ biasStep d := by
  have hs : 0 ≤ 1 / 2 - 2 * d ^ 2 := by nlinarith
  have h := mul_nonneg hd₀ hs
  dsimp [biasStep]
  nlinarith
