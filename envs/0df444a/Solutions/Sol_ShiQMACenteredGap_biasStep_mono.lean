-- Prove2me | solution 1 for ShiQMACenteredGap.biasStep_mono
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T23:41:43.362891+00:00
-- url     : https://prove2.me/submissions/de01c30c-dba6-4f26-bcb9-99ed71f7c156

import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem solution {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e)
    (he : e ≤ 1 / 2) : biasStep d ≤ biasStep e := by
  have hed : e * d ≤ 1 / 4 := by nlinarith [sq_nonneg (e - d)]
  have hsq : e ^ 2 + e * d + d ^ 2 ≤ 3 / 4 := by
    nlinarith [mul_nonneg (show 0 ≤ e by linarith) (show 0 ≤ 1 / 2 - e by linarith),
      mul_nonneg hd (show 0 ≤ 1 / 2 - d by linarith)]
  have h := mul_nonneg (show 0 ≤ e - d by linarith)
    (show 0 ≤ 3 / 2 - 2 * (e ^ 2 + e * d + d ^ 2) by linarith)
  dsimp [biasStep]
  nlinarith
