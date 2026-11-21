-- Prove2me | solution 1 for RH1E6S04.part_085_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:05:36.212426+00:00
-- url     : https://prove2.me/submissions/c5fa7240-8777-4154-b79f-a3cdc0cfb563

import Definitions.Def_RH1E6S04_D085_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0680 : RS5.BandZeros ((22937497748 : ℝ) / 65536) ((22937600000 : ℝ) / 65536) 3 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0680.s0 RH1E6S04_0680.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0680.s0 RH1E6S04_0680.rest = RH1E6S04_0680.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0680.s0 :: RH1E6S04_0680.rest) = 3 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0680.s0.t = ((22937497748 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0680.s0]
  have e1 : RH1E6S04_0680.sL.t = ((22937600000 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0680.sL]
  rw [e0, e1] at h
  exact h

theorem part_085_0 : RS5.BandZeros ((22937497748 : ℝ) / 65536) ((22937600000 : ℝ) / 65536) 3 := by
  exact band_0680

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22937497748 : ℝ) / 65536) ((22937600000 : ℝ) / 65536) 3 := by
  apply RH1E6S04.part_085_0 <;> assumption
