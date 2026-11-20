-- Prove2me | solution 1 for RH1E6S00.part_044_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:15:07.776517+00:00
-- url     : https://prove2.me/submissions/2b027ff3-9b3c-43e6-8139-015c15248dc7

import Definitions.Def_RH1E6S00_D044_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0354 : RS5.BandZeros ((8441329381 : ℝ) / 65536) ((8446586222 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0354.s0 RH1E6S00_0354.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0354.s0 RH1E6S00_0354.rest = RH1E6S00_0354.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0354.s0 :: RH1E6S00_0354.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0354.s0.t = ((8441329381 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0354.s0]
  have e1 : RH1E6S00_0354.sL.t = ((8446586222 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0354.sL]
  rw [e0, e1] at h
  exact h

theorem band_0355 : RS5.BandZeros ((8446586222 : ℝ) / 65536) ((8451853100 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0355.s0 RH1E6S00_0355.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0355.s0 RH1E6S00_0355.rest = RH1E6S00_0355.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0355.s0 :: RH1E6S00_0355.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0355.s0.t = ((8446586222 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0355.s0]
  have e1 : RH1E6S00_0355.sL.t = ((8451853100 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0355.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_1 : RS5.BandZeros ((8441329381 : ℝ) / 65536) ((8451853100 : ℝ) / 65536) 254 := by
  have g0 := band_0354
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0355
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8441329381 : ℝ) / 65536) ((8451853100 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_044_1 <;> assumption
