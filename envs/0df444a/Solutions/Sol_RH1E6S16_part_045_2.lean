-- Prove2me | solution 1 for RH1E6S16.part_045_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T16:46:07.483598+00:00
-- url     : https://prove2.me/submissions/055a97a9-278f-4d3b-a5f9-4171fa28927d

import Definitions.Def_RH1E6S16_D045_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0364 : RS5.BandZeros ((60583930043 : ℝ) / 65536) ((60588339315 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0364.s0 RH1E6S16_0364.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0364.s0 RH1E6S16_0364.rest = RH1E6S16_0364.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0364.s0 :: RH1E6S16_0364.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0364.s0.t = ((60583930043 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0364.s0]
  have e1 : RH1E6S16_0364.sL.t = ((60588339315 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0364.sL]
  rw [e0, e1] at h
  exact h

theorem band_0365 : RS5.BandZeros ((60588339315 : ℝ) / 65536) ((60592708238 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0365.s0 RH1E6S16_0365.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0365.s0 RH1E6S16_0365.rest = RH1E6S16_0365.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0365.s0 :: RH1E6S16_0365.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0365.s0.t = ((60588339315 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0365.s0]
  have e1 : RH1E6S16_0365.sL.t = ((60592708238 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0365.sL]
  rw [e0, e1] at h
  exact h

theorem part_045_2 : RS5.BandZeros ((60583930043 : ℝ) / 65536) ((60592708238 : ℝ) / 65536) 254 := by
  have g0 := band_0364
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0365
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60583930043 : ℝ) / 65536) ((60592708238 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_045_2 <;> assumption
