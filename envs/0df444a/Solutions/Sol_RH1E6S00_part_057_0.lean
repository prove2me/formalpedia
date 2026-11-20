-- Prove2me | solution 1 for RH1E6S00.part_057_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:40:52.599762+00:00
-- url     : https://prove2.me/submissions/ebda9628-0a54-41f5-99f4-cc393afcd3c0

import Definitions.Def_RH1E6S00_D057_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0456 : RS5.BandZeros ((8976914863 : ℝ) / 65536) ((8982139343 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0456.s0 RH1E6S00_0456.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0456.s0 RH1E6S00_0456.rest = RH1E6S00_0456.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0456.s0 :: RH1E6S00_0456.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0456.s0.t = ((8976914863 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0456.s0]
  have e1 : RH1E6S00_0456.sL.t = ((8982139343 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0456.sL]
  rw [e0, e1] at h
  exact h

theorem band_0457 : RS5.BandZeros ((8982139343 : ℝ) / 65536) ((8987394431 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0457.s0 RH1E6S00_0457.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0457.s0 RH1E6S00_0457.rest = RH1E6S00_0457.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0457.s0 :: RH1E6S00_0457.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0457.s0.t = ((8982139343 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0457.s0]
  have e1 : RH1E6S00_0457.sL.t = ((8987394431 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0457.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_0 : RS5.BandZeros ((8976914863 : ℝ) / 65536) ((8987394431 : ℝ) / 65536) 254 := by
  have g0 := band_0456
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0457
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8976914863 : ℝ) / 65536) ((8987394431 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_057_0 <;> assumption
