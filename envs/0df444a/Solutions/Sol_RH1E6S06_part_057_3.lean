-- Prove2me | solution 1 for RH1E6S06.part_057_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T20:13:36.225788+00:00
-- url     : https://prove2.me/submissions/2c9187c6-3a05-4fae-8c6d-6cd87e17bca5

import Definitions.Def_RH1E6S06_D057_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0462 : RS5.BandZeros ((28390688268 : ℝ) / 65536) ((28395381527 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0462.s0 RH1E6S06_0462.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0462.s0 RH1E6S06_0462.rest = RH1E6S06_0462.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0462.s0 :: RH1E6S06_0462.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0462.s0.t = ((28390688268 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0462.s0]
  have e1 : RH1E6S06_0462.sL.t = ((28395381527 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0462.sL]
  rw [e0, e1] at h
  exact h

theorem band_0463 : RS5.BandZeros ((28395381527 : ℝ) / 65536) ((28400072249 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0463.s0 RH1E6S06_0463.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0463.s0 RH1E6S06_0463.rest = RH1E6S06_0463.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0463.s0 :: RH1E6S06_0463.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0463.s0.t = ((28395381527 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0463.s0]
  have e1 : RH1E6S06_0463.sL.t = ((28400072249 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0463.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_3 : RS5.BandZeros ((28390688268 : ℝ) / 65536) ((28400072249 : ℝ) / 65536) 254 := by
  have g0 := band_0462
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0463
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28390688268 : ℝ) / 65536) ((28400072249 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_057_3 <;> assumption
