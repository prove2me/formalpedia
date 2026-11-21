-- Prove2me | solution 1 for RH1E6S04.part_055_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:30:20.598049+00:00
-- url     : https://prove2.me/submissions/dd3e76d0-abe4-42dd-b98f-3762de6e9e58

import Definitions.Def_RH1E6S04_D055_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0446 : RS5.BandZeros ((21815118218 : ℝ) / 65536) ((21819916313 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0446.s0 RH1E6S04_0446.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0446.s0 RH1E6S04_0446.rest = RH1E6S04_0446.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0446.s0 :: RH1E6S04_0446.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0446.s0.t = ((21815118218 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0446.s0]
  have e1 : RH1E6S04_0446.sL.t = ((21819916313 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0446.sL]
  rw [e0, e1] at h
  exact h

theorem band_0447 : RS5.BandZeros ((21819916313 : ℝ) / 65536) ((21824733237 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0447.s0 RH1E6S04_0447.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0447.s0 RH1E6S04_0447.rest = RH1E6S04_0447.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0447.s0 :: RH1E6S04_0447.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0447.s0.t = ((21819916313 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0447.s0]
  have e1 : RH1E6S04_0447.sL.t = ((21824733237 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0447.sL]
  rw [e0, e1] at h
  exact h

theorem part_055_3 : RS5.BandZeros ((21815118218 : ℝ) / 65536) ((21824733237 : ℝ) / 65536) 254 := by
  have g0 := band_0446
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0447
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21815118218 : ℝ) / 65536) ((21824733237 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_055_3 <;> assumption
