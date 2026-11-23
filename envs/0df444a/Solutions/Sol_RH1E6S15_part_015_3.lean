-- Prove2me | solution 1 for RH1E6S15.part_015_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:42:57.81042+00:00
-- url     : https://prove2.me/submissions/68fba952-5c5e-4619-bcd4-4fa40bc214cb

import Definitions.Def_RH1E6S15_D015_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0126 : RS5.BandZeros ((56263033614 : ℝ) / 65536) ((56267453712 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0126.s0 RH1E6S15_0126.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0126.s0 RH1E6S15_0126.rest = RH1E6S15_0126.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0126.s0 :: RH1E6S15_0126.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0126.s0.t = ((56263033614 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0126.s0]
  have e1 : RH1E6S15_0126.sL.t = ((56267453712 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0126.sL]
  rw [e0, e1] at h
  exact h

theorem band_0127 : RS5.BandZeros ((56267453712 : ℝ) / 65536) ((56271869685 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0127.s0 RH1E6S15_0127.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0127.s0 RH1E6S15_0127.rest = RH1E6S15_0127.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0127.s0 :: RH1E6S15_0127.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0127.s0.t = ((56267453712 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0127.s0]
  have e1 : RH1E6S15_0127.sL.t = ((56271869685 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0127.sL]
  rw [e0, e1] at h
  exact h

theorem part_015_3 : RS5.BandZeros ((56263033614 : ℝ) / 65536) ((56271869685 : ℝ) / 65536) 254 := by
  have g0 := band_0126
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0127
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56263033614 : ℝ) / 65536) ((56271869685 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_015_3 <;> assumption
