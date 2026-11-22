-- Prove2me | solution 1 for RH1E6S11.part_074_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:32:58.207371+00:00
-- url     : https://prove2.me/submissions/d2b4f14f-8125-48a8-a218-ac5b0c4f9107

import Definitions.Def_RH1E6S11_D074_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0596 : RS5.BandZeros ((45290449962 : ℝ) / 65536) ((45294946142 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0596.s0 RH1E6S11_0596.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0596.s0 RH1E6S11_0596.rest = RH1E6S11_0596.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0596.s0 :: RH1E6S11_0596.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0596.s0.t = ((45290449962 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0596.s0]
  have e1 : RH1E6S11_0596.sL.t = ((45294946142 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0596.sL]
  rw [e0, e1] at h
  exact h

theorem band_0597 : RS5.BandZeros ((45294946142 : ℝ) / 65536) ((45299460019 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0597.s0 RH1E6S11_0597.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0597.s0 RH1E6S11_0597.rest = RH1E6S11_0597.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0597.s0 :: RH1E6S11_0597.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0597.s0.t = ((45294946142 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0597.s0]
  have e1 : RH1E6S11_0597.sL.t = ((45299460019 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0597.sL]
  rw [e0, e1] at h
  exact h

theorem part_074_2 : RS5.BandZeros ((45290449962 : ℝ) / 65536) ((45299460019 : ℝ) / 65536) 254 := by
  have g0 := band_0596
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0597
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45290449962 : ℝ) / 65536) ((45299460019 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_074_2 <;> assumption
