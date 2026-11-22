-- Prove2me | solution 1 for RH1E6S10.part_007_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T17:40:38.686549+00:00
-- url     : https://prove2.me/submissions/5414a1d5-dd5a-496c-990f-78c240d9e14b

import Definitions.Def_RH1E6S10_D007_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0060 : RS5.BandZeros ((39595183039 : ℝ) / 65536) ((39599722906 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0060.s0 RH1E6S10_0060.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0060.s0 RH1E6S10_0060.rest = RH1E6S10_0060.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0060.s0 :: RH1E6S10_0060.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0060.s0.t = ((39595183039 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0060.s0]
  have e1 : RH1E6S10_0060.sL.t = ((39599722906 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0060.sL]
  rw [e0, e1] at h
  exact h

theorem band_0061 : RS5.BandZeros ((39599722906 : ℝ) / 65536) ((39604289643 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0061.s0 RH1E6S10_0061.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0061.s0 RH1E6S10_0061.rest = RH1E6S10_0061.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0061.s0 :: RH1E6S10_0061.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0061.s0.t = ((39599722906 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0061.s0]
  have e1 : RH1E6S10_0061.sL.t = ((39604289643 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0061.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_2 : RS5.BandZeros ((39595183039 : ℝ) / 65536) ((39604289643 : ℝ) / 65536) 254 := by
  have g0 := band_0060
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0061
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39595183039 : ℝ) / 65536) ((39604289643 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_007_2 <;> assumption
