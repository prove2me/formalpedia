-- Prove2me | solution 1 for RH1E6S09.part_028_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:29:16.963402+00:00
-- url     : https://prove2.me/submissions/6ffa93cc-3fcf-4dec-80c1-5a18237e9baf

import Definitions.Def_RH1E6S09_D028_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0228 : RS5.BandZeros ((37091225054 : ℝ) / 65536) ((37095805058 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0228.s0 RH1E6S09_0228.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0228.s0 RH1E6S09_0228.rest = RH1E6S09_0228.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0228.s0 :: RH1E6S09_0228.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0228.s0.t = ((37091225054 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0228.s0]
  have e1 : RH1E6S09_0228.sL.t = ((37095805058 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0228.sL]
  rw [e0, e1] at h
  exact h

theorem band_0229 : RS5.BandZeros ((37095805058 : ℝ) / 65536) ((37100387867 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0229.s0 RH1E6S09_0229.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0229.s0 RH1E6S09_0229.rest = RH1E6S09_0229.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0229.s0 :: RH1E6S09_0229.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0229.s0.t = ((37095805058 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0229.s0]
  have e1 : RH1E6S09_0229.sL.t = ((37100387867 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0229.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_2 : RS5.BandZeros ((37091225054 : ℝ) / 65536) ((37100387867 : ℝ) / 65536) 254 := by
  have g0 := band_0228
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0229
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37091225054 : ℝ) / 65536) ((37100387867 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_028_2 <;> assumption
