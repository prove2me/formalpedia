-- Prove2me | solution 1 for RH1E6S10.part_015_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T18:28:03.371022+00:00
-- url     : https://prove2.me/submissions/8292cedc-ccfb-49e5-a5c5-4050fd285dd3

import Definitions.Def_RH1E6S10_D015_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0120 : RS5.BandZeros ((39868562018 : ℝ) / 65536) ((39873126064 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0120.s0 RH1E6S10_0120.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0120.s0 RH1E6S10_0120.rest = RH1E6S10_0120.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0120.s0 :: RH1E6S10_0120.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0120.s0.t = ((39868562018 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0120.s0]
  have e1 : RH1E6S10_0120.sL.t = ((39873126064 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0120.sL]
  rw [e0, e1] at h
  exact h

theorem band_0121 : RS5.BandZeros ((39873126064 : ℝ) / 65536) ((39877672131 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0121.s0 RH1E6S10_0121.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0121.s0 RH1E6S10_0121.rest = RH1E6S10_0121.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0121.s0 :: RH1E6S10_0121.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0121.s0.t = ((39873126064 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0121.s0]
  have e1 : RH1E6S10_0121.sL.t = ((39877672131 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0121.sL]
  rw [e0, e1] at h
  exact h

theorem part_015_0 : RS5.BandZeros ((39868562018 : ℝ) / 65536) ((39877672131 : ℝ) / 65536) 254 := by
  have g0 := band_0120
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0121
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39868562018 : ℝ) / 65536) ((39877672131 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_015_0 <;> assumption
