-- Prove2me | solution 1 for RH1E6S10.part_031_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:40:15.483383+00:00
-- url     : https://prove2.me/submissions/3e6dab7a-85c3-47f4-a1f6-c0e1badd82af

import Definitions.Def_RH1E6S10_D031_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0252 : RS5.BandZeros ((40469443031 : ℝ) / 65536) ((40473992183 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0252.s0 RH1E6S10_0252.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0252.s0 RH1E6S10_0252.rest = RH1E6S10_0252.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0252.s0 :: RH1E6S10_0252.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0252.s0.t = ((40469443031 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0252.s0]
  have e1 : RH1E6S10_0252.sL.t = ((40473992183 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0252.sL]
  rw [e0, e1] at h
  exact h

theorem band_0253 : RS5.BandZeros ((40473992183 : ℝ) / 65536) ((40478550245 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0253.s0 RH1E6S10_0253.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0253.s0 RH1E6S10_0253.rest = RH1E6S10_0253.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0253.s0 :: RH1E6S10_0253.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0253.s0.t = ((40473992183 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0253.s0]
  have e1 : RH1E6S10_0253.sL.t = ((40478550245 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0253.sL]
  rw [e0, e1] at h
  exact h

theorem part_031_2 : RS5.BandZeros ((40469443031 : ℝ) / 65536) ((40478550245 : ℝ) / 65536) 254 := by
  have g0 := band_0252
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0253
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40469443031 : ℝ) / 65536) ((40478550245 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_031_2 <;> assumption
