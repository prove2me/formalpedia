-- Prove2me | solution 1 for RH1E6S10.part_009_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T17:51:59.408739+00:00
-- url     : https://prove2.me/submissions/7d94d5b9-aa0d-4d6f-b263-a0b7f977645d

import Definitions.Def_RH1E6S10_D009_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0076 : RS5.BandZeros ((39668093557 : ℝ) / 65536) ((39672650637 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0076.s0 RH1E6S10_0076.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0076.s0 RH1E6S10_0076.rest = RH1E6S10_0076.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0076.s0 :: RH1E6S10_0076.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0076.s0.t = ((39668093557 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0076.s0]
  have e1 : RH1E6S10_0076.sL.t = ((39672650637 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0076.sL]
  rw [e0, e1] at h
  exact h

theorem band_0077 : RS5.BandZeros ((39672650637 : ℝ) / 65536) ((39677207672 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0077.s0 RH1E6S10_0077.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0077.s0 RH1E6S10_0077.rest = RH1E6S10_0077.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0077.s0 :: RH1E6S10_0077.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0077.s0.t = ((39672650637 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0077.s0]
  have e1 : RH1E6S10_0077.sL.t = ((39677207672 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0077.sL]
  rw [e0, e1] at h
  exact h

theorem part_009_2 : RS5.BandZeros ((39668093557 : ℝ) / 65536) ((39677207672 : ℝ) / 65536) 254 := by
  have g0 := band_0076
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0077
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39668093557 : ℝ) / 65536) ((39677207672 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_009_2 <;> assumption
