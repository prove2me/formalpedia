-- Prove2me | solution 1 for RH1E6S10.part_000_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T16:50:46.620642+00:00
-- url     : https://prove2.me/submissions/5f87cf9a-6a38-4baf-85c5-764078e6c8df

import Definitions.Def_RH1E6S10_D000_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0002 : RS5.BandZeros ((39330751562 : ℝ) / 65536) ((39335303059 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0002.s0 RH1E6S10_0002.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0002.s0 RH1E6S10_0002.rest = RH1E6S10_0002.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0002.s0 :: RH1E6S10_0002.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0002.s0.t = ((39330751562 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0002.s0]
  have e1 : RH1E6S10_0002.sL.t = ((39335303059 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0002.sL]
  rw [e0, e1] at h
  exact h

theorem band_0003 : RS5.BandZeros ((39335303059 : ℝ) / 65536) ((39339863487 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0003.s0 RH1E6S10_0003.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0003.s0 RH1E6S10_0003.rest = RH1E6S10_0003.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0003.s0 :: RH1E6S10_0003.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0003.s0.t = ((39335303059 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0003.s0]
  have e1 : RH1E6S10_0003.sL.t = ((39339863487 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0003.sL]
  rw [e0, e1] at h
  exact h

theorem part_000_1 : RS5.BandZeros ((39330751562 : ℝ) / 65536) ((39339863487 : ℝ) / 65536) 254 := by
  have g0 := band_0002
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0003
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39330751562 : ℝ) / 65536) ((39339863487 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_000_1 <;> assumption
