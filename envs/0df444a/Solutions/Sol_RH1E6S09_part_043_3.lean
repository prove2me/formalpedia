-- Prove2me | solution 1 for RH1E6S09.part_043_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:12:39.539373+00:00
-- url     : https://prove2.me/submissions/f30dcd5b-4543-42cc-a194-de771a509814

import Definitions.Def_RH1E6S09_D043_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0350 : RS5.BandZeros ((37650093320 : ℝ) / 65536) ((37654664410 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0350.s0 RH1E6S09_0350.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0350.s0 RH1E6S09_0350.rest = RH1E6S09_0350.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0350.s0 :: RH1E6S09_0350.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0350.s0.t = ((37650093320 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0350.s0]
  have e1 : RH1E6S09_0350.sL.t = ((37654664410 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0350.sL]
  rw [e0, e1] at h
  exact h

theorem band_0351 : RS5.BandZeros ((37654664410 : ℝ) / 65536) ((37659243420 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0351.s0 RH1E6S09_0351.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0351.s0 RH1E6S09_0351.rest = RH1E6S09_0351.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0351.s0 :: RH1E6S09_0351.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0351.s0.t = ((37654664410 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0351.s0]
  have e1 : RH1E6S09_0351.sL.t = ((37659243420 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0351.sL]
  rw [e0, e1] at h
  exact h

theorem part_043_3 : RS5.BandZeros ((37650093320 : ℝ) / 65536) ((37659243420 : ℝ) / 65536) 254 := by
  have g0 := band_0350
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0351
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37650093320 : ℝ) / 65536) ((37659243420 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_043_3 <;> assumption
