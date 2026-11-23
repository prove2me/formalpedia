-- Prove2me | solution 1 for RH1E6S15.part_083_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:09:09.968151+00:00
-- url     : https://prove2.me/submissions/b35cb65c-7123-4085-b84b-813ca726c167

import Definitions.Def_RH1E6S15_D083_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0666 : RS5.BandZeros ((58646918592 : ℝ) / 65536) ((58651327984 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0666.s0 RH1E6S15_0666.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0666.s0 RH1E6S15_0666.rest = RH1E6S15_0666.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0666.s0 :: RH1E6S15_0666.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0666.s0.t = ((58646918592 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0666.s0]
  have e1 : RH1E6S15_0666.sL.t = ((58651327984 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0666.sL]
  rw [e0, e1] at h
  exact h

theorem band_0667 : RS5.BandZeros ((58651327984 : ℝ) / 65536) ((58655758466 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0667.s0 RH1E6S15_0667.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0667.s0 RH1E6S15_0667.rest = RH1E6S15_0667.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0667.s0 :: RH1E6S15_0667.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0667.s0.t = ((58651327984 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0667.s0]
  have e1 : RH1E6S15_0667.sL.t = ((58655758466 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0667.sL]
  rw [e0, e1] at h
  exact h

theorem part_083_1 : RS5.BandZeros ((58646918592 : ℝ) / 65536) ((58655758466 : ℝ) / 65536) 254 := by
  have g0 := band_0666
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0667
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58646918592 : ℝ) / 65536) ((58655758466 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_083_1 <;> assumption
