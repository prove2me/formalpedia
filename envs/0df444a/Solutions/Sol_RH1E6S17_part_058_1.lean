-- Prove2me | solution 1 for RH1E6S17.part_058_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:51:29.216352+00:00
-- url     : https://prove2.me/submissions/a197fcb6-75f9-48c0-b9b1-99dc268f4feb

import Definitions.Def_RH1E6S17_D058_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0466 : RS5.BandZeros ((64299778106 : ℝ) / 65536) ((64304168351 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0466.s0 RH1E6S17_0466.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0466.s0 RH1E6S17_0466.rest = RH1E6S17_0466.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0466.s0 :: RH1E6S17_0466.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0466.s0.t = ((64299778106 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0466.s0]
  have e1 : RH1E6S17_0466.sL.t = ((64304168351 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0466.sL]
  rw [e0, e1] at h
  exact h

theorem band_0467 : RS5.BandZeros ((64304168351 : ℝ) / 65536) ((64308524138 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0467.s0 RH1E6S17_0467.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0467.s0 RH1E6S17_0467.rest = RH1E6S17_0467.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0467.s0 :: RH1E6S17_0467.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0467.s0.t = ((64304168351 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0467.s0]
  have e1 : RH1E6S17_0467.sL.t = ((64308524138 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0467.sL]
  rw [e0, e1] at h
  exact h

theorem part_058_1 : RS5.BandZeros ((64299778106 : ℝ) / 65536) ((64308524138 : ℝ) / 65536) 254 := by
  have g0 := band_0466
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0467
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64299778106 : ℝ) / 65536) ((64308524138 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_058_1 <;> assumption
