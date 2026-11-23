-- Prove2me | solution 1 for RH1E6S16.part_007_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T14:17:47.389874+00:00
-- url     : https://prove2.me/submissions/d81d782f-1c3d-4a9e-9426-3c632b9b6c58

import Definitions.Def_RH1E6S16_D007_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0060 : RS5.BandZeros ((59246613863 : ℝ) / 65536) ((59251042299 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0060.s0 RH1E6S16_0060.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0060.s0 RH1E6S16_0060.rest = RH1E6S16_0060.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0060.s0 :: RH1E6S16_0060.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0060.s0.t = ((59246613863 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0060.s0]
  have e1 : RH1E6S16_0060.sL.t = ((59251042299 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0060.sL]
  rw [e0, e1] at h
  exact h

theorem band_0061 : RS5.BandZeros ((59251042299 : ℝ) / 65536) ((59255446165 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0061.s0 RH1E6S16_0061.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0061.s0 RH1E6S16_0061.rest = RH1E6S16_0061.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0061.s0 :: RH1E6S16_0061.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0061.s0.t = ((59251042299 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0061.s0]
  have e1 : RH1E6S16_0061.sL.t = ((59255446165 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0061.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_2 : RS5.BandZeros ((59246613863 : ℝ) / 65536) ((59255446165 : ℝ) / 65536) 254 := by
  have g0 := band_0060
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0061
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59246613863 : ℝ) / 65536) ((59255446165 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_007_2 <;> assumption
