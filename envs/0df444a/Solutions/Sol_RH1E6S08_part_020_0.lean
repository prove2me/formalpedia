-- Prove2me | solution 1 for RH1E6S08.part_020_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:51:47.498212+00:00
-- url     : https://prove2.me/submissions/9b7e251f-92fe-4c90-a2c6-af2d3f8f7349

import Definitions.Def_RH1E6S08_D020_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0160 : RS5.BandZeros ((33508782080 : ℝ) / 65536) ((33513403486 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0160.s0 RH1E6S08_0160.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0160.s0 RH1E6S08_0160.rest = RH1E6S08_0160.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0160.s0 :: RH1E6S08_0160.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0160.s0.t = ((33508782080 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0160.s0]
  have e1 : RH1E6S08_0160.sL.t = ((33513403486 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0160.sL]
  rw [e0, e1] at h
  exact h

theorem band_0161 : RS5.BandZeros ((33513403486 : ℝ) / 65536) ((33518016035 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0161.s0 RH1E6S08_0161.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0161.s0 RH1E6S08_0161.rest = RH1E6S08_0161.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0161.s0 :: RH1E6S08_0161.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0161.s0.t = ((33513403486 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0161.s0]
  have e1 : RH1E6S08_0161.sL.t = ((33518016035 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0161.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_0 : RS5.BandZeros ((33508782080 : ℝ) / 65536) ((33518016035 : ℝ) / 65536) 254 := by
  have g0 := band_0160
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0161
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33508782080 : ℝ) / 65536) ((33518016035 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_020_0 <;> assumption
