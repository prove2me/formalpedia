-- Prove2me | solution 1 for RH1E6S16.part_064_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:56:55.887071+00:00
-- url     : https://prove2.me/submissions/be3a5c2c-9ffb-428b-8eed-e57f93ab5cf0

import Definitions.Def_RH1E6S16_D064_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0512 : RS5.BandZeros ((61234090675 : ℝ) / 65536) ((61238467049 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0512.s0 RH1E6S16_0512.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0512.s0 RH1E6S16_0512.rest = RH1E6S16_0512.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0512.s0 :: RH1E6S16_0512.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0512.s0.t = ((61234090675 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0512.s0]
  have e1 : RH1E6S16_0512.sL.t = ((61238467049 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0512.sL]
  rw [e0, e1] at h
  exact h

theorem band_0513 : RS5.BandZeros ((61238467049 : ℝ) / 65536) ((61242881716 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0513.s0 RH1E6S16_0513.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0513.s0 RH1E6S16_0513.rest = RH1E6S16_0513.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0513.s0 :: RH1E6S16_0513.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0513.s0.t = ((61238467049 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0513.s0]
  have e1 : RH1E6S16_0513.sL.t = ((61242881716 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0513.sL]
  rw [e0, e1] at h
  exact h

theorem part_064_0 : RS5.BandZeros ((61234090675 : ℝ) / 65536) ((61242881716 : ℝ) / 65536) 254 := by
  have g0 := band_0512
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0513
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61234090675 : ℝ) / 65536) ((61242881716 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_064_0 <;> assumption
