-- Prove2me | solution 1 for RH1E6S16.part_072_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:24:59.696826+00:00
-- url     : https://prove2.me/submissions/9024ee0d-e7b1-4a44-96da-8fbf386388dd

import Definitions.Def_RH1E6S16_D072_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0582 : RS5.BandZeros ((61541393231 : ℝ) / 65536) ((61545777936 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0582.s0 RH1E6S16_0582.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0582.s0 RH1E6S16_0582.rest = RH1E6S16_0582.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0582.s0 :: RH1E6S16_0582.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0582.s0.t = ((61541393231 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0582.s0]
  have e1 : RH1E6S16_0582.sL.t = ((61545777936 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0582.sL]
  rw [e0, e1] at h
  exact h

theorem band_0583 : RS5.BandZeros ((61545777936 : ℝ) / 65536) ((61550178224 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0583.s0 RH1E6S16_0583.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0583.s0 RH1E6S16_0583.rest = RH1E6S16_0583.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0583.s0 :: RH1E6S16_0583.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0583.s0.t = ((61545777936 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0583.s0]
  have e1 : RH1E6S16_0583.sL.t = ((61550178224 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0583.sL]
  rw [e0, e1] at h
  exact h

theorem part_072_3 : RS5.BandZeros ((61541393231 : ℝ) / 65536) ((61550178224 : ℝ) / 65536) 254 := by
  have g0 := band_0582
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0583
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61541393231 : ℝ) / 65536) ((61550178224 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_072_3 <;> assumption
