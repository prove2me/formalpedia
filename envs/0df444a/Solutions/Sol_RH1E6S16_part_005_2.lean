-- Prove2me | solution 1 for RH1E6S16.part_005_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T14:08:53.553404+00:00
-- url     : https://prove2.me/submissions/d06b78cb-7b74-44e9-b2a6-b2d525d2b0a1

import Definitions.Def_RH1E6S16_D005_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0044 : RS5.BandZeros ((59176182374 : ℝ) / 65536) ((59180580439 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0044.s0 RH1E6S16_0044.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0044.s0 RH1E6S16_0044.rest = RH1E6S16_0044.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0044.s0 :: RH1E6S16_0044.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0044.s0.t = ((59176182374 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0044.s0]
  have e1 : RH1E6S16_0044.sL.t = ((59180580439 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0044.sL]
  rw [e0, e1] at h
  exact h

theorem band_0045 : RS5.BandZeros ((59180580439 : ℝ) / 65536) ((59184989303 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0045.s0 RH1E6S16_0045.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0045.s0 RH1E6S16_0045.rest = RH1E6S16_0045.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0045.s0 :: RH1E6S16_0045.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0045.s0.t = ((59180580439 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0045.s0]
  have e1 : RH1E6S16_0045.sL.t = ((59184989303 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0045.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_2 : RS5.BandZeros ((59176182374 : ℝ) / 65536) ((59184989303 : ℝ) / 65536) 254 := by
  have g0 := band_0044
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0045
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59176182374 : ℝ) / 65536) ((59184989303 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_005_2 <;> assumption
