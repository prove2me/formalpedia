-- Prove2me | solution 1 for RH1E6S14.part_026_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:58:47.826507+00:00
-- url     : https://prove2.me/submissions/614546e1-aa86-4753-ad1b-27677456b3f6

import Definitions.Def_RH1E6S14_D026_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0208 : RS5.BandZeros ((53353489783 : ℝ) / 65536) ((53357936769 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0208.s0 RH1E6S14_0208.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0208.s0 RH1E6S14_0208.rest = RH1E6S14_0208.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0208.s0 :: RH1E6S14_0208.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0208.s0.t = ((53353489783 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0208.s0]
  have e1 : RH1E6S14_0208.sL.t = ((53357936769 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0208.sL]
  rw [e0, e1] at h
  exact h

theorem band_0209 : RS5.BandZeros ((53357936769 : ℝ) / 65536) ((53362370343 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0209.s0 RH1E6S14_0209.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0209.s0 RH1E6S14_0209.rest = RH1E6S14_0209.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0209.s0 :: RH1E6S14_0209.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0209.s0.t = ((53357936769 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0209.s0]
  have e1 : RH1E6S14_0209.sL.t = ((53362370343 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0209.sL]
  rw [e0, e1] at h
  exact h

theorem part_026_0 : RS5.BandZeros ((53353489783 : ℝ) / 65536) ((53362370343 : ℝ) / 65536) 254 := by
  have g0 := band_0208
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0209
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53353489783 : ℝ) / 65536) ((53362370343 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_026_0 <;> assumption
