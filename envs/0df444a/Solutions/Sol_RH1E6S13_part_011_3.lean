-- Prove2me | solution 1 for RH1E6S13.part_011_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T19:27:38.942508+00:00
-- url     : https://prove2.me/submissions/e465c505-df5d-4f31-81d1-e42c4587975c

import Definitions.Def_RH1E6S13_D011_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0094 : RS5.BandZeros ((49572347239 : ℝ) / 65536) ((49576826300 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0094.s0 RH1E6S13_0094.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0094.s0 RH1E6S13_0094.rest = RH1E6S13_0094.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0094.s0 :: RH1E6S13_0094.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0094.s0.t = ((49572347239 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0094.s0]
  have e1 : RH1E6S13_0094.sL.t = ((49576826300 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0094.sL]
  rw [e0, e1] at h
  exact h

theorem band_0095 : RS5.BandZeros ((49576826300 : ℝ) / 65536) ((49581305326 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0095.s0 RH1E6S13_0095.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0095.s0 RH1E6S13_0095.rest = RH1E6S13_0095.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0095.s0 :: RH1E6S13_0095.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0095.s0.t = ((49576826300 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0095.s0]
  have e1 : RH1E6S13_0095.sL.t = ((49581305326 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0095.sL]
  rw [e0, e1] at h
  exact h

theorem part_011_3 : RS5.BandZeros ((49572347239 : ℝ) / 65536) ((49581305326 : ℝ) / 65536) 254 := by
  have g0 := band_0094
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0095
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49572347239 : ℝ) / 65536) ((49581305326 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_011_3 <;> assumption
