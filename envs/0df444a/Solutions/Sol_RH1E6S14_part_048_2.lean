-- Prove2me | solution 1 for RH1E6S14.part_048_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T05:20:12.056463+00:00
-- url     : https://prove2.me/submissions/79039902-c660-4d98-803a-9889bde167dd

import Definitions.Def_RH1E6S14_D048_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0388 : RS5.BandZeros ((54152605553 : ℝ) / 65536) ((54157046881 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0388.s0 RH1E6S14_0388.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0388.s0 RH1E6S14_0388.rest = RH1E6S14_0388.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0388.s0 :: RH1E6S14_0388.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0388.s0.t = ((54152605553 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0388.s0]
  have e1 : RH1E6S14_0388.sL.t = ((54157046881 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0388.sL]
  rw [e0, e1] at h
  exact h

theorem band_0389 : RS5.BandZeros ((54157046881 : ℝ) / 65536) ((54161486163 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0389.s0 RH1E6S14_0389.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0389.s0 RH1E6S14_0389.rest = RH1E6S14_0389.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0389.s0 :: RH1E6S14_0389.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0389.s0.t = ((54157046881 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0389.s0]
  have e1 : RH1E6S14_0389.sL.t = ((54161486163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0389.sL]
  rw [e0, e1] at h
  exact h

theorem part_048_2 : RS5.BandZeros ((54152605553 : ℝ) / 65536) ((54161486163 : ℝ) / 65536) 254 := by
  have g0 := band_0388
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0389
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54152605553 : ℝ) / 65536) ((54161486163 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_048_2 <;> assumption
