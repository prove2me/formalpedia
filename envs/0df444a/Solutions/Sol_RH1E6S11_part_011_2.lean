-- Prove2me | solution 1 for RH1E6S11.part_011_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T16:29:42.332806+00:00
-- url     : https://prove2.me/submissions/ff810a12-216a-4db0-a955-ac1338245911

import Definitions.Def_RH1E6S11_D011_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0092 : RS5.BandZeros ((43014886891 : ℝ) / 65536) ((43019420941 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0092.s0 RH1E6S11_0092.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0092.s0 RH1E6S11_0092.rest = RH1E6S11_0092.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0092.s0 :: RH1E6S11_0092.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0092.s0.t = ((43014886891 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0092.s0]
  have e1 : RH1E6S11_0092.sL.t = ((43019420941 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0092.sL]
  rw [e0, e1] at h
  exact h

theorem band_0093 : RS5.BandZeros ((43019420941 : ℝ) / 65536) ((43023919318 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0093.s0 RH1E6S11_0093.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0093.s0 RH1E6S11_0093.rest = RH1E6S11_0093.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0093.s0 :: RH1E6S11_0093.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0093.s0.t = ((43019420941 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0093.s0]
  have e1 : RH1E6S11_0093.sL.t = ((43023919318 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0093.sL]
  rw [e0, e1] at h
  exact h

theorem part_011_2 : RS5.BandZeros ((43014886891 : ℝ) / 65536) ((43023919318 : ℝ) / 65536) 254 := by
  have g0 := band_0092
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0093
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43014886891 : ℝ) / 65536) ((43023919318 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_011_2 <;> assumption
