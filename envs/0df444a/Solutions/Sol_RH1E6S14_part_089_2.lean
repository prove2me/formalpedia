-- Prove2me | solution 1 for RH1E6S14.part_089_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:34:29.233847+00:00
-- url     : https://prove2.me/submissions/0c2cd341-f2f2-48c5-98fd-d7b9d8cd710c

import Definitions.Def_RH1E6S14_D089_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0716 : RS5.BandZeros ((55606226482 : ℝ) / 65536) ((55610659904 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0716.s0 RH1E6S14_0716.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0716.s0 RH1E6S14_0716.rest = RH1E6S14_0716.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0716.s0 :: RH1E6S14_0716.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0716.s0.t = ((55606226482 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0716.s0]
  have e1 : RH1E6S14_0716.sL.t = ((55610659904 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0716.sL]
  rw [e0, e1] at h
  exact h

theorem band_0717 : RS5.BandZeros ((55610659904 : ℝ) / 65536) ((55615076460 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0717.s0 RH1E6S14_0717.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0717.s0 RH1E6S14_0717.rest = RH1E6S14_0717.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0717.s0 :: RH1E6S14_0717.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0717.s0.t = ((55610659904 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0717.s0]
  have e1 : RH1E6S14_0717.sL.t = ((55615076460 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0717.sL]
  rw [e0, e1] at h
  exact h

theorem part_089_2 : RS5.BandZeros ((55606226482 : ℝ) / 65536) ((55615076460 : ℝ) / 65536) 254 := by
  have g0 := band_0716
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0717
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55606226482 : ℝ) / 65536) ((55615076460 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_089_2 <;> assumption
