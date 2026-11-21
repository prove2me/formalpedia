-- Prove2me | solution 1 for RH1E6S06.part_016_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:53:52.256309+00:00
-- url     : https://prove2.me/submissions/c7d54e04-8922-40f1-a194-b492645f33b4

import Definitions.Def_RH1E6S06_D016_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0132 : RS5.BandZeros ((26837805420 : ℝ) / 65536) ((26842517378 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0132.s0 RH1E6S06_0132.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0132.s0 RH1E6S06_0132.rest = RH1E6S06_0132.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0132.s0 :: RH1E6S06_0132.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0132.s0.t = ((26837805420 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0132.s0]
  have e1 : RH1E6S06_0132.sL.t = ((26842517378 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0132.sL]
  rw [e0, e1] at h
  exact h

theorem band_0133 : RS5.BandZeros ((26842517378 : ℝ) / 65536) ((26847250035 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0133.s0 RH1E6S06_0133.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0133.s0 RH1E6S06_0133.rest = RH1E6S06_0133.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0133.s0 :: RH1E6S06_0133.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0133.s0.t = ((26842517378 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0133.s0]
  have e1 : RH1E6S06_0133.sL.t = ((26847250035 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0133.sL]
  rw [e0, e1] at h
  exact h

theorem part_016_2 : RS5.BandZeros ((26837805420 : ℝ) / 65536) ((26847250035 : ℝ) / 65536) 254 := by
  have g0 := band_0132
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0133
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26837805420 : ℝ) / 65536) ((26847250035 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_016_2 <;> assumption
