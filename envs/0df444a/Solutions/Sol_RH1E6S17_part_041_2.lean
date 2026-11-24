-- Prove2me | solution 1 for RH1E6S17.part_041_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:57:35.305185+00:00
-- url     : https://prove2.me/submissions/bfe3fe39-cbda-4fc3-ba48-a544e7877586

import Definitions.Def_RH1E6S17_D041_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0332 : RS5.BandZeros ((63713575101 : ℝ) / 65536) ((63717934251 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0332.s0 RH1E6S17_0332.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0332.s0 RH1E6S17_0332.rest = RH1E6S17_0332.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0332.s0 :: RH1E6S17_0332.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0332.s0.t = ((63713575101 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0332.s0]
  have e1 : RH1E6S17_0332.sL.t = ((63717934251 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0332.sL]
  rw [e0, e1] at h
  exact h

theorem band_0333 : RS5.BandZeros ((63717934251 : ℝ) / 65536) ((63722310606 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0333.s0 RH1E6S17_0333.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0333.s0 RH1E6S17_0333.rest = RH1E6S17_0333.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0333.s0 :: RH1E6S17_0333.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0333.s0.t = ((63717934251 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0333.s0]
  have e1 : RH1E6S17_0333.sL.t = ((63722310606 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0333.sL]
  rw [e0, e1] at h
  exact h

theorem part_041_2 : RS5.BandZeros ((63713575101 : ℝ) / 65536) ((63722310606 : ℝ) / 65536) 254 := by
  have g0 := band_0332
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0333
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63713575101 : ℝ) / 65536) ((63722310606 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_041_2 <;> assumption
