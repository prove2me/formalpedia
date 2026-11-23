-- Prove2me | solution 1 for RH1E6S16.part_089_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:18:45.45711+00:00
-- url     : https://prove2.me/submissions/405f8738-144b-4aa4-bdd5-bebcfc7ae8bd

import Definitions.Def_RH1E6S16_D089_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0712 : RS5.BandZeros ((62111752872 : ℝ) / 65536) ((62116164112 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0712.s0 RH1E6S16_0712.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0712.s0 RH1E6S16_0712.rest = RH1E6S16_0712.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0712.s0 :: RH1E6S16_0712.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0712.s0.t = ((62111752872 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0712.s0]
  have e1 : RH1E6S16_0712.sL.t = ((62116164112 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0712.sL]
  rw [e0, e1] at h
  exact h

theorem band_0713 : RS5.BandZeros ((62116164112 : ℝ) / 65536) ((62120533806 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0713.s0 RH1E6S16_0713.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0713.s0 RH1E6S16_0713.rest = RH1E6S16_0713.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0713.s0 :: RH1E6S16_0713.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0713.s0.t = ((62116164112 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0713.s0]
  have e1 : RH1E6S16_0713.sL.t = ((62120533806 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0713.sL]
  rw [e0, e1] at h
  exact h

theorem part_089_0 : RS5.BandZeros ((62111752872 : ℝ) / 65536) ((62120533806 : ℝ) / 65536) 254 := by
  have g0 := band_0712
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0713
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62111752872 : ℝ) / 65536) ((62120533806 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_089_0 <;> assumption
