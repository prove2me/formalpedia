-- Prove2me | solution 1 for RH1E6S11.part_052_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T05:27:44.046506+00:00
-- url     : https://prove2.me/submissions/df11f2b8-4d1b-49eb-a5fd-268d6915252e

import Definitions.Def_RH1E6S11_D052_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0416 : RS5.BandZeros ((44478907769 : ℝ) / 65536) ((44483410962 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0416.s0 RH1E6S11_0416.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0416.s0 RH1E6S11_0416.rest = RH1E6S11_0416.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0416.s0 :: RH1E6S11_0416.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0416.s0.t = ((44478907769 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0416.s0]
  have e1 : RH1E6S11_0416.sL.t = ((44483410962 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0416.sL]
  rw [e0, e1] at h
  exact h

theorem band_0417 : RS5.BandZeros ((44483410962 : ℝ) / 65536) ((44487931880 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0417.s0 RH1E6S11_0417.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0417.s0 RH1E6S11_0417.rest = RH1E6S11_0417.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0417.s0 :: RH1E6S11_0417.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0417.s0.t = ((44483410962 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0417.s0]
  have e1 : RH1E6S11_0417.sL.t = ((44487931880 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0417.sL]
  rw [e0, e1] at h
  exact h

theorem part_052_0 : RS5.BandZeros ((44478907769 : ℝ) / 65536) ((44487931880 : ℝ) / 65536) 254 := by
  have g0 := band_0416
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0417
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44478907769 : ℝ) / 65536) ((44487931880 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_052_0 <;> assumption
