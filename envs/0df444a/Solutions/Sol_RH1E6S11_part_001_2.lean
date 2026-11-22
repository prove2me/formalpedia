-- Prove2me | solution 1 for RH1E6S11.part_001_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:06:41.81756+00:00
-- url     : https://prove2.me/submissions/75fae2a3-3a02-4d3b-a313-94bb7e86f69b

import Definitions.Def_RH1E6S11_D001_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0012 : RS5.BandZeros ((42652750516 : ℝ) / 65536) ((42657270057 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0012.s0 RH1E6S11_0012.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0012.s0 RH1E6S11_0012.rest = RH1E6S11_0012.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0012.s0 :: RH1E6S11_0012.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0012.s0.t = ((42652750516 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0012.s0]
  have e1 : RH1E6S11_0012.sL.t = ((42657270057 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0012.sL]
  rw [e0, e1] at h
  exact h

theorem band_0013 : RS5.BandZeros ((42657270057 : ℝ) / 65536) ((42661807384 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0013.s0 RH1E6S11_0013.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0013.s0 RH1E6S11_0013.rest = RH1E6S11_0013.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0013.s0 :: RH1E6S11_0013.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0013.s0.t = ((42657270057 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0013.s0]
  have e1 : RH1E6S11_0013.sL.t = ((42661807384 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0013.sL]
  rw [e0, e1] at h
  exact h

theorem part_001_2 : RS5.BandZeros ((42652750516 : ℝ) / 65536) ((42661807384 : ℝ) / 65536) 254 := by
  have g0 := band_0012
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0013
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((42652750516 : ℝ) / 65536) ((42661807384 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_001_2 <;> assumption
