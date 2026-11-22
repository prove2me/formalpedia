-- Prove2me | solution 1 for RH1E6S11.part_056_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T05:39:10.499822+00:00
-- url     : https://prove2.me/submissions/1e1051e8-2153-4454-886b-f07b48741e26

import Definitions.Def_RH1E6S11_D056_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0452 : RS5.BandZeros ((44641317642 : ℝ) / 65536) ((44645828299 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0452.s0 RH1E6S11_0452.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0452.s0 RH1E6S11_0452.rest = RH1E6S11_0452.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0452.s0 :: RH1E6S11_0452.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0452.s0.t = ((44641317642 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0452.s0]
  have e1 : RH1E6S11_0452.sL.t = ((44645828299 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0452.sL]
  rw [e0, e1] at h
  exact h

theorem band_0453 : RS5.BandZeros ((44645828299 : ℝ) / 65536) ((44650330037 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0453.s0 RH1E6S11_0453.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0453.s0 RH1E6S11_0453.rest = RH1E6S11_0453.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0453.s0 :: RH1E6S11_0453.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0453.s0.t = ((44645828299 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0453.s0]
  have e1 : RH1E6S11_0453.sL.t = ((44650330037 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0453.sL]
  rw [e0, e1] at h
  exact h

theorem part_056_2 : RS5.BandZeros ((44641317642 : ℝ) / 65536) ((44650330037 : ℝ) / 65536) 254 := by
  have g0 := band_0452
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0453
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44641317642 : ℝ) / 65536) ((44650330037 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_056_2 <;> assumption
