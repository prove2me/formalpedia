-- Prove2me | solution 1 for RH1E6S17.part_079_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:59:11.09767+00:00
-- url     : https://prove2.me/submissions/cce6204f-cfac-4d23-b3b2-d260e111ce5f

import Definitions.Def_RH1E6S17_D079_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0632 : RS5.BandZeros ((65025379042 : ℝ) / 65536) ((65029722170 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0632.s0 RH1E6S17_0632.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0632.s0 RH1E6S17_0632.rest = RH1E6S17_0632.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0632.s0 :: RH1E6S17_0632.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0632.s0.t = ((65025379042 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0632.s0]
  have e1 : RH1E6S17_0632.sL.t = ((65029722170 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0632.sL]
  rw [e0, e1] at h
  exact h

theorem band_0633 : RS5.BandZeros ((65029722170 : ℝ) / 65536) ((65034099675 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0633.s0 RH1E6S17_0633.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0633.s0 RH1E6S17_0633.rest = RH1E6S17_0633.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0633.s0 :: RH1E6S17_0633.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0633.s0.t = ((65029722170 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0633.s0]
  have e1 : RH1E6S17_0633.sL.t = ((65034099675 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0633.sL]
  rw [e0, e1] at h
  exact h

theorem part_079_0 : RS5.BandZeros ((65025379042 : ℝ) / 65536) ((65034099675 : ℝ) / 65536) 254 := by
  have g0 := band_0632
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0633
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65025379042 : ℝ) / 65536) ((65034099675 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_079_0 <;> assumption
