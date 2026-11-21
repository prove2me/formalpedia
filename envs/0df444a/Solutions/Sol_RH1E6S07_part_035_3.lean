-- Prove2me | solution 1 for RH1E6S07.part_035_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:37:59.652207+00:00
-- url     : https://prove2.me/submissions/bad6ac05-52dc-4c55-b460-600e0c2d415c

import Definitions.Def_RH1E6S07_D035_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0286 : RS5.BandZeros ((30826427908 : ℝ) / 65536) ((30831096543 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0286.s0 RH1E6S07_0286.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0286.s0 RH1E6S07_0286.rest = RH1E6S07_0286.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0286.s0 :: RH1E6S07_0286.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0286.s0.t = ((30826427908 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0286.s0]
  have e1 : RH1E6S07_0286.sL.t = ((30831096543 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0286.sL]
  rw [e0, e1] at h
  exact h

theorem band_0287 : RS5.BandZeros ((30831096543 : ℝ) / 65536) ((30835754965 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0287.s0 RH1E6S07_0287.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0287.s0 RH1E6S07_0287.rest = RH1E6S07_0287.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0287.s0 :: RH1E6S07_0287.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0287.s0.t = ((30831096543 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0287.s0]
  have e1 : RH1E6S07_0287.sL.t = ((30835754965 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0287.sL]
  rw [e0, e1] at h
  exact h

theorem part_035_3 : RS5.BandZeros ((30826427908 : ℝ) / 65536) ((30835754965 : ℝ) / 65536) 254 := by
  have g0 := band_0286
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0287
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30826427908 : ℝ) / 65536) ((30835754965 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_035_3 <;> assumption
