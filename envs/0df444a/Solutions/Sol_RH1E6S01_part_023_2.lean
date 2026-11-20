-- Prove2me | solution 1 for RH1E6S01.part_023_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:10:17.682182+00:00
-- url     : https://prove2.me/submissions/b361da57-c9d9-418a-850d-12c1f9c091d9

import Definitions.Def_RH1E6S01_D023_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0188 : RS5.BandZeros ((10801099407 : ℝ) / 65536) ((10806228928 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0188.s0 RH1E6S01_0188.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0188.s0 RH1E6S01_0188.rest = RH1E6S01_0188.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0188.s0 :: RH1E6S01_0188.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0188.s0.t = ((10801099407 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0188.s0]
  have e1 : RH1E6S01_0188.sL.t = ((10806228928 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0188.sL]
  rw [e0, e1] at h
  exact h

theorem band_0189 : RS5.BandZeros ((10806228928 : ℝ) / 65536) ((10811358209 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0189.s0 RH1E6S01_0189.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0189.s0 RH1E6S01_0189.rest = RH1E6S01_0189.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0189.s0 :: RH1E6S01_0189.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0189.s0.t = ((10806228928 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0189.s0]
  have e1 : RH1E6S01_0189.sL.t = ((10811358209 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0189.sL]
  rw [e0, e1] at h
  exact h

theorem part_023_2 : RS5.BandZeros ((10801099407 : ℝ) / 65536) ((10811358209 : ℝ) / 65536) 254 := by
  have g0 := band_0188
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0189
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10801099407 : ℝ) / 65536) ((10811358209 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_023_2 <;> assumption
