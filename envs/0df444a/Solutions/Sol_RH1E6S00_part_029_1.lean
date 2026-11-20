-- Prove2me | solution 1 for RH1E6S00.part_029_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:44:53.617541+00:00
-- url     : https://prove2.me/submissions/e5854ccc-999d-42b3-8f84-f8da474002a3

import Definitions.Def_RH1E6S00_D029_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0234 : RS5.BandZeros ((7806790125 : ℝ) / 65536) ((7812088655 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0234.s0 RH1E6S00_0234.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0234.s0 RH1E6S00_0234.rest = RH1E6S00_0234.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0234.s0 :: RH1E6S00_0234.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0234.s0.t = ((7806790125 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0234.s0]
  have e1 : RH1E6S00_0234.sL.t = ((7812088655 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0234.sL]
  rw [e0, e1] at h
  exact h

theorem band_0235 : RS5.BandZeros ((7812088655 : ℝ) / 65536) ((7817386820 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0235.s0 RH1E6S00_0235.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0235.s0 RH1E6S00_0235.rest = RH1E6S00_0235.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0235.s0 :: RH1E6S00_0235.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0235.s0.t = ((7812088655 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0235.s0]
  have e1 : RH1E6S00_0235.sL.t = ((7817386820 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0235.sL]
  rw [e0, e1] at h
  exact h

theorem part_029_1 : RS5.BandZeros ((7806790125 : ℝ) / 65536) ((7817386820 : ℝ) / 65536) 254 := by
  have g0 := band_0234
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0235
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7806790125 : ℝ) / 65536) ((7817386820 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_029_1 <;> assumption
