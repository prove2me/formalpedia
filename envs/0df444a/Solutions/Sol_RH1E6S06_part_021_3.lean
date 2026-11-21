-- Prove2me | solution 1 for RH1E6S06.part_021_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:06:40.343003+00:00
-- url     : https://prove2.me/submissions/ca9acf7b-6901-4b58-93a8-ea2134ee661f

import Definitions.Def_RH1E6S06_D021_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0174 : RS5.BandZeros ((27035869393 : ℝ) / 65536) ((27040597232 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0174.s0 RH1E6S06_0174.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0174.s0 RH1E6S06_0174.rest = RH1E6S06_0174.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0174.s0 :: RH1E6S06_0174.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0174.s0.t = ((27035869393 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0174.s0]
  have e1 : RH1E6S06_0174.sL.t = ((27040597232 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0174.sL]
  rw [e0, e1] at h
  exact h

theorem band_0175 : RS5.BandZeros ((27040597232 : ℝ) / 65536) ((27045303054 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0175.s0 RH1E6S06_0175.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0175.s0 RH1E6S06_0175.rest = RH1E6S06_0175.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0175.s0 :: RH1E6S06_0175.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0175.s0.t = ((27040597232 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0175.s0]
  have e1 : RH1E6S06_0175.sL.t = ((27045303054 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0175.sL]
  rw [e0, e1] at h
  exact h

theorem part_021_3 : RS5.BandZeros ((27035869393 : ℝ) / 65536) ((27045303054 : ℝ) / 65536) 254 := by
  have g0 := band_0174
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0175
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27035869393 : ℝ) / 65536) ((27045303054 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_021_3 <;> assumption
