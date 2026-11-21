-- Prove2me | solution 1 for RH1E6S03.part_036_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:35:25.766167+00:00
-- url     : https://prove2.me/submissions/1acb2408-20ac-42be-b245-ff6182ca6bf4

import Definitions.Def_RH1E6S03_D036_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0294 : RS5.BandZeros ((17829785144 : ℝ) / 65536) ((17834683533 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0294.s0 RH1E6S03_0294.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0294.s0 RH1E6S03_0294.rest = RH1E6S03_0294.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0294.s0 :: RH1E6S03_0294.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0294.s0.t = ((17829785144 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0294.s0]
  have e1 : RH1E6S03_0294.sL.t = ((17834683533 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0294.sL]
  rw [e0, e1] at h
  exact h

theorem band_0295 : RS5.BandZeros ((17834683533 : ℝ) / 65536) ((17839562511 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0295.s0 RH1E6S03_0295.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0295.s0 RH1E6S03_0295.rest = RH1E6S03_0295.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0295.s0 :: RH1E6S03_0295.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0295.s0.t = ((17834683533 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0295.s0]
  have e1 : RH1E6S03_0295.sL.t = ((17839562511 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0295.sL]
  rw [e0, e1] at h
  exact h

theorem part_036_3 : RS5.BandZeros ((17829785144 : ℝ) / 65536) ((17839562511 : ℝ) / 65536) 254 := by
  have g0 := band_0294
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0295
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17829785144 : ℝ) / 65536) ((17839562511 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_036_3 <;> assumption
