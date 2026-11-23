-- Prove2me | solution 1 for RH1E6S15.part_005_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:01:55.362795+00:00
-- url     : https://prove2.me/submissions/bc7c37d5-c8fe-4837-a911-62ca42406367

import Definitions.Def_RH1E6S15_D005_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0042 : RS5.BandZeros ((55891430923 : ℝ) / 65536) ((55895871428 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0042.s0 RH1E6S15_0042.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0042.s0 RH1E6S15_0042.rest = RH1E6S15_0042.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0042.s0 :: RH1E6S15_0042.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0042.s0.t = ((55891430923 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0042.s0]
  have e1 : RH1E6S15_0042.sL.t = ((55895871428 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0042.sL]
  rw [e0, e1] at h
  exact h

theorem band_0043 : RS5.BandZeros ((55895871428 : ℝ) / 65536) ((55900285478 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0043.s0 RH1E6S15_0043.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0043.s0 RH1E6S15_0043.rest = RH1E6S15_0043.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0043.s0 :: RH1E6S15_0043.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0043.s0.t = ((55895871428 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0043.s0]
  have e1 : RH1E6S15_0043.sL.t = ((55900285478 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0043.sL]
  rw [e0, e1] at h
  exact h

theorem part_005_1 : RS5.BandZeros ((55891430923 : ℝ) / 65536) ((55900285478 : ℝ) / 65536) 254 := by
  have g0 := band_0042
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0043
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((55891430923 : ℝ) / 65536) ((55900285478 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_005_1 <;> assumption
