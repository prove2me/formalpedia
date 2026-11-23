-- Prove2me | solution 1 for RH1E6S13.part_063_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T00:33:48.15116+00:00
-- url     : https://prove2.me/submissions/e001802c-420c-4747-88c4-d857bd3a3c0f

import Definitions.Def_RH1E6S13_D063_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0504 : RS5.BandZeros ((51402335300 : ℝ) / 65536) ((51406774207 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0504.s0 RH1E6S13_0504.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0504.s0 RH1E6S13_0504.rest = RH1E6S13_0504.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0504.s0 :: RH1E6S13_0504.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0504.s0.t = ((51402335300 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0504.s0]
  have e1 : RH1E6S13_0504.sL.t = ((51406774207 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0504.sL]
  rw [e0, e1] at h
  exact h

theorem band_0505 : RS5.BandZeros ((51406774207 : ℝ) / 65536) ((51411239399 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0505.s0 RH1E6S13_0505.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0505.s0 RH1E6S13_0505.rest = RH1E6S13_0505.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0505.s0 :: RH1E6S13_0505.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0505.s0.t = ((51406774207 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0505.s0]
  have e1 : RH1E6S13_0505.sL.t = ((51411239399 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0505.sL]
  rw [e0, e1] at h
  exact h

theorem part_063_0 : RS5.BandZeros ((51402335300 : ℝ) / 65536) ((51411239399 : ℝ) / 65536) 254 := by
  have g0 := band_0504
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0505
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51402335300 : ℝ) / 65536) ((51411239399 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_063_0 <;> assumption
