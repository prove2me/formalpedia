-- Prove2me | solution 1 for RH1E6S13.part_070_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T01:13:22.136408+00:00
-- url     : https://prove2.me/submissions/9fe8b60f-6880-4ebc-8da7-05f926c7fe94

import Definitions.Def_RH1E6S13_D070_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0562 : RS5.BandZeros ((51660755233 : ℝ) / 65536) ((51665201013 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0562.s0 RH1E6S13_0562.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0562.s0 RH1E6S13_0562.rest = RH1E6S13_0562.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0562.s0 :: RH1E6S13_0562.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0562.s0.t = ((51660755233 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0562.s0]
  have e1 : RH1E6S13_0562.sL.t = ((51665201013 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0562.sL]
  rw [e0, e1] at h
  exact h

theorem band_0563 : RS5.BandZeros ((51665201013 : ℝ) / 65536) ((51669655529 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0563.s0 RH1E6S13_0563.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0563.s0 RH1E6S13_0563.rest = RH1E6S13_0563.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0563.s0 :: RH1E6S13_0563.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0563.s0.t = ((51665201013 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0563.s0]
  have e1 : RH1E6S13_0563.sL.t = ((51669655529 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0563.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_1 : RS5.BandZeros ((51660755233 : ℝ) / 65536) ((51669655529 : ℝ) / 65536) 254 := by
  have g0 := band_0562
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0563
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51660755233 : ℝ) / 65536) ((51669655529 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_070_1 <;> assumption
