-- Prove2me | solution 1 for RH1E6S13.part_028_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T21:57:52.436105+00:00
-- url     : https://prove2.me/submissions/260f1a8a-30dd-4678-8453-c1a9057e8414

import Definitions.Def_RH1E6S13_D028_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0230 : RS5.BandZeros ((50179988042 : ℝ) / 65536) ((50184471233 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0230.s0 RH1E6S13_0230.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0230.s0 RH1E6S13_0230.rest = RH1E6S13_0230.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0230.s0 :: RH1E6S13_0230.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0230.s0.t = ((50179988042 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0230.s0]
  have e1 : RH1E6S13_0230.sL.t = ((50184471233 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0230.sL]
  rw [e0, e1] at h
  exact h

theorem band_0231 : RS5.BandZeros ((50184471233 : ℝ) / 65536) ((50188928020 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0231.s0 RH1E6S13_0231.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0231.s0 RH1E6S13_0231.rest = RH1E6S13_0231.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0231.s0 :: RH1E6S13_0231.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0231.s0.t = ((50184471233 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0231.s0]
  have e1 : RH1E6S13_0231.sL.t = ((50188928020 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0231.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_3 : RS5.BandZeros ((50179988042 : ℝ) / 65536) ((50188928020 : ℝ) / 65536) 254 := by
  have g0 := band_0230
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0231
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50179988042 : ℝ) / 65536) ((50188928020 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_028_3 <;> assumption
