-- Prove2me | solution 1 for RH1E6S04.part_019_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:05:42.28451+00:00
-- url     : https://prove2.me/submissions/73fb1dcf-8cc1-40ea-b075-c9c059381778

import Definitions.Def_RH1E6S04_D019_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0152 : RS5.BandZeros ((20397361113 : ℝ) / 65536) ((20402189029 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0152.s0 RH1E6S04_0152.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0152.s0 RH1E6S04_0152.rest = RH1E6S04_0152.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0152.s0 :: RH1E6S04_0152.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0152.s0.t = ((20397361113 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0152.s0]
  have e1 : RH1E6S04_0152.sL.t = ((20402189029 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0152.sL]
  rw [e0, e1] at h
  exact h

theorem band_0153 : RS5.BandZeros ((20402189029 : ℝ) / 65536) ((20407016839 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0153.s0 RH1E6S04_0153.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0153.s0 RH1E6S04_0153.rest = RH1E6S04_0153.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0153.s0 :: RH1E6S04_0153.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0153.s0.t = ((20402189029 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0153.s0]
  have e1 : RH1E6S04_0153.sL.t = ((20407016839 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0153.sL]
  rw [e0, e1] at h
  exact h

theorem part_019_0 : RS5.BandZeros ((20397361113 : ℝ) / 65536) ((20407016839 : ℝ) / 65536) 254 := by
  have g0 := band_0152
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0153
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20397361113 : ℝ) / 65536) ((20407016839 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_019_0 <;> assumption
