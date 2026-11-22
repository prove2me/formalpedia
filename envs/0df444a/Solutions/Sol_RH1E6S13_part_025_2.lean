-- Prove2me | solution 1 for RH1E6S13.part_025_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T21:43:51.116276+00:00
-- url     : https://prove2.me/submissions/3b2966c0-d00a-440a-91ac-6b90870653a2

import Definitions.Def_RH1E6S13_D025_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0204 : RS5.BandZeros ((50063896617 : ℝ) / 65536) ((50068354319 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0204.s0 RH1E6S13_0204.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0204.s0 RH1E6S13_0204.rest = RH1E6S13_0204.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0204.s0 :: RH1E6S13_0204.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0204.s0.t = ((50063896617 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0204.s0]
  have e1 : RH1E6S13_0204.sL.t = ((50068354319 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0204.sL]
  rw [e0, e1] at h
  exact h

theorem band_0205 : RS5.BandZeros ((50068354319 : ℝ) / 65536) ((50072820779 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0205.s0 RH1E6S13_0205.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0205.s0 RH1E6S13_0205.rest = RH1E6S13_0205.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0205.s0 :: RH1E6S13_0205.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0205.s0.t = ((50068354319 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0205.s0]
  have e1 : RH1E6S13_0205.sL.t = ((50072820779 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0205.sL]
  rw [e0, e1] at h
  exact h

theorem part_025_2 : RS5.BandZeros ((50063896617 : ℝ) / 65536) ((50072820779 : ℝ) / 65536) 254 := by
  have g0 := band_0204
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0205
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50063896617 : ℝ) / 65536) ((50072820779 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_025_2 <;> assumption
