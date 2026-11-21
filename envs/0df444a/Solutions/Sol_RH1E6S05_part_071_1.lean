-- Prove2me | solution 1 for RH1E6S05.part_071_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T16:05:33.513909+00:00
-- url     : https://prove2.me/submissions/44d256cc-9ee7-4f81-8a0e-448e99c0d278

import Definitions.Def_RH1E6S05_D071_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0570 : RS5.BandZeros ((25651223086 : ℝ) / 65536) ((25655960110 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0570.s0 RH1E6S05_0570.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0570.s0 RH1E6S05_0570.rest = RH1E6S05_0570.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0570.s0 :: RH1E6S05_0570.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0570.s0.t = ((25651223086 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0570.s0]
  have e1 : RH1E6S05_0570.sL.t = ((25655960110 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0570.sL]
  rw [e0, e1] at h
  exact h

theorem band_0571 : RS5.BandZeros ((25655960110 : ℝ) / 65536) ((25660678405 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0571.s0 RH1E6S05_0571.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0571.s0 RH1E6S05_0571.rest = RH1E6S05_0571.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0571.s0 :: RH1E6S05_0571.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0571.s0.t = ((25655960110 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0571.s0]
  have e1 : RH1E6S05_0571.sL.t = ((25660678405 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0571.sL]
  rw [e0, e1] at h
  exact h

theorem part_071_1 : RS5.BandZeros ((25651223086 : ℝ) / 65536) ((25660678405 : ℝ) / 65536) 254 := by
  have g0 := band_0570
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0571
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25651223086 : ℝ) / 65536) ((25660678405 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_071_1 <;> assumption
