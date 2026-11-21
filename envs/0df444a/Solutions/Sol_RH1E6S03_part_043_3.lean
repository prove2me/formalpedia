-- Prove2me | solution 1 for RH1E6S03.part_043_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:52:30.679542+00:00
-- url     : https://prove2.me/submissions/c9a4856f-8b23-4d4d-8841-6c8ebcc6f372

import Definitions.Def_RH1E6S03_D043_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0350 : RS5.BandZeros ((18103892452 : ℝ) / 65536) ((18108793480 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0350.s0 RH1E6S03_0350.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0350.s0 RH1E6S03_0350.rest = RH1E6S03_0350.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0350.s0 :: RH1E6S03_0350.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0350.s0.t = ((18103892452 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0350.s0]
  have e1 : RH1E6S03_0350.sL.t = ((18108793480 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0350.sL]
  rw [e0, e1] at h
  exact h

theorem band_0351 : RS5.BandZeros ((18108793480 : ℝ) / 65536) ((18113704013 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0351.s0 RH1E6S03_0351.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0351.s0 RH1E6S03_0351.rest = RH1E6S03_0351.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0351.s0 :: RH1E6S03_0351.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0351.s0.t = ((18108793480 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0351.s0]
  have e1 : RH1E6S03_0351.sL.t = ((18113704013 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0351.sL]
  rw [e0, e1] at h
  exact h

theorem part_043_3 : RS5.BandZeros ((18103892452 : ℝ) / 65536) ((18113704013 : ℝ) / 65536) 254 := by
  have g0 := band_0350
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0351
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18103892452 : ℝ) / 65536) ((18113704013 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_043_3 <;> assumption
