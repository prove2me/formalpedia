-- Prove2me | solution 1 for RH1E6S09.part_080_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T15:49:28.146528+00:00
-- url     : https://prove2.me/submissions/00e2fa60-8d31-48b4-8eb6-aa869c08aa8a

import Definitions.Def_RH1E6S09_D080_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0642 : RS5.BandZeros ((38984792766 : ℝ) / 65536) ((38989368273 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0642.s0 RH1E6S09_0642.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0642.s0 RH1E6S09_0642.rest = RH1E6S09_0642.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0642.s0 :: RH1E6S09_0642.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0642.s0.t = ((38984792766 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0642.s0]
  have e1 : RH1E6S09_0642.sL.t = ((38989368273 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0642.sL]
  rw [e0, e1] at h
  exact h

theorem band_0643 : RS5.BandZeros ((38989368273 : ℝ) / 65536) ((38993943160 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0643.s0 RH1E6S09_0643.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0643.s0 RH1E6S09_0643.rest = RH1E6S09_0643.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0643.s0 :: RH1E6S09_0643.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0643.s0.t = ((38989368273 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0643.s0]
  have e1 : RH1E6S09_0643.sL.t = ((38993943160 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0643.sL]
  rw [e0, e1] at h
  exact h

theorem part_080_1 : RS5.BandZeros ((38984792766 : ℝ) / 65536) ((38993943160 : ℝ) / 65536) 254 := by
  have g0 := band_0642
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0643
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38984792766 : ℝ) / 65536) ((38993943160 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_080_1 <;> assumption
