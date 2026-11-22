-- Prove2me | solution 1 for RH1E6S09.part_088_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T16:43:18.99373+00:00
-- url     : https://prove2.me/submissions/6ee00389-29c8-4c07-b662-caaa9e22dd66

import Definitions.Def_RH1E6S09_D088_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0708 : RS5.BandZeros ((39285933888 : ℝ) / 65536) ((39290477343 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0708.s0 RH1E6S09_0708.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0708.s0 RH1E6S09_0708.rest = RH1E6S09_0708.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0708.s0 :: RH1E6S09_0708.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0708.s0.t = ((39285933888 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0708.s0]
  have e1 : RH1E6S09_0708.sL.t = ((39290477343 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0708.sL]
  rw [e0, e1] at h
  exact h

theorem band_0709 : RS5.BandZeros ((39290477343 : ℝ) / 65536) ((39295053700 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0709.s0 RH1E6S09_0709.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0709.s0 RH1E6S09_0709.rest = RH1E6S09_0709.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0709.s0 :: RH1E6S09_0709.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0709.s0.t = ((39290477343 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0709.s0]
  have e1 : RH1E6S09_0709.sL.t = ((39295053700 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0709.sL]
  rw [e0, e1] at h
  exact h

theorem part_088_2 : RS5.BandZeros ((39285933888 : ℝ) / 65536) ((39295053700 : ℝ) / 65536) 254 := by
  have g0 := band_0708
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0709
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((39285933888 : ℝ) / 65536) ((39295053700 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_088_2 <;> assumption
