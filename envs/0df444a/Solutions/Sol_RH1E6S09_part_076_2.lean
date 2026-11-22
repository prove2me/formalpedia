-- Prove2me | solution 1 for RH1E6S09.part_076_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T15:05:44.715464+00:00
-- url     : https://prove2.me/submissions/6717dfe4-2c78-4e7e-b750-7c557db9c6f6

import Definitions.Def_RH1E6S09_D076_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0612 : RS5.BandZeros ((38847863289 : ℝ) / 65536) ((38852421280 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0612.s0 RH1E6S09_0612.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0612.s0 RH1E6S09_0612.rest = RH1E6S09_0612.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0612.s0 :: RH1E6S09_0612.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0612.s0.t = ((38847863289 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0612.s0]
  have e1 : RH1E6S09_0612.sL.t = ((38852421280 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0612.sL]
  rw [e0, e1] at h
  exact h

theorem band_0613 : RS5.BandZeros ((38852421280 : ℝ) / 65536) ((38857000059 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0613.s0 RH1E6S09_0613.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0613.s0 RH1E6S09_0613.rest = RH1E6S09_0613.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0613.s0 :: RH1E6S09_0613.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0613.s0.t = ((38852421280 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0613.s0]
  have e1 : RH1E6S09_0613.sL.t = ((38857000059 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0613.sL]
  rw [e0, e1] at h
  exact h

theorem part_076_2 : RS5.BandZeros ((38847863289 : ℝ) / 65536) ((38857000059 : ℝ) / 65536) 254 := by
  have g0 := band_0612
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0613
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38847863289 : ℝ) / 65536) ((38857000059 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_076_2 <;> assumption
