-- Prove2me | solution 1 for RH1E6S09.part_088_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T16:41:21.612181+00:00
-- url     : https://prove2.me/submissions/ac473c66-0b13-4dcf-860c-62117f49b041

import Definitions.Def_RH1E6S09_D088_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0706 : RS5.BandZeros ((39276812379 : ℝ) / 65536) ((39281355442 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0706.s0 RH1E6S09_0706.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0706.s0 RH1E6S09_0706.rest = RH1E6S09_0706.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0706.s0 :: RH1E6S09_0706.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0706.s0.t = ((39276812379 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0706.s0]
  have e1 : RH1E6S09_0706.sL.t = ((39281355442 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0706.sL]
  rw [e0, e1] at h
  exact h

theorem band_0707 : RS5.BandZeros ((39281355442 : ℝ) / 65536) ((39285933888 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0707.s0 RH1E6S09_0707.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0707.s0 RH1E6S09_0707.rest = RH1E6S09_0707.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0707.s0 :: RH1E6S09_0707.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0707.s0.t = ((39281355442 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0707.s0]
  have e1 : RH1E6S09_0707.sL.t = ((39285933888 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0707.sL]
  rw [e0, e1] at h
  exact h

theorem part_088_1 : RS5.BandZeros ((39276812379 : ℝ) / 65536) ((39285933888 : ℝ) / 65536) 254 := by
  have g0 := band_0706
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0707
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((39276812379 : ℝ) / 65536) ((39285933888 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_088_1 <;> assumption
