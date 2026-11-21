-- Prove2me | solution 1 for RH1E6S07.part_039_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:47:08.435539+00:00
-- url     : https://prove2.me/submissions/e2908864-94ad-4588-abff-7448de1ec241

import Definitions.Def_RH1E6S07_D039_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0312 : RS5.BandZeros ((30947541122 : ℝ) / 65536) ((30952218394 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0312.s0 RH1E6S07_0312.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0312.s0 RH1E6S07_0312.rest = RH1E6S07_0312.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0312.s0 :: RH1E6S07_0312.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0312.s0.t = ((30947541122 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0312.s0]
  have e1 : RH1E6S07_0312.sL.t = ((30952218394 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0312.sL]
  rw [e0, e1] at h
  exact h

theorem band_0313 : RS5.BandZeros ((30952218394 : ℝ) / 65536) ((30956869209 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0313.s0 RH1E6S07_0313.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0313.s0 RH1E6S07_0313.rest = RH1E6S07_0313.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0313.s0 :: RH1E6S07_0313.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0313.s0.t = ((30952218394 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0313.s0]
  have e1 : RH1E6S07_0313.sL.t = ((30956869209 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0313.sL]
  rw [e0, e1] at h
  exact h

theorem part_039_0 : RS5.BandZeros ((30947541122 : ℝ) / 65536) ((30956869209 : ℝ) / 65536) 254 := by
  have g0 := band_0312
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0313
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30947541122 : ℝ) / 65536) ((30956869209 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_039_0 <;> assumption
