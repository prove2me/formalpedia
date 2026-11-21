-- Prove2me | solution 1 for RH1E6S05.part_080_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T16:28:18.646804+00:00
-- url     : https://prove2.me/submissions/320d7fd2-fab0-4b40-a7c6-6334340d943d

import Definitions.Def_RH1E6S05_D080_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0646 : RS5.BandZeros ((26011012400 : ℝ) / 65536) ((26015724829 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0646.s0 RH1E6S05_0646.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0646.s0 RH1E6S05_0646.rest = RH1E6S05_0646.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0646.s0 :: RH1E6S05_0646.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0646.s0.t = ((26011012400 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0646.s0]
  have e1 : RH1E6S05_0646.sL.t = ((26015724829 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0646.sL]
  rw [e0, e1] at h
  exact h

theorem band_0647 : RS5.BandZeros ((26015724829 : ℝ) / 65536) ((26020465120 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0647.s0 RH1E6S05_0647.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0647.s0 RH1E6S05_0647.rest = RH1E6S05_0647.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0647.s0 :: RH1E6S05_0647.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0647.s0.t = ((26015724829 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0647.s0]
  have e1 : RH1E6S05_0647.sL.t = ((26020465120 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0647.sL]
  rw [e0, e1] at h
  exact h

theorem part_080_3 : RS5.BandZeros ((26011012400 : ℝ) / 65536) ((26020465120 : ℝ) / 65536) 254 := by
  have g0 := band_0646
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0647
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((26011012400 : ℝ) / 65536) ((26020465120 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_080_3 <;> assumption
