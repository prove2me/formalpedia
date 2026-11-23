-- Prove2me | solution 1 for RH1E6S17.part_024_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T20:53:12.159359+00:00
-- url     : https://prove2.me/submissions/7c335a07-0d0f-4245-a600-91d55067a99e

import Definitions.Def_RH1E6S17_D024_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0196 : RS5.BandZeros ((63118126282 : ℝ) / 65536) ((63122523347 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0196.s0 RH1E6S17_0196.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0196.s0 RH1E6S17_0196.rest = RH1E6S17_0196.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0196.s0 :: RH1E6S17_0196.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0196.s0.t = ((63118126282 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0196.s0]
  have e1 : RH1E6S17_0196.sL.t = ((63122523347 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0196.sL]
  rw [e0, e1] at h
  exact h

theorem band_0197 : RS5.BandZeros ((63122523347 : ℝ) / 65536) ((63126903143 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0197.s0 RH1E6S17_0197.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0197.s0 RH1E6S17_0197.rest = RH1E6S17_0197.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0197.s0 :: RH1E6S17_0197.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0197.s0.t = ((63122523347 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0197.s0]
  have e1 : RH1E6S17_0197.sL.t = ((63126903143 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0197.sL]
  rw [e0, e1] at h
  exact h

theorem part_024_2 : RS5.BandZeros ((63118126282 : ℝ) / 65536) ((63126903143 : ℝ) / 65536) 254 := by
  have g0 := band_0196
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0197
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63118126282 : ℝ) / 65536) ((63126903143 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_024_2 <;> assumption
