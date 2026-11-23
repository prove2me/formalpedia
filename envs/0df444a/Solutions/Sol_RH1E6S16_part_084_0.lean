-- Prove2me | solution 1 for RH1E6S16.part_084_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:02:52.997546+00:00
-- url     : https://prove2.me/submissions/bdd5faf8-356c-49c5-a31e-d6ad42022a37

import Definitions.Def_RH1E6S16_D084_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0672 : RS5.BandZeros ((61936314830 : ℝ) / 65536) ((61940701205 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0672.s0 RH1E6S16_0672.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0672.s0 RH1E6S16_0672.rest = RH1E6S16_0672.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0672.s0 :: RH1E6S16_0672.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0672.s0.t = ((61936314830 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0672.s0]
  have e1 : RH1E6S16_0672.sL.t = ((61940701205 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0672.sL]
  rw [e0, e1] at h
  exact h

theorem band_0673 : RS5.BandZeros ((61940701205 : ℝ) / 65536) ((61945084694 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0673.s0 RH1E6S16_0673.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0673.s0 RH1E6S16_0673.rest = RH1E6S16_0673.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0673.s0 :: RH1E6S16_0673.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0673.s0.t = ((61940701205 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0673.s0]
  have e1 : RH1E6S16_0673.sL.t = ((61945084694 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0673.sL]
  rw [e0, e1] at h
  exact h

theorem part_084_0 : RS5.BandZeros ((61936314830 : ℝ) / 65536) ((61945084694 : ℝ) / 65536) 254 := by
  have g0 := band_0672
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0673
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61936314830 : ℝ) / 65536) ((61945084694 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_084_0 <;> assumption
