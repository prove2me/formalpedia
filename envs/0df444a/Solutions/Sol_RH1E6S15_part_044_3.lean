-- Prove2me | solution 1 for RH1E6S15.part_044_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:29:35.547833+00:00
-- url     : https://prove2.me/submissions/945af29f-1fdd-4952-99b6-34dd923375fa

import Definitions.Def_RH1E6S15_D044_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0358 : RS5.BandZeros ((57288249328 : ℝ) / 65536) ((57292650523 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0358.s0 RH1E6S15_0358.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0358.s0 RH1E6S15_0358.rest = RH1E6S15_0358.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0358.s0 :: RH1E6S15_0358.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0358.s0.t = ((57288249328 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0358.s0]
  have e1 : RH1E6S15_0358.sL.t = ((57292650523 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0358.sL]
  rw [e0, e1] at h
  exact h

theorem band_0359 : RS5.BandZeros ((57292650523 : ℝ) / 65536) ((57297078737 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0359.s0 RH1E6S15_0359.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0359.s0 RH1E6S15_0359.rest = RH1E6S15_0359.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0359.s0 :: RH1E6S15_0359.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0359.s0.t = ((57292650523 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0359.s0]
  have e1 : RH1E6S15_0359.sL.t = ((57297078737 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0359.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_3 : RS5.BandZeros ((57288249328 : ℝ) / 65536) ((57297078737 : ℝ) / 65536) 254 := by
  have g0 := band_0358
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0359
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57288249328 : ℝ) / 65536) ((57297078737 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_044_3 <;> assumption
