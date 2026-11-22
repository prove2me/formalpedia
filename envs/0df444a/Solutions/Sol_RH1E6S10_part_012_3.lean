-- Prove2me | solution 1 for RH1E6S10.part_012_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T18:12:51.361244+00:00
-- url     : https://prove2.me/submissions/cd9e69b8-fb13-405d-ad2d-a8afa24a8994

import Definitions.Def_RH1E6S10_D012_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0102 : RS5.BandZeros ((39786580769 : ℝ) / 65536) ((39791127697 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0102.s0 RH1E6S10_0102.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0102.s0 RH1E6S10_0102.rest = RH1E6S10_0102.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0102.s0 :: RH1E6S10_0102.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0102.s0.t = ((39786580769 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0102.s0]
  have e1 : RH1E6S10_0102.sL.t = ((39791127697 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0102.sL]
  rw [e0, e1] at h
  exact h

theorem band_0103 : RS5.BandZeros ((39791127697 : ℝ) / 65536) ((39795665611 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0103.s0 RH1E6S10_0103.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0103.s0 RH1E6S10_0103.rest = RH1E6S10_0103.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0103.s0 :: RH1E6S10_0103.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0103.s0.t = ((39791127697 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0103.s0]
  have e1 : RH1E6S10_0103.sL.t = ((39795665611 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0103.sL]
  rw [e0, e1] at h
  exact h

theorem part_012_3 : RS5.BandZeros ((39786580769 : ℝ) / 65536) ((39795665611 : ℝ) / 65536) 254 := by
  have g0 := band_0102
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0103
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39786580769 : ℝ) / 65536) ((39795665611 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_012_3 <;> assumption
