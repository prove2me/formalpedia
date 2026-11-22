-- Prove2me | solution 1 for RH1E6S09.part_022_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:12:02.520787+00:00
-- url     : https://prove2.me/submissions/0045900f-ebf1-43c1-a6e5-1432b5239288

import Definitions.Def_RH1E6S09_D022_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0182 : RS5.BandZeros ((36880317965 : ℝ) / 65536) ((36884887439 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0182.s0 RH1E6S09_0182.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0182.s0 RH1E6S09_0182.rest = RH1E6S09_0182.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0182.s0 :: RH1E6S09_0182.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0182.s0.t = ((36880317965 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0182.s0]
  have e1 : RH1E6S09_0182.sL.t = ((36884887439 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0182.sL]
  rw [e0, e1] at h
  exact h

theorem band_0183 : RS5.BandZeros ((36884887439 : ℝ) / 65536) ((36889469852 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0183.s0 RH1E6S09_0183.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0183.s0 RH1E6S09_0183.rest = RH1E6S09_0183.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0183.s0 :: RH1E6S09_0183.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0183.s0.t = ((36884887439 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0183.s0]
  have e1 : RH1E6S09_0183.sL.t = ((36889469852 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0183.sL]
  rw [e0, e1] at h
  exact h

theorem part_022_3 : RS5.BandZeros ((36880317965 : ℝ) / 65536) ((36889469852 : ℝ) / 65536) 254 := by
  have g0 := band_0182
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0183
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36880317965 : ℝ) / 65536) ((36889469852 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_022_3 <;> assumption
