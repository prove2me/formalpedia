-- Prove2me | solution 1 for RH1E6S09.part_084_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T16:16:58.497674+00:00
-- url     : https://prove2.me/submissions/712bd80d-b606-4103-ad6e-409bad1f013b

import Definitions.Def_RH1E6S09_D084_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0678 : RS5.BandZeros ((39149081704 : ℝ) / 65536) ((39153632375 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0678.s0 RH1E6S09_0678.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0678.s0 RH1E6S09_0678.rest = RH1E6S09_0678.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0678.s0 :: RH1E6S09_0678.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0678.s0.t = ((39149081704 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0678.s0]
  have e1 : RH1E6S09_0678.sL.t = ((39153632375 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0678.sL]
  rw [e0, e1] at h
  exact h

theorem band_0679 : RS5.BandZeros ((39153632375 : ℝ) / 65536) ((39158193792 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0679.s0 RH1E6S09_0679.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0679.s0 RH1E6S09_0679.rest = RH1E6S09_0679.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0679.s0 :: RH1E6S09_0679.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0679.s0.t = ((39153632375 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0679.s0]
  have e1 : RH1E6S09_0679.sL.t = ((39158193792 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0679.sL]
  rw [e0, e1] at h
  exact h

theorem part_084_3 : RS5.BandZeros ((39149081704 : ℝ) / 65536) ((39158193792 : ℝ) / 65536) 254 := by
  have g0 := band_0678
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0679
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((39149081704 : ℝ) / 65536) ((39158193792 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_084_3 <;> assumption
