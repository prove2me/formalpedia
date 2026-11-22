-- Prove2me | solution 1 for RH1E6S10.part_001_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T17:00:11.417607+00:00
-- url     : https://prove2.me/submissions/c5bf70c7-148a-4a06-8fe1-317dec9a0b89

import Definitions.Def_RH1E6S10_D001_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0014 : RS5.BandZeros ((39385483183 : ℝ) / 65536) ((39390016176 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0014.s0 RH1E6S10_0014.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0014.s0 RH1E6S10_0014.rest = RH1E6S10_0014.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0014.s0 :: RH1E6S10_0014.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0014.s0.t = ((39385483183 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0014.s0]
  have e1 : RH1E6S10_0014.sL.t = ((39390016176 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0014.sL]
  rw [e0, e1] at h
  exact h

theorem band_0015 : RS5.BandZeros ((39390016176 : ℝ) / 65536) ((39394594003 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0015.s0 RH1E6S10_0015.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0015.s0 RH1E6S10_0015.rest = RH1E6S10_0015.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0015.s0 :: RH1E6S10_0015.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0015.s0.t = ((39390016176 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0015.s0]
  have e1 : RH1E6S10_0015.sL.t = ((39394594003 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0015.sL]
  rw [e0, e1] at h
  exact h

theorem part_001_3 : RS5.BandZeros ((39385483183 : ℝ) / 65536) ((39394594003 : ℝ) / 65536) 254 := by
  have g0 := band_0014
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0015
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39385483183 : ℝ) / 65536) ((39394594003 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_001_3 <;> assumption
