-- Prove2me | solution 1 for RH1E6S15.part_007_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:10:43.861888+00:00
-- url     : https://prove2.me/submissions/d350aed1-6526-495c-93a6-55f65d892d7f

import Definitions.Def_RH1E6S15_D007_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0056 : RS5.BandZeros ((55953392201 : ℝ) / 65536) ((55957804936 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0056.s0 RH1E6S15_0056.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0056.s0 RH1E6S15_0056.rest = RH1E6S15_0056.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0056.s0 :: RH1E6S15_0056.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0056.s0.t = ((55953392201 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0056.s0]
  have e1 : RH1E6S15_0056.sL.t = ((55957804936 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0056.sL]
  rw [e0, e1] at h
  exact h

theorem band_0057 : RS5.BandZeros ((55957804936 : ℝ) / 65536) ((55962227422 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0057.s0 RH1E6S15_0057.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0057.s0 RH1E6S15_0057.rest = RH1E6S15_0057.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0057.s0 :: RH1E6S15_0057.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0057.s0.t = ((55957804936 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0057.s0]
  have e1 : RH1E6S15_0057.sL.t = ((55962227422 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0057.sL]
  rw [e0, e1] at h
  exact h

theorem part_007_0 : RS5.BandZeros ((55953392201 : ℝ) / 65536) ((55962227422 : ℝ) / 65536) 254 := by
  have g0 := band_0056
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0057
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((55953392201 : ℝ) / 65536) ((55962227422 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_007_0 <;> assumption
