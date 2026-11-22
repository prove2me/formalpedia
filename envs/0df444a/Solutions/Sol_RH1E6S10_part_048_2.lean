-- Prove2me | solution 1 for RH1E6S10.part_048_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T01:08:38.046693+00:00
-- url     : https://prove2.me/submissions/d5266161-c5f5-436c-8f9d-1e5640da528e

import Definitions.Def_RH1E6S10_D048_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0388 : RS5.BandZeros ((41087704098 : ℝ) / 65536) ((41092265145 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0388.s0 RH1E6S10_0388.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0388.s0 RH1E6S10_0388.rest = RH1E6S10_0388.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0388.s0 :: RH1E6S10_0388.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0388.s0.t = ((41087704098 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0388.s0]
  have e1 : RH1E6S10_0388.sL.t = ((41092265145 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0388.sL]
  rw [e0, e1] at h
  exact h

theorem band_0389 : RS5.BandZeros ((41092265145 : ℝ) / 65536) ((41096799318 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0389.s0 RH1E6S10_0389.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0389.s0 RH1E6S10_0389.rest = RH1E6S10_0389.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0389.s0 :: RH1E6S10_0389.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0389.s0.t = ((41092265145 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0389.s0]
  have e1 : RH1E6S10_0389.sL.t = ((41096799318 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0389.sL]
  rw [e0, e1] at h
  exact h

theorem part_048_2 : RS5.BandZeros ((41087704098 : ℝ) / 65536) ((41096799318 : ℝ) / 65536) 254 := by
  have g0 := band_0388
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0389
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41087704098 : ℝ) / 65536) ((41096799318 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_048_2 <;> assumption
