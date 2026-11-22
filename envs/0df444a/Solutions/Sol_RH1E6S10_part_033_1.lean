-- Prove2me | solution 1 for RH1E6S10.part_033_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:45:44.86011+00:00
-- url     : https://prove2.me/submissions/8d55e108-8337-4126-986a-7d5e3f82e475

import Definitions.Def_RH1E6S10_D033_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0266 : RS5.BandZeros ((40533145024 : ℝ) / 65536) ((40537675646 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0266.s0 RH1E6S10_0266.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0266.s0 RH1E6S10_0266.rest = RH1E6S10_0266.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0266.s0 :: RH1E6S10_0266.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0266.s0.t = ((40533145024 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0266.s0]
  have e1 : RH1E6S10_0266.sL.t = ((40537675646 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0266.sL]
  rw [e0, e1] at h
  exact h

theorem band_0267 : RS5.BandZeros ((40537675646 : ℝ) / 65536) ((40542233086 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0267.s0 RH1E6S10_0267.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0267.s0 RH1E6S10_0267.rest = RH1E6S10_0267.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0267.s0 :: RH1E6S10_0267.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0267.s0.t = ((40537675646 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0267.s0]
  have e1 : RH1E6S10_0267.sL.t = ((40542233086 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0267.sL]
  rw [e0, e1] at h
  exact h

theorem part_033_1 : RS5.BandZeros ((40533145024 : ℝ) / 65536) ((40542233086 : ℝ) / 65536) 254 := by
  have g0 := band_0266
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0267
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40533145024 : ℝ) / 65536) ((40542233086 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_033_1 <;> assumption
