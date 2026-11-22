-- Prove2me | solution 1 for RH1E6S09.part_033_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:45:32.810163+00:00
-- url     : https://prove2.me/submissions/4febfbe9-2c93-4ebf-aaf6-e8acd477db43

import Definitions.Def_RH1E6S09_D033_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0266 : RS5.BandZeros ((37265373765 : ℝ) / 65536) ((37269964811 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0266.s0 RH1E6S09_0266.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0266.s0 RH1E6S09_0266.rest = RH1E6S09_0266.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0266.s0 :: RH1E6S09_0266.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0266.s0.t = ((37265373765 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0266.s0]
  have e1 : RH1E6S09_0266.sL.t = ((37269964811 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0266.sL]
  rw [e0, e1] at h
  exact h

theorem band_0267 : RS5.BandZeros ((37269964811 : ℝ) / 65536) ((37274540098 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0267.s0 RH1E6S09_0267.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0267.s0 RH1E6S09_0267.rest = RH1E6S09_0267.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0267.s0 :: RH1E6S09_0267.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0267.s0.t = ((37269964811 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0267.s0]
  have e1 : RH1E6S09_0267.sL.t = ((37274540098 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0267.sL]
  rw [e0, e1] at h
  exact h

theorem part_033_1 : RS5.BandZeros ((37265373765 : ℝ) / 65536) ((37274540098 : ℝ) / 65536) 254 := by
  have g0 := band_0266
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0267
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37265373765 : ℝ) / 65536) ((37274540098 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_033_1 <;> assumption
