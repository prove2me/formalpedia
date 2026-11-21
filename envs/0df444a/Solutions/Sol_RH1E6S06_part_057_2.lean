-- Prove2me | solution 1 for RH1E6S06.part_057_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T20:13:34.20621+00:00
-- url     : https://prove2.me/submissions/ac1afdc3-f16d-4df0-8754-71bab14db8da

import Definitions.Def_RH1E6S06_D057_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0460 : RS5.BandZeros ((28381303506 : ℝ) / 65536) ((28385973720 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0460.s0 RH1E6S06_0460.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0460.s0 RH1E6S06_0460.rest = RH1E6S06_0460.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0460.s0 :: RH1E6S06_0460.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0460.s0.t = ((28381303506 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0460.s0]
  have e1 : RH1E6S06_0460.sL.t = ((28385973720 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0460.sL]
  rw [e0, e1] at h
  exact h

theorem band_0461 : RS5.BandZeros ((28385973720 : ℝ) / 65536) ((28390688268 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0461.s0 RH1E6S06_0461.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0461.s0 RH1E6S06_0461.rest = RH1E6S06_0461.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0461.s0 :: RH1E6S06_0461.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0461.s0.t = ((28385973720 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0461.s0]
  have e1 : RH1E6S06_0461.sL.t = ((28390688268 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0461.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_2 : RS5.BandZeros ((28381303506 : ℝ) / 65536) ((28390688268 : ℝ) / 65536) 254 := by
  have g0 := band_0460
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0461
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28381303506 : ℝ) / 65536) ((28390688268 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_057_2 <;> assumption
