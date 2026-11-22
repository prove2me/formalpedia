-- Prove2me | solution 1 for RH1E6S10.part_057_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T01:31:08.012724+00:00
-- url     : https://prove2.me/submissions/371d3e1a-2ebd-4273-9c5e-5dfc26553476

import Definitions.Def_RH1E6S10_D057_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0460 : RS5.BandZeros ((41414727296 : ℝ) / 65536) ((41419249456 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0460.s0 RH1E6S10_0460.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0460.s0 RH1E6S10_0460.rest = RH1E6S10_0460.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0460.s0 :: RH1E6S10_0460.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0460.s0.t = ((41414727296 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0460.s0]
  have e1 : RH1E6S10_0460.sL.t = ((41419249456 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0460.sL]
  rw [e0, e1] at h
  exact h

theorem band_0461 : RS5.BandZeros ((41419249456 : ℝ) / 65536) ((41423807321 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0461.s0 RH1E6S10_0461.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0461.s0 RH1E6S10_0461.rest = RH1E6S10_0461.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0461.s0 :: RH1E6S10_0461.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0461.s0.t = ((41419249456 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0461.s0]
  have e1 : RH1E6S10_0461.sL.t = ((41423807321 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0461.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_2 : RS5.BandZeros ((41414727296 : ℝ) / 65536) ((41423807321 : ℝ) / 65536) 254 := by
  have g0 := band_0460
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0461
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41414727296 : ℝ) / 65536) ((41423807321 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_057_2 <;> assumption
