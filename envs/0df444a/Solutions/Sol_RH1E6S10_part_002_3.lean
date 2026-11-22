-- Prove2me | solution 1 for RH1E6S10.part_002_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T17:07:41.135206+00:00
-- url     : https://prove2.me/submissions/c6c6c65b-2cbc-4b76-9f2f-d3ea76cb36b4

import Definitions.Def_RH1E6S10_D002_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0022 : RS5.BandZeros ((39421943312 : ℝ) / 65536) ((39426502865 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0022.s0 RH1E6S10_0022.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0022.s0 RH1E6S10_0022.rest = RH1E6S10_0022.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0022.s0 :: RH1E6S10_0022.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0022.s0.t = ((39421943312 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0022.s0]
  have e1 : RH1E6S10_0022.sL.t = ((39426502865 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0022.sL]
  rw [e0, e1] at h
  exact h

theorem band_0023 : RS5.BandZeros ((39426502865 : ℝ) / 65536) ((39431053397 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0023.s0 RH1E6S10_0023.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0023.s0 RH1E6S10_0023.rest = RH1E6S10_0023.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0023.s0 :: RH1E6S10_0023.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0023.s0.t = ((39426502865 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0023.s0]
  have e1 : RH1E6S10_0023.sL.t = ((39431053397 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0023.sL]
  rw [e0, e1] at h
  exact h

theorem part_002_3 : RS5.BandZeros ((39421943312 : ℝ) / 65536) ((39431053397 : ℝ) / 65536) 254 := by
  have g0 := band_0022
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0023
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39421943312 : ℝ) / 65536) ((39431053397 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_002_3 <;> assumption
