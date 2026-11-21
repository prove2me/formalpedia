-- Prove2me | solution 1 for RH1E6S07.part_029_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:17:51.842831+00:00
-- url     : https://prove2.me/submissions/1501a3ca-f0b1-4b6b-b669-4b26c763a542

import Definitions.Def_RH1E6S07_D029_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0236 : RS5.BandZeros ((30593377440 : ℝ) / 65536) ((30598052111 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0236.s0 RH1E6S07_0236.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0236.s0 RH1E6S07_0236.rest = RH1E6S07_0236.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0236.s0 :: RH1E6S07_0236.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0236.s0.t = ((30593377440 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0236.s0]
  have e1 : RH1E6S07_0236.sL.t = ((30598052111 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0236.sL]
  rw [e0, e1] at h
  exact h

theorem band_0237 : RS5.BandZeros ((30598052111 : ℝ) / 65536) ((30602690463 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0237.s0 RH1E6S07_0237.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0237.s0 RH1E6S07_0237.rest = RH1E6S07_0237.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0237.s0 :: RH1E6S07_0237.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0237.s0.t = ((30598052111 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0237.s0]
  have e1 : RH1E6S07_0237.sL.t = ((30602690463 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0237.sL]
  rw [e0, e1] at h
  exact h

theorem part_029_2 : RS5.BandZeros ((30593377440 : ℝ) / 65536) ((30602690463 : ℝ) / 65536) 254 := by
  have g0 := band_0236
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0237
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30593377440 : ℝ) / 65536) ((30602690463 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_029_2 <;> assumption
