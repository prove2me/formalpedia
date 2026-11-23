-- Prove2me | solution 1 for RH1E6S13.part_053_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T00:03:12.317773+00:00
-- url     : https://prove2.me/submissions/662c7efd-998f-423f-bce4-870b282024e2

import Definitions.Def_RH1E6S13_D053_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0428 : RS5.BandZeros ((51063557089 : ℝ) / 65536) ((51068007276 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0428.s0 RH1E6S13_0428.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0428.s0 RH1E6S13_0428.rest = RH1E6S13_0428.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0428.s0 :: RH1E6S13_0428.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0428.s0.t = ((51063557089 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0428.s0]
  have e1 : RH1E6S13_0428.sL.t = ((51068007276 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0428.sL]
  rw [e0, e1] at h
  exact h

theorem band_0429 : RS5.BandZeros ((51068007276 : ℝ) / 65536) ((51072457431 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0429.s0 RH1E6S13_0429.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0429.s0 RH1E6S13_0429.rest = RH1E6S13_0429.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0429.s0 :: RH1E6S13_0429.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0429.s0.t = ((51068007276 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0429.s0]
  have e1 : RH1E6S13_0429.sL.t = ((51072457431 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0429.sL]
  rw [e0, e1] at h
  exact h

theorem part_053_2 : RS5.BandZeros ((51063557089 : ℝ) / 65536) ((51072457431 : ℝ) / 65536) 254 := by
  have g0 := band_0428
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0429
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51063557089 : ℝ) / 65536) ((51072457431 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_053_2 <;> assumption
