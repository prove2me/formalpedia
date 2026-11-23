-- Prove2me | solution 1 for RH1E6S16.part_089_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:18:47.408007+00:00
-- url     : https://prove2.me/submissions/e7fd1ada-e01a-46da-b839-147cfe6a0f7e

import Definitions.Def_RH1E6S16_D089_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0714 : RS5.BandZeros ((62120533806 : ℝ) / 65536) ((62124902656 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0714.s0 RH1E6S16_0714.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0714.s0 RH1E6S16_0714.rest = RH1E6S16_0714.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0714.s0 :: RH1E6S16_0714.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0714.s0.t = ((62120533806 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0714.s0]
  have e1 : RH1E6S16_0714.sL.t = ((62124902656 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0714.sL]
  rw [e0, e1] at h
  exact h

theorem band_0715 : RS5.BandZeros ((62124902656 : ℝ) / 65536) ((62129310281 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0715.s0 RH1E6S16_0715.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0715.s0 RH1E6S16_0715.rest = RH1E6S16_0715.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0715.s0 :: RH1E6S16_0715.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0715.s0.t = ((62124902656 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0715.s0]
  have e1 : RH1E6S16_0715.sL.t = ((62129310281 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0715.sL]
  rw [e0, e1] at h
  exact h

theorem part_089_1 : RS5.BandZeros ((62120533806 : ℝ) / 65536) ((62129310281 : ℝ) / 65536) 254 := by
  have g0 := band_0714
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0715
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62120533806 : ℝ) / 65536) ((62129310281 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_089_1 <;> assumption
