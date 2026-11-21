-- Prove2me | solution 1 for RH1E6S06.part_010_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:38:17.021242+00:00
-- url     : https://prove2.me/submissions/5a96ff6f-0247-43b4-9092-3ad8a3606958

import Definitions.Def_RH1E6S06_D010_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0082 : RS5.BandZeros ((26601833913 : ℝ) / 65536) ((26606552633 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0082.s0 RH1E6S06_0082.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0082.s0 RH1E6S06_0082.rest = RH1E6S06_0082.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0082.s0 :: RH1E6S06_0082.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0082.s0.t = ((26601833913 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0082.s0]
  have e1 : RH1E6S06_0082.sL.t = ((26606552633 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0082.sL]
  rw [e0, e1] at h
  exact h

theorem band_0083 : RS5.BandZeros ((26606552633 : ℝ) / 65536) ((26611269942 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0083.s0 RH1E6S06_0083.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0083.s0 RH1E6S06_0083.rest = RH1E6S06_0083.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0083.s0 :: RH1E6S06_0083.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0083.s0.t = ((26606552633 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0083.s0]
  have e1 : RH1E6S06_0083.sL.t = ((26611269942 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0083.sL]
  rw [e0, e1] at h
  exact h

theorem part_010_1 : RS5.BandZeros ((26601833913 : ℝ) / 65536) ((26611269942 : ℝ) / 65536) 254 := by
  have g0 := band_0082
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0083
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26601833913 : ℝ) / 65536) ((26611269942 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_010_1 <;> assumption
