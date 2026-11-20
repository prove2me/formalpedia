-- Prove2me | solution 1 for RH1E6S00.part_024_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:35:37.511504+00:00
-- url     : https://prove2.me/submissions/06d6e08b-9ada-4df2-ba12-86f8f77b54c6

import Definitions.Def_RH1E6S00_D024_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0198 : RS5.BandZeros ((7615399203 : ℝ) / 65536) ((7620721590 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0198.s0 RH1E6S00_0198.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0198.s0 RH1E6S00_0198.rest = RH1E6S00_0198.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0198.s0 :: RH1E6S00_0198.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0198.s0.t = ((7615399203 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0198.s0]
  have e1 : RH1E6S00_0198.sL.t = ((7620721590 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0198.sL]
  rw [e0, e1] at h
  exact h

theorem band_0199 : RS5.BandZeros ((7620721590 : ℝ) / 65536) ((7626054074 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0199.s0 RH1E6S00_0199.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0199.s0 RH1E6S00_0199.rest = RH1E6S00_0199.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0199.s0 :: RH1E6S00_0199.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0199.s0.t = ((7620721590 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0199.s0]
  have e1 : RH1E6S00_0199.sL.t = ((7626054074 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0199.sL]
  rw [e0, e1] at h
  exact h

theorem part_024_3 : RS5.BandZeros ((7615399203 : ℝ) / 65536) ((7626054074 : ℝ) / 65536) 254 := by
  have g0 := band_0198
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0199
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7615399203 : ℝ) / 65536) ((7626054074 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_024_3 <;> assumption
