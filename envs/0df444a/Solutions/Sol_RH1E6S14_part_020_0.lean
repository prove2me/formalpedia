-- Prove2me | solution 1 for RH1E6S14.part_020_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:35:27.452813+00:00
-- url     : https://prove2.me/submissions/853cf190-8f08-4054-b605-a7109e4978e7

import Definitions.Def_RH1E6S14_D020_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0160 : RS5.BandZeros ((53140201014 : ℝ) / 65536) ((53144668499 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0160.s0 RH1E6S14_0160.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0160.s0 RH1E6S14_0160.rest = RH1E6S14_0160.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0160.s0 :: RH1E6S14_0160.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0160.s0.t = ((53140201014 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0160.s0]
  have e1 : RH1E6S14_0160.sL.t = ((53144668499 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0160.sL]
  rw [e0, e1] at h
  exact h

theorem band_0161 : RS5.BandZeros ((53144668499 : ℝ) / 65536) ((53149110590 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0161.s0 RH1E6S14_0161.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0161.s0 RH1E6S14_0161.rest = RH1E6S14_0161.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0161.s0 :: RH1E6S14_0161.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0161.s0.t = ((53144668499 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0161.s0]
  have e1 : RH1E6S14_0161.sL.t = ((53149110590 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0161.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_0 : RS5.BandZeros ((53140201014 : ℝ) / 65536) ((53149110590 : ℝ) / 65536) 254 := by
  have g0 := band_0160
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0161
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53140201014 : ℝ) / 65536) ((53149110590 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_020_0 <;> assumption
