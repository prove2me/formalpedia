-- Prove2me | solution 1 for RH1E6S00.part_049_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:26:43.278182+00:00
-- url     : https://prove2.me/submissions/94854000-cf6a-4677-8325-662c102abf78

import Definitions.Def_RH1E6S00_D049_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0394 : RS5.BandZeros ((8651741632 : ℝ) / 65536) ((8657006158 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0394.s0 RH1E6S00_0394.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0394.s0 RH1E6S00_0394.rest = RH1E6S00_0394.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0394.s0 :: RH1E6S00_0394.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0394.s0.t = ((8651741632 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0394.s0]
  have e1 : RH1E6S00_0394.sL.t = ((8657006158 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0394.sL]
  rw [e0, e1] at h
  exact h

theorem band_0395 : RS5.BandZeros ((8657006158 : ℝ) / 65536) ((8662249679 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0395.s0 RH1E6S00_0395.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0395.s0 RH1E6S00_0395.rest = RH1E6S00_0395.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0395.s0 :: RH1E6S00_0395.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0395.s0.t = ((8657006158 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0395.s0]
  have e1 : RH1E6S00_0395.sL.t = ((8662249679 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0395.sL]
  rw [e0, e1] at h
  exact h

theorem part_049_1 : RS5.BandZeros ((8651741632 : ℝ) / 65536) ((8662249679 : ℝ) / 65536) 254 := by
  have g0 := band_0394
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0395
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8651741632 : ℝ) / 65536) ((8662249679 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_049_1 <;> assumption
