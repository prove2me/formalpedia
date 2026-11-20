-- Prove2me | solution 1 for RH1E6S02.part_029_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:10:31.97188+00:00
-- url     : https://prove2.me/submissions/9403e95e-95a6-4d72-b54f-876070e86e6b

import Definitions.Def_RH1E6S02_D029_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0236 : RS5.BandZeros ((14292521412 : ℝ) / 65536) ((14297538251 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0236.s0 RH1E6S02_0236.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0236.s0 RH1E6S02_0236.rest = RH1E6S02_0236.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0236.s0 :: RH1E6S02_0236.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0236.s0.t = ((14292521412 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0236.s0]
  have e1 : RH1E6S02_0236.sL.t = ((14297538251 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0236.sL]
  rw [e0, e1] at h
  exact h

theorem band_0237 : RS5.BandZeros ((14297538251 : ℝ) / 65536) ((14302531194 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0237.s0 RH1E6S02_0237.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0237.s0 RH1E6S02_0237.rest = RH1E6S02_0237.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0237.s0 :: RH1E6S02_0237.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0237.s0.t = ((14297538251 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0237.s0]
  have e1 : RH1E6S02_0237.sL.t = ((14302531194 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0237.sL]
  rw [e0, e1] at h
  exact h

theorem part_029_2 : RS5.BandZeros ((14292521412 : ℝ) / 65536) ((14302531194 : ℝ) / 65536) 254 := by
  have g0 := band_0236
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0237
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14292521412 : ℝ) / 65536) ((14302531194 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_029_2 <;> assumption
