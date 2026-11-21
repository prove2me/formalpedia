-- Prove2me | solution 1 for RH1E6S04.part_067_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T11:50:23.509609+00:00
-- url     : https://prove2.me/submissions/245f5a12-6590-4491-a019-89956961ad3d

import Definitions.Def_RH1E6S04_D067_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem band_0538 : RS5.BandZeros ((22257009365 : ℝ) / 65536) ((22261808078 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0538.s0 RH1E6S04_0538.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0538.s0 RH1E6S04_0538.rest = RH1E6S04_0538.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0538.s0 :: RH1E6S04_0538.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0538.s0.t = ((22257009365 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0538.s0]
  have e1 : RH1E6S04_0538.sL.t = ((22261808078 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0538.sL]
  rw [e0, e1] at h
  exact h

theorem band_0539 : RS5.BandZeros ((22261808078 : ℝ) / 65536) ((22266597250 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S04_0539.s0 RH1E6S04_0539.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S04_0539.s0 RH1E6S04_0539.rest = RH1E6S04_0539.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S04_0539.s0 :: RH1E6S04_0539.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S04_0539.s0.t = ((22261808078 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0539.s0]
  have e1 : RH1E6S04_0539.sL.t = ((22266597250 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S04_0539.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_1 : RS5.BandZeros ((22257009365 : ℝ) / 65536) ((22266597250 : ℝ) / 65536) 254 := by
  have g0 := band_0538
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0539
  exact g1

end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22257009365 : ℝ) / 65536) ((22266597250 : ℝ) / 65536) 254 := by
  apply RH1E6S04.part_067_1 <;> assumption
