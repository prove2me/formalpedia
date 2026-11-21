-- Prove2me | solution 1 for RH1E6S06.part_061_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T20:41:55.597016+00:00
-- url     : https://prove2.me/submissions/631c28e8-8a5d-4609-87dd-157ab18ffac6

import Definitions.Def_RH1E6S06_D061_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0492 : RS5.BandZeros ((28531460892 : ℝ) / 65536) ((28536166828 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0492.s0 RH1E6S06_0492.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0492.s0 RH1E6S06_0492.rest = RH1E6S06_0492.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0492.s0 :: RH1E6S06_0492.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0492.s0.t = ((28531460892 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0492.s0]
  have e1 : RH1E6S06_0492.sL.t = ((28536166828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0492.sL]
  rw [e0, e1] at h
  exact h

theorem band_0493 : RS5.BandZeros ((28536166828 : ℝ) / 65536) ((28540858619 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0493.s0 RH1E6S06_0493.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0493.s0 RH1E6S06_0493.rest = RH1E6S06_0493.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0493.s0 :: RH1E6S06_0493.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0493.s0.t = ((28536166828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0493.s0]
  have e1 : RH1E6S06_0493.sL.t = ((28540858619 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0493.sL]
  rw [e0, e1] at h
  exact h

theorem part_061_2 : RS5.BandZeros ((28531460892 : ℝ) / 65536) ((28540858619 : ℝ) / 65536) 254 := by
  have g0 := band_0492
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0493
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28531460892 : ℝ) / 65536) ((28540858619 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_061_2 <;> assumption
