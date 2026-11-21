-- Prove2me | solution 1 for RH1E6S06.part_075_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:16:30.348361+00:00
-- url     : https://prove2.me/submissions/c887c7a8-5c45-46b6-83d0-12e3cbf4d41e

import Definitions.Def_RH1E6S06_D075_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0606 : RS5.BandZeros ((29065891633 : ℝ) / 65536) ((29070575637 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0606.s0 RH1E6S06_0606.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0606.s0 RH1E6S06_0606.rest = RH1E6S06_0606.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0606.s0 :: RH1E6S06_0606.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0606.s0.t = ((29065891633 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0606.s0]
  have e1 : RH1E6S06_0606.sL.t = ((29070575637 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0606.sL]
  rw [e0, e1] at h
  exact h

theorem band_0607 : RS5.BandZeros ((29070575637 : ℝ) / 65536) ((29075243590 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0607.s0 RH1E6S06_0607.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0607.s0 RH1E6S06_0607.rest = RH1E6S06_0607.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0607.s0 :: RH1E6S06_0607.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0607.s0.t = ((29070575637 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0607.s0]
  have e1 : RH1E6S06_0607.sL.t = ((29075243590 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0607.sL]
  rw [e0, e1] at h
  exact h

theorem part_075_3 : RS5.BandZeros ((29065891633 : ℝ) / 65536) ((29075243590 : ℝ) / 65536) 254 := by
  have g0 := band_0606
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0607
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29065891633 : ℝ) / 65536) ((29075243590 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_075_3 <;> assumption
