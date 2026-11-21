-- Prove2me | solution 1 for RH1E6S07.part_085_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T03:48:11.14382+00:00
-- url     : https://prove2.me/submissions/23ba212b-c38e-4864-97ab-2523aeac928c

import Definitions.Def_RH1E6S07_D085_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0684 : RS5.BandZeros ((32676070113 : ℝ) / 65536) ((32680675875 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0684.s0 RH1E6S07_0684.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0684.s0 RH1E6S07_0684.rest = RH1E6S07_0684.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0684.s0 :: RH1E6S07_0684.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0684.s0.t = ((32676070113 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0684.s0]
  have e1 : RH1E6S07_0684.sL.t = ((32680675875 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0684.sL]
  rw [e0, e1] at h
  exact h

theorem band_0685 : RS5.BandZeros ((32680675875 : ℝ) / 65536) ((32685323458 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0685.s0 RH1E6S07_0685.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0685.s0 RH1E6S07_0685.rest = RH1E6S07_0685.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0685.s0 :: RH1E6S07_0685.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0685.s0.t = ((32680675875 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0685.s0]
  have e1 : RH1E6S07_0685.sL.t = ((32685323458 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0685.sL]
  rw [e0, e1] at h
  exact h

theorem part_085_2 : RS5.BandZeros ((32676070113 : ℝ) / 65536) ((32685323458 : ℝ) / 65536) 254 := by
  have g0 := band_0684
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0685
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32676070113 : ℝ) / 65536) ((32685323458 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_085_2 <;> assumption
