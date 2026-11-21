-- Prove2me | solution 1 for RH1E6S06.part_062_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T20:53:19.072335+00:00
-- url     : https://prove2.me/submissions/8f7a9234-b0fd-4e23-b135-9aa63d587ada

import Definitions.Def_RH1E6S06_D062_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0500 : RS5.BandZeros ((28568991795 : ℝ) / 65536) ((28573683641 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0500.s0 RH1E6S06_0500.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0500.s0 RH1E6S06_0500.rest = RH1E6S06_0500.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0500.s0 :: RH1E6S06_0500.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0500.s0.t = ((28568991795 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0500.s0]
  have e1 : RH1E6S06_0500.sL.t = ((28573683641 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0500.sL]
  rw [e0, e1] at h
  exact h

theorem band_0501 : RS5.BandZeros ((28573683641 : ℝ) / 65536) ((28578374224 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0501.s0 RH1E6S06_0501.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0501.s0 RH1E6S06_0501.rest = RH1E6S06_0501.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0501.s0 :: RH1E6S06_0501.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0501.s0.t = ((28573683641 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0501.s0]
  have e1 : RH1E6S06_0501.sL.t = ((28578374224 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0501.sL]
  rw [e0, e1] at h
  exact h

theorem part_062_2 : RS5.BandZeros ((28568991795 : ℝ) / 65536) ((28578374224 : ℝ) / 65536) 254 := by
  have g0 := band_0500
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0501
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28568991795 : ℝ) / 65536) ((28578374224 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_062_2 <;> assumption
