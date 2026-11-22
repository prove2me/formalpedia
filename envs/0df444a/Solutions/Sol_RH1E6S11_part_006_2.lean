-- Prove2me | solution 1 for RH1E6S11.part_006_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:20:39.437996+00:00
-- url     : https://prove2.me/submissions/a9d01376-65b0-4a17-91f8-170bae814095

import Definitions.Def_RH1E6S11_D006_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0052 : RS5.BandZeros ((42833838465 : ℝ) / 65536) ((42838374170 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0052.s0 RH1E6S11_0052.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0052.s0 RH1E6S11_0052.rest = RH1E6S11_0052.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0052.s0 :: RH1E6S11_0052.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0052.s0.t = ((42833838465 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0052.s0]
  have e1 : RH1E6S11_0052.sL.t = ((42838374170 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0052.sL]
  rw [e0, e1] at h
  exact h

theorem band_0053 : RS5.BandZeros ((42838374170 : ℝ) / 65536) ((42842909834 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0053.s0 RH1E6S11_0053.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0053.s0 RH1E6S11_0053.rest = RH1E6S11_0053.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0053.s0 :: RH1E6S11_0053.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0053.s0.t = ((42838374170 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0053.s0]
  have e1 : RH1E6S11_0053.sL.t = ((42842909834 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0053.sL]
  rw [e0, e1] at h
  exact h

theorem part_006_2 : RS5.BandZeros ((42833838465 : ℝ) / 65536) ((42842909834 : ℝ) / 65536) 254 := by
  have g0 := band_0052
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0053
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((42833838465 : ℝ) / 65536) ((42842909834 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_006_2 <;> assumption
