-- Prove2me | solution 1 for RH1E6S07.part_012_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T23:28:22.046894+00:00
-- url     : https://prove2.me/submissions/f53200a2-a533-431c-ab36-43f796ec90fd

import Definitions.Def_RH1E6S07_D012_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0096 : RS5.BandZeros ((29939974749 : ℝ) / 65536) ((29944662209 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0096.s0 RH1E6S07_0096.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0096.s0 RH1E6S07_0096.rest = RH1E6S07_0096.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0096.s0 :: RH1E6S07_0096.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0096.s0.t = ((29939974749 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0096.s0]
  have e1 : RH1E6S07_0096.sL.t = ((29944662209 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0096.sL]
  rw [e0, e1] at h
  exact h

theorem band_0097 : RS5.BandZeros ((29944662209 : ℝ) / 65536) ((29949327177 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0097.s0 RH1E6S07_0097.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0097.s0 RH1E6S07_0097.rest = RH1E6S07_0097.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0097.s0 :: RH1E6S07_0097.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0097.s0.t = ((29944662209 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0097.s0]
  have e1 : RH1E6S07_0097.sL.t = ((29949327177 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0097.sL]
  rw [e0, e1] at h
  exact h

theorem part_012_0 : RS5.BandZeros ((29939974749 : ℝ) / 65536) ((29949327177 : ℝ) / 65536) 254 := by
  have g0 := band_0096
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0097
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((29939974749 : ℝ) / 65536) ((29949327177 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_012_0 <;> assumption
