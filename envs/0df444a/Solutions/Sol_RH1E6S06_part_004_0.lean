-- Prove2me | solution 1 for RH1E6S06.part_004_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:22:43.89358+00:00
-- url     : https://prove2.me/submissions/1eef58ac-cb02-41b4-8645-97d0e23c534e

import Definitions.Def_RH1E6S06_D004_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0032 : RS5.BandZeros ((26365656292 : ℝ) / 65536) ((26370375511 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0032.s0 RH1E6S06_0032.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0032.s0 RH1E6S06_0032.rest = RH1E6S06_0032.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0032.s0 :: RH1E6S06_0032.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0032.s0.t = ((26365656292 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0032.s0]
  have e1 : RH1E6S06_0032.sL.t = ((26370375511 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0032.sL]
  rw [e0, e1] at h
  exact h

theorem band_0033 : RS5.BandZeros ((26370375511 : ℝ) / 65536) ((26375095819 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0033.s0 RH1E6S06_0033.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0033.s0 RH1E6S06_0033.rest = RH1E6S06_0033.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0033.s0 :: RH1E6S06_0033.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0033.s0.t = ((26370375511 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0033.s0]
  have e1 : RH1E6S06_0033.sL.t = ((26375095819 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0033.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_0 : RS5.BandZeros ((26365656292 : ℝ) / 65536) ((26375095819 : ℝ) / 65536) 254 := by
  have g0 := band_0032
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0033
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26365656292 : ℝ) / 65536) ((26375095819 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_004_0 <;> assumption
