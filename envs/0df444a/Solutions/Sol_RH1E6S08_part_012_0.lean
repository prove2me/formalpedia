-- Prove2me | solution 1 for RH1E6S08.part_012_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:28:40.218389+00:00
-- url     : https://prove2.me/submissions/58c2aa26-dd68-4466-9c63-97ae19ab37bf

import Definitions.Def_RH1E6S08_D012_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0096 : RS5.BandZeros ((33212654092 : ℝ) / 65536) ((33217279235 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0096.s0 RH1E6S08_0096.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0096.s0 RH1E6S08_0096.rest = RH1E6S08_0096.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0096.s0 :: RH1E6S08_0096.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0096.s0.t = ((33212654092 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0096.s0]
  have e1 : RH1E6S08_0096.sL.t = ((33217279235 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0096.sL]
  rw [e0, e1] at h
  exact h

theorem band_0097 : RS5.BandZeros ((33217279235 : ℝ) / 65536) ((33221898286 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0097.s0 RH1E6S08_0097.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0097.s0 RH1E6S08_0097.rest = RH1E6S08_0097.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0097.s0 :: RH1E6S08_0097.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0097.s0.t = ((33217279235 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0097.s0]
  have e1 : RH1E6S08_0097.sL.t = ((33221898286 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0097.sL]
  rw [e0, e1] at h
  exact h

theorem part_012_0 : RS5.BandZeros ((33212654092 : ℝ) / 65536) ((33221898286 : ℝ) / 65536) 254 := by
  have g0 := band_0096
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0097
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33212654092 : ℝ) / 65536) ((33221898286 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_012_0 <;> assumption
