-- Prove2me | solution 1 for RH1E6S08.part_025_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:06:00.567705+00:00
-- url     : https://prove2.me/submissions/3b0aa2ac-95dd-44e4-aaa2-79ddae89b343

import Definitions.Def_RH1E6S08_D025_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0206 : RS5.BandZeros ((33721453449 : ℝ) / 65536) ((33726083088 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0206.s0 RH1E6S08_0206.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0206.s0 RH1E6S08_0206.rest = RH1E6S08_0206.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0206.s0 :: RH1E6S08_0206.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0206.s0.t = ((33721453449 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0206.s0]
  have e1 : RH1E6S08_0206.sL.t = ((33726083088 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0206.sL]
  rw [e0, e1] at h
  exact h

theorem band_0207 : RS5.BandZeros ((33726083088 : ℝ) / 65536) ((33730714410 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0207.s0 RH1E6S08_0207.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0207.s0 RH1E6S08_0207.rest = RH1E6S08_0207.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0207.s0 :: RH1E6S08_0207.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0207.s0.t = ((33726083088 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0207.s0]
  have e1 : RH1E6S08_0207.sL.t = ((33730714410 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0207.sL]
  rw [e0, e1] at h
  exact h

theorem part_025_3 : RS5.BandZeros ((33721453449 : ℝ) / 65536) ((33730714410 : ℝ) / 65536) 254 := by
  have g0 := band_0206
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0207
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33721453449 : ℝ) / 65536) ((33730714410 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_025_3 <;> assumption
