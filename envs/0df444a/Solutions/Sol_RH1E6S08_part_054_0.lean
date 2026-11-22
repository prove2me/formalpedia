-- Prove2me | solution 1 for RH1E6S08.part_054_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T06:32:57.797073+00:00
-- url     : https://prove2.me/submissions/6865c4a3-b856-440b-aaef-187edfbda84b

import Definitions.Def_RH1E6S08_D054_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0432 : RS5.BandZeros ((34764765543 : ℝ) / 65536) ((34769357475 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0432.s0 RH1E6S08_0432.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0432.s0 RH1E6S08_0432.rest = RH1E6S08_0432.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0432.s0 :: RH1E6S08_0432.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0432.s0.t = ((34764765543 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0432.s0]
  have e1 : RH1E6S08_0432.sL.t = ((34769357475 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0432.sL]
  rw [e0, e1] at h
  exact h

theorem band_0433 : RS5.BandZeros ((34769357475 : ℝ) / 65536) ((34773965074 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0433.s0 RH1E6S08_0433.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0433.s0 RH1E6S08_0433.rest = RH1E6S08_0433.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0433.s0 :: RH1E6S08_0433.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0433.s0.t = ((34769357475 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0433.s0]
  have e1 : RH1E6S08_0433.sL.t = ((34773965074 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0433.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_0 : RS5.BandZeros ((34764765543 : ℝ) / 65536) ((34773965074 : ℝ) / 65536) 254 := by
  have g0 := band_0432
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0433
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34764765543 : ℝ) / 65536) ((34773965074 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_054_0 <;> assumption
