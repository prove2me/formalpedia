-- Prove2me | solution 1 for RH1E6S02.part_028_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:08:03.666523+00:00
-- url     : https://prove2.me/submissions/894c6c35-b41a-4a4c-9aaf-ef4564cfc3ae

import Definitions.Def_RH1E6S02_D028_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0226 : RS5.BandZeros ((14242497288 : ℝ) / 65536) ((14247512655 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0226.s0 RH1E6S02_0226.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0226.s0 RH1E6S02_0226.rest = RH1E6S02_0226.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0226.s0 :: RH1E6S02_0226.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0226.s0.t = ((14242497288 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0226.s0]
  have e1 : RH1E6S02_0226.sL.t = ((14247512655 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0226.sL]
  rw [e0, e1] at h
  exact h

theorem band_0227 : RS5.BandZeros ((14247512655 : ℝ) / 65536) ((14252508432 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0227.s0 RH1E6S02_0227.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0227.s0 RH1E6S02_0227.rest = RH1E6S02_0227.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0227.s0 :: RH1E6S02_0227.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0227.s0.t = ((14247512655 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0227.s0]
  have e1 : RH1E6S02_0227.sL.t = ((14252508432 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0227.sL]
  rw [e0, e1] at h
  exact h

theorem part_028_1 : RS5.BandZeros ((14242497288 : ℝ) / 65536) ((14252508432 : ℝ) / 65536) 254 := by
  have g0 := band_0226
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0227
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14242497288 : ℝ) / 65536) ((14252508432 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_028_1 <;> assumption
