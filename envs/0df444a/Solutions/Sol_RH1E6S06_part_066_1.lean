-- Prove2me | solution 1 for RH1E6S06.part_066_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T21:18:37.36578+00:00
-- url     : https://prove2.me/submissions/19fef0c4-8728-48c4-9a95-ae4456b238c5

import Definitions.Def_RH1E6S06_D066_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0530 : RS5.BandZeros ((28709710274 : ℝ) / 65536) ((28714403259 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0530.s0 RH1E6S06_0530.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0530.s0 RH1E6S06_0530.rest = RH1E6S06_0530.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0530.s0 :: RH1E6S06_0530.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0530.s0.t = ((28709710274 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0530.s0]
  have e1 : RH1E6S06_0530.sL.t = ((28714403259 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0530.sL]
  rw [e0, e1] at h
  exact h

theorem band_0531 : RS5.BandZeros ((28714403259 : ℝ) / 65536) ((28719090198 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0531.s0 RH1E6S06_0531.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0531.s0 RH1E6S06_0531.rest = RH1E6S06_0531.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0531.s0 :: RH1E6S06_0531.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0531.s0.t = ((28714403259 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0531.s0]
  have e1 : RH1E6S06_0531.sL.t = ((28719090198 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0531.sL]
  rw [e0, e1] at h
  exact h

theorem part_066_1 : RS5.BandZeros ((28709710274 : ℝ) / 65536) ((28719090198 : ℝ) / 65536) 254 := by
  have g0 := band_0530
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0531
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28709710274 : ℝ) / 65536) ((28719090198 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_066_1 <;> assumption
