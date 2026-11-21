-- Prove2me | solution 1 for RH1E6S07.part_067_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T02:04:02.890866+00:00
-- url     : https://prove2.me/submissions/56d462fd-ce78-4469-b2be-a12ce45e4411

import Definitions.Def_RH1E6S07_D067_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0538 : RS5.BandZeros ((31998656126 : ℝ) / 65536) ((32003294902 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0538.s0 RH1E6S07_0538.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0538.s0 RH1E6S07_0538.rest = RH1E6S07_0538.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0538.s0 :: RH1E6S07_0538.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0538.s0.t = ((31998656126 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0538.s0]
  have e1 : RH1E6S07_0538.sL.t = ((32003294902 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0538.sL]
  rw [e0, e1] at h
  exact h

theorem band_0539 : RS5.BandZeros ((32003294902 : ℝ) / 65536) ((32007949218 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0539.s0 RH1E6S07_0539.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0539.s0 RH1E6S07_0539.rest = RH1E6S07_0539.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0539.s0 :: RH1E6S07_0539.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0539.s0.t = ((32003294902 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0539.s0]
  have e1 : RH1E6S07_0539.sL.t = ((32007949218 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0539.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_1 : RS5.BandZeros ((31998656126 : ℝ) / 65536) ((32007949218 : ℝ) / 65536) 254 := by
  have g0 := band_0538
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0539
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31998656126 : ℝ) / 65536) ((32007949218 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_067_1 <;> assumption
