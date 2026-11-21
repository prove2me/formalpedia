-- Prove2me | solution 1 for RH1E6S07.part_067_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T02:04:00.822791+00:00
-- url     : https://prove2.me/submissions/aa2aefa3-3d48-4875-a2c2-36a1aa8344be

import Definitions.Def_RH1E6S07_D067_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0536 : RS5.BandZeros ((31989376607 : ℝ) / 65536) ((31994011499 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0536.s0 RH1E6S07_0536.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0536.s0 RH1E6S07_0536.rest = RH1E6S07_0536.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0536.s0 :: RH1E6S07_0536.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0536.s0.t = ((31989376607 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0536.s0]
  have e1 : RH1E6S07_0536.sL.t = ((31994011499 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0536.sL]
  rw [e0, e1] at h
  exact h

theorem band_0537 : RS5.BandZeros ((31994011499 : ℝ) / 65536) ((31998656126 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0537.s0 RH1E6S07_0537.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0537.s0 RH1E6S07_0537.rest = RH1E6S07_0537.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0537.s0 :: RH1E6S07_0537.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0537.s0.t = ((31994011499 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0537.s0]
  have e1 : RH1E6S07_0537.sL.t = ((31998656126 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0537.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_0 : RS5.BandZeros ((31989376607 : ℝ) / 65536) ((31998656126 : ℝ) / 65536) 254 := by
  have g0 := band_0536
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0537
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31989376607 : ℝ) / 65536) ((31998656126 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_067_0 <;> assumption
