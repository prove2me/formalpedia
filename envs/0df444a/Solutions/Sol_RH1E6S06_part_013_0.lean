-- Prove2me | solution 1 for RH1E6S06.part_013_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:46:04.030876+00:00
-- url     : https://prove2.me/submissions/bba5d028-a75e-4ed8-9993-3c39c3f7de2c

import Definitions.Def_RH1E6S06_D013_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0104 : RS5.BandZeros ((26705688640 : ℝ) / 65536) ((26710407131 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0104.s0 RH1E6S06_0104.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0104.s0 RH1E6S06_0104.rest = RH1E6S06_0104.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0104.s0 :: RH1E6S06_0104.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0104.s0.t = ((26705688640 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0104.s0]
  have e1 : RH1E6S06_0104.sL.t = ((26710407131 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0104.sL]
  rw [e0, e1] at h
  exact h

theorem band_0105 : RS5.BandZeros ((26710407131 : ℝ) / 65536) ((26715109588 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0105.s0 RH1E6S06_0105.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0105.s0 RH1E6S06_0105.rest = RH1E6S06_0105.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0105.s0 :: RH1E6S06_0105.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0105.s0.t = ((26710407131 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0105.s0]
  have e1 : RH1E6S06_0105.sL.t = ((26715109588 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0105.sL]
  rw [e0, e1] at h
  exact h

theorem part_013_0 : RS5.BandZeros ((26705688640 : ℝ) / 65536) ((26715109588 : ℝ) / 65536) 254 := by
  have g0 := band_0104
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0105
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26705688640 : ℝ) / 65536) ((26715109588 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_013_0 <;> assumption
