-- Prove2me | solution 1 for RH1E6S06.part_004_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:25:09.4639+00:00
-- url     : https://prove2.me/submissions/4d39ae8d-4553-4939-b166-199871d6af22

import Definitions.Def_RH1E6S06_D004_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0036 : RS5.BandZeros ((26384549431 : ℝ) / 65536) ((26389284163 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0036.s0 RH1E6S06_0036.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0036.s0 RH1E6S06_0036.rest = RH1E6S06_0036.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0036.s0 :: RH1E6S06_0036.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0036.s0.t = ((26384549431 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0036.s0]
  have e1 : RH1E6S06_0036.sL.t = ((26389284163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0036.sL]
  rw [e0, e1] at h
  exact h

theorem band_0037 : RS5.BandZeros ((26389284163 : ℝ) / 65536) ((26394011249 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0037.s0 RH1E6S06_0037.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0037.s0 RH1E6S06_0037.rest = RH1E6S06_0037.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0037.s0 :: RH1E6S06_0037.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0037.s0.t = ((26389284163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0037.s0]
  have e1 : RH1E6S06_0037.sL.t = ((26394011249 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0037.sL]
  rw [e0, e1] at h
  exact h

theorem part_004_2 : RS5.BandZeros ((26384549431 : ℝ) / 65536) ((26394011249 : ℝ) / 65536) 254 := by
  have g0 := band_0036
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0037
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26384549431 : ℝ) / 65536) ((26394011249 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_004_2 <;> assumption
