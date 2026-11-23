-- Prove2me | solution 1 for RH1E6S15.part_071_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T12:15:36.190194+00:00
-- url     : https://prove2.me/submissions/6e9e9a98-860a-414f-84d1-2afc5b8d4a54

import Definitions.Def_RH1E6S15_D071_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0572 : RS5.BandZeros ((58232536129 : ℝ) / 65536) ((58236958002 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0572.s0 RH1E6S15_0572.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0572.s0 RH1E6S15_0572.rest = RH1E6S15_0572.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0572.s0 :: RH1E6S15_0572.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0572.s0.t = ((58232536129 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0572.s0]
  have e1 : RH1E6S15_0572.sL.t = ((58236958002 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0572.sL]
  rw [e0, e1] at h
  exact h

theorem band_0573 : RS5.BandZeros ((58236958002 : ℝ) / 65536) ((58241354615 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0573.s0 RH1E6S15_0573.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0573.s0 RH1E6S15_0573.rest = RH1E6S15_0573.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0573.s0 :: RH1E6S15_0573.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0573.s0.t = ((58236958002 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0573.s0]
  have e1 : RH1E6S15_0573.sL.t = ((58241354615 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0573.sL]
  rw [e0, e1] at h
  exact h

theorem part_071_2 : RS5.BandZeros ((58232536129 : ℝ) / 65536) ((58241354615 : ℝ) / 65536) 254 := by
  have g0 := band_0572
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0573
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58232536129 : ℝ) / 65536) ((58241354615 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_071_2 <;> assumption
