-- Prove2me | solution 1 for RH1E6S10.part_089_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:00:53.215587+00:00
-- url     : https://prove2.me/submissions/d33a2adc-bb3b-43a3-b4d2-781f12efb774

import Definitions.Def_RH1E6S10_D089_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0716 : RS5.BandZeros ((42575591014 : ℝ) / 65536) ((42580093432 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0716.s0 RH1E6S10_0716.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0716.s0 RH1E6S10_0716.rest = RH1E6S10_0716.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0716.s0 :: RH1E6S10_0716.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0716.s0.t = ((42575591014 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0716.s0]
  have e1 : RH1E6S10_0716.sL.t = ((42580093432 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0716.sL]
  rw [e0, e1] at h
  exact h

theorem band_0717 : RS5.BandZeros ((42580093432 : ℝ) / 65536) ((42584631471 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0717.s0 RH1E6S10_0717.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0717.s0 RH1E6S10_0717.rest = RH1E6S10_0717.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0717.s0 :: RH1E6S10_0717.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0717.s0.t = ((42580093432 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0717.s0]
  have e1 : RH1E6S10_0717.sL.t = ((42584631471 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0717.sL]
  rw [e0, e1] at h
  exact h

theorem part_089_2 : RS5.BandZeros ((42575591014 : ℝ) / 65536) ((42584631471 : ℝ) / 65536) 254 := by
  have g0 := band_0716
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0717
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42575591014 : ℝ) / 65536) ((42584631471 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_089_2 <;> assumption
