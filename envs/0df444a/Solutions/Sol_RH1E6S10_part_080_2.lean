-- Prove2me | solution 1 for RH1E6S10.part_080_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:35:36.346002+00:00
-- url     : https://prove2.me/submissions/965b9bda-e098-4297-9c15-e3132e9433ae

import Definitions.Def_RH1E6S10_D080_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0644 : RS5.BandZeros ((42249372218 : ℝ) / 65536) ((42253886558 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0644.s0 RH1E6S10_0644.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0644.s0 RH1E6S10_0644.rest = RH1E6S10_0644.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0644.s0 :: RH1E6S10_0644.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0644.s0.t = ((42249372218 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0644.s0]
  have e1 : RH1E6S10_0644.sL.t = ((42253886558 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0644.sL]
  rw [e0, e1] at h
  exact h

theorem band_0645 : RS5.BandZeros ((42253886558 : ℝ) / 65536) ((42258436543 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0645.s0 RH1E6S10_0645.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0645.s0 RH1E6S10_0645.rest = RH1E6S10_0645.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0645.s0 :: RH1E6S10_0645.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0645.s0.t = ((42253886558 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0645.s0]
  have e1 : RH1E6S10_0645.sL.t = ((42258436543 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0645.sL]
  rw [e0, e1] at h
  exact h

theorem part_080_2 : RS5.BandZeros ((42249372218 : ℝ) / 65536) ((42258436543 : ℝ) / 65536) 254 := by
  have g0 := band_0644
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0645
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42249372218 : ℝ) / 65536) ((42258436543 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_080_2 <;> assumption
