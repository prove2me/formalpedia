-- Prove2me | solution 1 for RH1E6S15.part_091_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:44:47.686512+00:00
-- url     : https://prove2.me/submissions/9135238b-f358-482a-a7d5-f787fc832de3

import Definitions.Def_RH1E6S15_D091_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0734 : RS5.BandZeros ((58946526213 : ℝ) / 65536) ((58950933252 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0734.s0 RH1E6S15_0734.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0734.s0 RH1E6S15_0734.rest = RH1E6S15_0734.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0734.s0 :: RH1E6S15_0734.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0734.s0.t = ((58946526213 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0734.s0]
  have e1 : RH1E6S15_0734.sL.t = ((58950933252 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0734.sL]
  rw [e0, e1] at h
  exact h

theorem band_0735 : RS5.BandZeros ((58950933252 : ℝ) / 65536) ((58955345706 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0735.s0 RH1E6S15_0735.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0735.s0 RH1E6S15_0735.rest = RH1E6S15_0735.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0735.s0 :: RH1E6S15_0735.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0735.s0.t = ((58950933252 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0735.s0]
  have e1 : RH1E6S15_0735.sL.t = ((58955345706 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0735.sL]
  rw [e0, e1] at h
  exact h

theorem part_091_3 : RS5.BandZeros ((58946526213 : ℝ) / 65536) ((58955345706 : ℝ) / 65536) 254 := by
  have g0 := band_0734
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0735
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58946526213 : ℝ) / 65536) ((58955345706 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_091_3 <;> assumption
