-- Prove2me | solution 1 for RH1E6S09.part_044_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:12:45.610103+00:00
-- url     : https://prove2.me/submissions/4bc29ebf-d0c6-4e9d-8c50-0ecdf72906ea

import Definitions.Def_RH1E6S09_D044_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0356 : RS5.BandZeros ((37677577413 : ℝ) / 65536) ((37682132645 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0356.s0 RH1E6S09_0356.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0356.s0 RH1E6S09_0356.rest = RH1E6S09_0356.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0356.s0 :: RH1E6S09_0356.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0356.s0.t = ((37677577413 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0356.s0]
  have e1 : RH1E6S09_0356.sL.t = ((37682132645 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0356.sL]
  rw [e0, e1] at h
  exact h

theorem band_0357 : RS5.BandZeros ((37682132645 : ℝ) / 65536) ((37686689011 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0357.s0 RH1E6S09_0357.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0357.s0 RH1E6S09_0357.rest = RH1E6S09_0357.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0357.s0 :: RH1E6S09_0357.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0357.s0.t = ((37682132645 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0357.s0]
  have e1 : RH1E6S09_0357.sL.t = ((37686689011 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0357.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_2 : RS5.BandZeros ((37677577413 : ℝ) / 65536) ((37686689011 : ℝ) / 65536) 254 := by
  have g0 := band_0356
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0357
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37677577413 : ℝ) / 65536) ((37686689011 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_044_2 <;> assumption
