-- Prove2me | solution 1 for RH1E6S01.part_052_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:11:41.799934+00:00
-- url     : https://prove2.me/submissions/21bfbb94-546f-4520-b451-e0094c6952af

import Definitions.Def_RH1E6S01_D052_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0422 : RS5.BandZeros ((11997508265 : ℝ) / 65536) ((12002595394 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0422.s0 RH1E6S01_0422.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0422.s0 RH1E6S01_0422.rest = RH1E6S01_0422.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0422.s0 :: RH1E6S01_0422.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0422.s0.t = ((11997508265 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0422.s0]
  have e1 : RH1E6S01_0422.sL.t = ((12002595394 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0422.sL]
  rw [e0, e1] at h
  exact h

theorem band_0423 : RS5.BandZeros ((12002595394 : ℝ) / 65536) ((12007682313 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0423.s0 RH1E6S01_0423.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0423.s0 RH1E6S01_0423.rest = RH1E6S01_0423.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0423.s0 :: RH1E6S01_0423.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0423.s0.t = ((12002595394 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0423.s0]
  have e1 : RH1E6S01_0423.sL.t = ((12007682313 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0423.sL]
  rw [e0, e1] at h
  exact h

theorem part_052_3 : RS5.BandZeros ((11997508265 : ℝ) / 65536) ((12007682313 : ℝ) / 65536) 254 := by
  have g0 := band_0422
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0423
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11997508265 : ℝ) / 65536) ((12007682313 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_052_3 <;> assumption
