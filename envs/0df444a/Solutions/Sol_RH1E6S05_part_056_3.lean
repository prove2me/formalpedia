-- Prove2me | solution 1 for RH1E6S05.part_056_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T14:42:08.390082+00:00
-- url     : https://prove2.me/submissions/e7e99dfb-eb00-4e2e-8f3f-9195b288204f

import Definitions.Def_RH1E6S05_D056_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0454 : RS5.BandZeros ((25101176348 : ℝ) / 65536) ((25105932033 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0454.s0 RH1E6S05_0454.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0454.s0 RH1E6S05_0454.rest = RH1E6S05_0454.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0454.s0 :: RH1E6S05_0454.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0454.s0.t = ((25101176348 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0454.s0]
  have e1 : RH1E6S05_0454.sL.t = ((25105932033 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0454.sL]
  rw [e0, e1] at h
  exact h

theorem band_0455 : RS5.BandZeros ((25105932033 : ℝ) / 65536) ((25110678294 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0455.s0 RH1E6S05_0455.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0455.s0 RH1E6S05_0455.rest = RH1E6S05_0455.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0455.s0 :: RH1E6S05_0455.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0455.s0.t = ((25105932033 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0455.s0]
  have e1 : RH1E6S05_0455.sL.t = ((25110678294 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0455.sL]
  rw [e0, e1] at h
  exact h

theorem part_056_3 : RS5.BandZeros ((25101176348 : ℝ) / 65536) ((25110678294 : ℝ) / 65536) 254 := by
  have g0 := band_0454
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0455
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25101176348 : ℝ) / 65536) ((25110678294 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_056_3 <;> assumption
