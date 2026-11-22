-- Prove2me | solution 1 for RH1E6S09.part_065_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T13:50:39.22901+00:00
-- url     : https://prove2.me/submissions/a5639219-c1e2-4e00-8179-fbc6af0dcd37

import Definitions.Def_RH1E6S09_D065_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0522 : RS5.BandZeros ((38436797277 : ℝ) / 65536) ((38441352038 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0522.s0 RH1E6S09_0522.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0522.s0 RH1E6S09_0522.rest = RH1E6S09_0522.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0522.s0 :: RH1E6S09_0522.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0522.s0.t = ((38436797277 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0522.s0]
  have e1 : RH1E6S09_0522.sL.t = ((38441352038 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0522.sL]
  rw [e0, e1] at h
  exact h

theorem band_0523 : RS5.BandZeros ((38441352038 : ℝ) / 65536) ((38445914811 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0523.s0 RH1E6S09_0523.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0523.s0 RH1E6S09_0523.rest = RH1E6S09_0523.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0523.s0 :: RH1E6S09_0523.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0523.s0.t = ((38441352038 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0523.s0]
  have e1 : RH1E6S09_0523.sL.t = ((38445914811 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0523.sL]
  rw [e0, e1] at h
  exact h

theorem part_065_1 : RS5.BandZeros ((38436797277 : ℝ) / 65536) ((38445914811 : ℝ) / 65536) 254 := by
  have g0 := band_0522
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0523
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38436797277 : ℝ) / 65536) ((38445914811 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_065_1 <;> assumption
