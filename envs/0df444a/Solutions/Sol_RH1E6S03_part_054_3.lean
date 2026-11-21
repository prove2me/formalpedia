-- Prove2me | solution 1 for RH1E6S03.part_054_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:14:43.674885+00:00
-- url     : https://prove2.me/submissions/e8f38251-f1d2-448b-aa01-b0e5b4981542

import Definitions.Def_RH1E6S03_D054_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0438 : RS5.BandZeros ((18533886438 : ℝ) / 65536) ((18538757516 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0438.s0 RH1E6S03_0438.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0438.s0 RH1E6S03_0438.rest = RH1E6S03_0438.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0438.s0 :: RH1E6S03_0438.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0438.s0.t = ((18533886438 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0438.s0]
  have e1 : RH1E6S03_0438.sL.t = ((18538757516 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0438.sL]
  rw [e0, e1] at h
  exact h

theorem band_0439 : RS5.BandZeros ((18538757516 : ℝ) / 65536) ((18543638082 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0439.s0 RH1E6S03_0439.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0439.s0 RH1E6S03_0439.rest = RH1E6S03_0439.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0439.s0 :: RH1E6S03_0439.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0439.s0.t = ((18538757516 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0439.s0]
  have e1 : RH1E6S03_0439.sL.t = ((18543638082 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0439.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_3 : RS5.BandZeros ((18533886438 : ℝ) / 65536) ((18543638082 : ℝ) / 65536) 254 := by
  have g0 := band_0438
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0439
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18533886438 : ℝ) / 65536) ((18543638082 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_054_3 <;> assumption
