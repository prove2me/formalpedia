-- Prove2me | solution 1 for RH1E6S05.part_065_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T15:50:59.66409+00:00
-- url     : https://prove2.me/submissions/e8ee7f83-a016-4dfc-bb11-e5a005fc69c0

import Definitions.Def_RH1E6S05_D065_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0522 : RS5.BandZeros ((25423752413 : ℝ) / 65536) ((25428502594 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0522.s0 RH1E6S05_0522.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0522.s0 RH1E6S05_0522.rest = RH1E6S05_0522.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0522.s0 :: RH1E6S05_0522.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0522.s0.t = ((25423752413 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0522.s0]
  have e1 : RH1E6S05_0522.sL.t = ((25428502594 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0522.sL]
  rw [e0, e1] at h
  exact h

theorem band_0523 : RS5.BandZeros ((25428502594 : ℝ) / 65536) ((25433215365 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0523.s0 RH1E6S05_0523.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0523.s0 RH1E6S05_0523.rest = RH1E6S05_0523.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0523.s0 :: RH1E6S05_0523.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0523.s0.t = ((25428502594 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0523.s0]
  have e1 : RH1E6S05_0523.sL.t = ((25433215365 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0523.sL]
  rw [e0, e1] at h
  exact h

theorem part_065_1 : RS5.BandZeros ((25423752413 : ℝ) / 65536) ((25433215365 : ℝ) / 65536) 254 := by
  have g0 := band_0522
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0523
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25423752413 : ℝ) / 65536) ((25433215365 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_065_1 <;> assumption
