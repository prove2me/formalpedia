-- Prove2me | solution 1 for RH1E6S05.part_048_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T14:19:30.549481+00:00
-- url     : https://prove2.me/submissions/7390eb08-5625-4e8c-a571-7bd8461787b8

import Definitions.Def_RH1E6S05_D048_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0386 : RS5.BandZeros ((24778232941 : ℝ) / 65536) ((24782984867 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0386.s0 RH1E6S05_0386.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0386.s0 RH1E6S05_0386.rest = RH1E6S05_0386.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0386.s0 :: RH1E6S05_0386.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0386.s0.t = ((24778232941 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0386.s0]
  have e1 : RH1E6S05_0386.sL.t = ((24782984867 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0386.sL]
  rw [e0, e1] at h
  exact h

theorem band_0387 : RS5.BandZeros ((24782984867 : ℝ) / 65536) ((24787727357 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0387.s0 RH1E6S05_0387.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0387.s0 RH1E6S05_0387.rest = RH1E6S05_0387.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0387.s0 :: RH1E6S05_0387.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0387.s0.t = ((24782984867 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0387.s0]
  have e1 : RH1E6S05_0387.sL.t = ((24787727357 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0387.sL]
  rw [e0, e1] at h
  exact h

theorem part_048_1 : RS5.BandZeros ((24778232941 : ℝ) / 65536) ((24787727357 : ℝ) / 65536) 254 := by
  have g0 := band_0386
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0387
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24778232941 : ℝ) / 65536) ((24787727357 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_048_1 <;> assumption
