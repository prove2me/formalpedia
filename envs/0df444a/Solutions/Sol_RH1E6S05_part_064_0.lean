-- Prove2me | solution 1 for RH1E6S05.part_064_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T15:46:10.020989+00:00
-- url     : https://prove2.me/submissions/cd13714a-a638-488b-befd-022936ac47f3

import Definitions.Def_RH1E6S05_D064_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0512 : RS5.BandZeros ((25376339517 : ℝ) / 65536) ((25381071834 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0512.s0 RH1E6S05_0512.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0512.s0 RH1E6S05_0512.rest = RH1E6S05_0512.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0512.s0 :: RH1E6S05_0512.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0512.s0.t = ((25376339517 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0512.s0]
  have e1 : RH1E6S05_0512.sL.t = ((25381071834 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0512.sL]
  rw [e0, e1] at h
  exact h

theorem band_0513 : RS5.BandZeros ((25381071834 : ℝ) / 65536) ((25385822738 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0513.s0 RH1E6S05_0513.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0513.s0 RH1E6S05_0513.rest = RH1E6S05_0513.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0513.s0 :: RH1E6S05_0513.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0513.s0.t = ((25381071834 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0513.s0]
  have e1 : RH1E6S05_0513.sL.t = ((25385822738 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0513.sL]
  rw [e0, e1] at h
  exact h

theorem part_064_0 : RS5.BandZeros ((25376339517 : ℝ) / 65536) ((25385822738 : ℝ) / 65536) 254 := by
  have g0 := band_0512
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0513
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25376339517 : ℝ) / 65536) ((25385822738 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_064_0 <;> assumption
