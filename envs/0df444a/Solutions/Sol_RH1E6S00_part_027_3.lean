-- Prove2me | solution 1 for RH1E6S00.part_027_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:42:32.978595+00:00
-- url     : https://prove2.me/submissions/5e60f7a7-8188-4d01-9ff0-305af30dd53d

import Definitions.Def_RH1E6S00_D027_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0222 : RS5.BandZeros ((7743032763 : ℝ) / 65536) ((7748335705 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0222.s0 RH1E6S00_0222.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0222.s0 RH1E6S00_0222.rest = RH1E6S00_0222.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0222.s0 :: RH1E6S00_0222.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0222.s0.t = ((7743032763 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0222.s0]
  have e1 : RH1E6S00_0222.sL.t = ((7748335705 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0222.sL]
  rw [e0, e1] at h
  exact h

theorem band_0223 : RS5.BandZeros ((7748335705 : ℝ) / 65536) ((7753648737 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0223.s0 RH1E6S00_0223.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0223.s0 RH1E6S00_0223.rest = RH1E6S00_0223.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0223.s0 :: RH1E6S00_0223.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0223.s0.t = ((7748335705 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0223.s0]
  have e1 : RH1E6S00_0223.sL.t = ((7753648737 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0223.sL]
  rw [e0, e1] at h
  exact h

theorem part_027_3 : RS5.BandZeros ((7743032763 : ℝ) / 65536) ((7753648737 : ℝ) / 65536) 254 := by
  have g0 := band_0222
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0223
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7743032763 : ℝ) / 65536) ((7753648737 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_027_3 <;> assumption
