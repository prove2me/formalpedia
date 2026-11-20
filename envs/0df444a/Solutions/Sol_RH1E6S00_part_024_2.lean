-- Prove2me | solution 1 for RH1E6S00.part_024_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:35:35.550188+00:00
-- url     : https://prove2.me/submissions/fd86afe2-1d8c-465a-9538-2bf132567d1f

import Definitions.Def_RH1E6S00_D024_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0196 : RS5.BandZeros ((7604763773 : ℝ) / 65536) ((7610086917 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0196.s0 RH1E6S00_0196.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0196.s0 RH1E6S00_0196.rest = RH1E6S00_0196.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0196.s0 :: RH1E6S00_0196.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0196.s0.t = ((7604763773 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0196.s0]
  have e1 : RH1E6S00_0196.sL.t = ((7610086917 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0196.sL]
  rw [e0, e1] at h
  exact h

theorem band_0197 : RS5.BandZeros ((7610086917 : ℝ) / 65536) ((7615399203 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0197.s0 RH1E6S00_0197.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0197.s0 RH1E6S00_0197.rest = RH1E6S00_0197.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0197.s0 :: RH1E6S00_0197.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0197.s0.t = ((7610086917 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0197.s0]
  have e1 : RH1E6S00_0197.sL.t = ((7615399203 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0197.sL]
  rw [e0, e1] at h
  exact h

theorem part_024_2 : RS5.BandZeros ((7604763773 : ℝ) / 65536) ((7615399203 : ℝ) / 65536) 254 := by
  have g0 := band_0196
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0197
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7604763773 : ℝ) / 65536) ((7615399203 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_024_2 <;> assumption
