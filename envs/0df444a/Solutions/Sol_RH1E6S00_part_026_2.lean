-- Prove2me | solution 1 for RH1E6S00.part_026_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:40:10.579356+00:00
-- url     : https://prove2.me/submissions/d7110eaf-20ba-4431-9642-300c1fa0f63f

import Definitions.Def_RH1E6S00_D026_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0212 : RS5.BandZeros ((7689878314 : ℝ) / 65536) ((7695184969 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0212.s0 RH1E6S00_0212.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0212.s0 RH1E6S00_0212.rest = RH1E6S00_0212.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0212.s0 :: RH1E6S00_0212.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0212.s0.t = ((7689878314 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0212.s0]
  have e1 : RH1E6S00_0212.sL.t = ((7695184969 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0212.sL]
  rw [e0, e1] at h
  exact h

theorem band_0213 : RS5.BandZeros ((7695184969 : ℝ) / 65536) ((7700512184 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0213.s0 RH1E6S00_0213.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0213.s0 RH1E6S00_0213.rest = RH1E6S00_0213.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0213.s0 :: RH1E6S00_0213.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0213.s0.t = ((7695184969 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0213.s0]
  have e1 : RH1E6S00_0213.sL.t = ((7700512184 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0213.sL]
  rw [e0, e1] at h
  exact h

theorem part_026_2 : RS5.BandZeros ((7689878314 : ℝ) / 65536) ((7700512184 : ℝ) / 65536) 254 := by
  have g0 := band_0212
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0213
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7689878314 : ℝ) / 65536) ((7700512184 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_026_2 <;> assumption
