-- Prove2me | solution 1 for RH1E6S03.part_024_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:10:34.36717+00:00
-- url     : https://prove2.me/submissions/eec01ad8-e3e2-41a2-8545-18cd64b0016c

import Definitions.Def_RH1E6S03_D024_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0196 : RS5.BandZeros ((17349134124 : ℝ) / 65536) ((17354035415 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0196.s0 RH1E6S03_0196.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0196.s0 RH1E6S03_0196.rest = RH1E6S03_0196.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0196.s0 :: RH1E6S03_0196.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0196.s0.t = ((17349134124 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0196.s0]
  have e1 : RH1E6S03_0196.sL.t = ((17354035415 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0196.sL]
  rw [e0, e1] at h
  exact h

theorem band_0197 : RS5.BandZeros ((17354035415 : ℝ) / 65536) ((17358946242 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0197.s0 RH1E6S03_0197.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0197.s0 RH1E6S03_0197.rest = RH1E6S03_0197.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0197.s0 :: RH1E6S03_0197.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0197.s0.t = ((17354035415 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0197.s0]
  have e1 : RH1E6S03_0197.sL.t = ((17358946242 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0197.sL]
  rw [e0, e1] at h
  exact h

theorem part_024_2 : RS5.BandZeros ((17349134124 : ℝ) / 65536) ((17358946242 : ℝ) / 65536) 254 := by
  have g0 := band_0196
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0197
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17349134124 : ℝ) / 65536) ((17358946242 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_024_2 <;> assumption
