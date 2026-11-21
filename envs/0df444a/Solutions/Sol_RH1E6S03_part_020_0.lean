-- Prove2me | solution 1 for RH1E6S03.part_020_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:58:27.161609+00:00
-- url     : https://prove2.me/submissions/d7174ee4-9e4a-4435-905f-4b571208c6d7

import Definitions.Def_RH1E6S03_D020_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0160 : RS5.BandZeros ((17172252331 : ℝ) / 65536) ((17177158342 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0160.s0 RH1E6S03_0160.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0160.s0 RH1E6S03_0160.rest = RH1E6S03_0160.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0160.s0 :: RH1E6S03_0160.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0160.s0.t = ((17172252331 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0160.s0]
  have e1 : RH1E6S03_0160.sL.t = ((17177158342 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0160.sL]
  rw [e0, e1] at h
  exact h

theorem band_0161 : RS5.BandZeros ((17177158342 : ℝ) / 65536) ((17182054545 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0161.s0 RH1E6S03_0161.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0161.s0 RH1E6S03_0161.rest = RH1E6S03_0161.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0161.s0 :: RH1E6S03_0161.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0161.s0.t = ((17177158342 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0161.s0]
  have e1 : RH1E6S03_0161.sL.t = ((17182054545 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0161.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_0 : RS5.BandZeros ((17172252331 : ℝ) / 65536) ((17182054545 : ℝ) / 65536) 254 := by
  have g0 := band_0160
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0161
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17172252331 : ℝ) / 65536) ((17182054545 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_020_0 <;> assumption
