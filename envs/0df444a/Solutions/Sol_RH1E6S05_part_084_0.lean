-- Prove2me | solution 1 for RH1E6S05.part_084_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:07:35.618355+00:00
-- url     : https://prove2.me/submissions/d663c220-b645-4340-bdfa-ebfbf209933c

import Definitions.Def_RH1E6S05_D084_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0672 : RS5.BandZeros ((26133975967 : ℝ) / 65536) ((26138705005 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0672.s0 RH1E6S05_0672.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0672.s0 RH1E6S05_0672.rest = RH1E6S05_0672.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0672.s0 :: RH1E6S05_0672.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0672.s0.t = ((26133975967 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0672.s0]
  have e1 : RH1E6S05_0672.sL.t = ((26138705005 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0672.sL]
  rw [e0, e1] at h
  exact h

theorem band_0673 : RS5.BandZeros ((26138705005 : ℝ) / 65536) ((26143433965 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0673.s0 RH1E6S05_0673.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0673.s0 RH1E6S05_0673.rest = RH1E6S05_0673.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0673.s0 :: RH1E6S05_0673.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0673.s0.t = ((26138705005 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0673.s0]
  have e1 : RH1E6S05_0673.sL.t = ((26143433965 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0673.sL]
  rw [e0, e1] at h
  exact h

theorem part_084_0 : RS5.BandZeros ((26133975967 : ℝ) / 65536) ((26143433965 : ℝ) / 65536) 254 := by
  have g0 := band_0672
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0673
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((26133975967 : ℝ) / 65536) ((26143433965 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_084_0 <;> assumption
