-- Prove2me | solution 1 for RH1E6S11.part_090_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:19:39.69785+00:00
-- url     : https://prove2.me/submissions/2fcef30f-2902-4927-b9de-0ec8cc2ca2a4

import Definitions.Def_RH1E6S11_D090_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0720 : RS5.BandZeros ((45848783006 : ℝ) / 65536) ((45853292163 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0720.s0 RH1E6S11_0720.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0720.s0 RH1E6S11_0720.rest = RH1E6S11_0720.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0720.s0 :: RH1E6S11_0720.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0720.s0.t = ((45848783006 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0720.s0]
  have e1 : RH1E6S11_0720.sL.t = ((45853292163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0720.sL]
  rw [e0, e1] at h
  exact h

theorem band_0721 : RS5.BandZeros ((45853292163 : ℝ) / 65536) ((45857792422 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0721.s0 RH1E6S11_0721.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0721.s0 RH1E6S11_0721.rest = RH1E6S11_0721.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0721.s0 :: RH1E6S11_0721.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0721.s0.t = ((45853292163 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0721.s0]
  have e1 : RH1E6S11_0721.sL.t = ((45857792422 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0721.sL]
  rw [e0, e1] at h
  exact h

theorem part_090_0 : RS5.BandZeros ((45848783006 : ℝ) / 65536) ((45857792422 : ℝ) / 65536) 254 := by
  have g0 := band_0720
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0721
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45848783006 : ℝ) / 65536) ((45857792422 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_090_0 <;> assumption
