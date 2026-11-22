-- Prove2me | solution 1 for RH1E6S09.part_021_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T09:09:13.289675+00:00
-- url     : https://prove2.me/submissions/906519d0-ace4-428e-a73f-60e597ecef41

import Definitions.Def_RH1E6S09_D021_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0168 : RS5.BandZeros ((36816112530 : ℝ) / 65536) ((36820690827 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0168.s0 RH1E6S09_0168.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0168.s0 RH1E6S09_0168.rest = RH1E6S09_0168.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0168.s0 :: RH1E6S09_0168.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0168.s0.t = ((36816112530 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0168.s0]
  have e1 : RH1E6S09_0168.sL.t = ((36820690827 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0168.sL]
  rw [e0, e1] at h
  exact h

theorem band_0169 : RS5.BandZeros ((36820690827 : ℝ) / 65536) ((36825262790 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0169.s0 RH1E6S09_0169.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0169.s0 RH1E6S09_0169.rest = RH1E6S09_0169.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0169.s0 :: RH1E6S09_0169.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0169.s0.t = ((36820690827 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0169.s0]
  have e1 : RH1E6S09_0169.sL.t = ((36825262790 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0169.sL]
  rw [e0, e1] at h
  exact h

theorem part_021_0 : RS5.BandZeros ((36816112530 : ℝ) / 65536) ((36825262790 : ℝ) / 65536) 254 := by
  have g0 := band_0168
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0169
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36816112530 : ℝ) / 65536) ((36825262790 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_021_0 <;> assumption
