-- Prove2me | solution 1 for RH1E6S03.part_081_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T08:16:09.086407+00:00
-- url     : https://prove2.me/submissions/29b01565-8339-4f44-9d3e-7f84cca9dd7d

import Definitions.Def_RH1E6S03_D081_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0650 : RS5.BandZeros ((19565951799 : ℝ) / 65536) ((19570807928 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0650.s0 RH1E6S03_0650.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0650.s0 RH1E6S03_0650.rest = RH1E6S03_0650.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0650.s0 :: RH1E6S03_0650.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0650.s0.t = ((19565951799 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0650.s0]
  have e1 : RH1E6S03_0650.sL.t = ((19570807928 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0650.sL]
  rw [e0, e1] at h
  exact h

theorem band_0651 : RS5.BandZeros ((19570807928 : ℝ) / 65536) ((19575683063 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0651.s0 RH1E6S03_0651.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0651.s0 RH1E6S03_0651.rest = RH1E6S03_0651.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0651.s0 :: RH1E6S03_0651.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0651.s0.t = ((19570807928 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0651.s0]
  have e1 : RH1E6S03_0651.sL.t = ((19575683063 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0651.sL]
  rw [e0, e1] at h
  exact h

theorem part_081_1 : RS5.BandZeros ((19565951799 : ℝ) / 65536) ((19575683063 : ℝ) / 65536) 254 := by
  have g0 := band_0650
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0651
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((19565951799 : ℝ) / 65536) ((19575683063 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_081_1 <;> assumption
