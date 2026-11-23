-- Prove2me | solution 1 for RH1E6S17.part_021_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T20:43:13.15303+00:00
-- url     : https://prove2.me/submissions/5e2c6237-fb9d-45c4-ae48-bbbc701a3d34

import Definitions.Def_RH1E6S17_D021_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0168 : RS5.BandZeros ((62995498185 : ℝ) / 65536) ((62999878720 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0168.s0 RH1E6S17_0168.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0168.s0 RH1E6S17_0168.rest = RH1E6S17_0168.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0168.s0 :: RH1E6S17_0168.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0168.s0.t = ((62995498185 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0168.s0]
  have e1 : RH1E6S17_0168.sL.t = ((62999878720 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0168.sL]
  rw [e0, e1] at h
  exact h

theorem band_0169 : RS5.BandZeros ((62999878720 : ℝ) / 65536) ((63004259229 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0169.s0 RH1E6S17_0169.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0169.s0 RH1E6S17_0169.rest = RH1E6S17_0169.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0169.s0 :: RH1E6S17_0169.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0169.s0.t = ((62999878720 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0169.s0]
  have e1 : RH1E6S17_0169.sL.t = ((63004259229 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0169.sL]
  rw [e0, e1] at h
  exact h

theorem part_021_0 : RS5.BandZeros ((62995498185 : ℝ) / 65536) ((63004259229 : ℝ) / 65536) 254 := by
  have g0 := band_0168
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0169
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((62995498185 : ℝ) / 65536) ((63004259229 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_021_0 <;> assumption
