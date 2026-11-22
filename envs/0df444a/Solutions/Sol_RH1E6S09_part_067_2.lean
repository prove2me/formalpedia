-- Prove2me | solution 1 for RH1E6S09.part_067_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T14:05:57.303175+00:00
-- url     : https://prove2.me/submissions/5a9e08de-5327-4c6c-b43f-f6dd18ea8e79

import Definitions.Def_RH1E6S09_D067_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0540 : RS5.BandZeros ((38519031025 : ℝ) / 65536) ((38523595863 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0540.s0 RH1E6S09_0540.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0540.s0 RH1E6S09_0540.rest = RH1E6S09_0540.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0540.s0 :: RH1E6S09_0540.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0540.s0.t = ((38519031025 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0540.s0]
  have e1 : RH1E6S09_0540.sL.t = ((38523595863 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0540.sL]
  rw [e0, e1] at h
  exact h

theorem band_0541 : RS5.BandZeros ((38523595863 : ℝ) / 65536) ((38528162148 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0541.s0 RH1E6S09_0541.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0541.s0 RH1E6S09_0541.rest = RH1E6S09_0541.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0541.s0 :: RH1E6S09_0541.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0541.s0.t = ((38523595863 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0541.s0]
  have e1 : RH1E6S09_0541.sL.t = ((38528162148 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0541.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_2 : RS5.BandZeros ((38519031025 : ℝ) / 65536) ((38528162148 : ℝ) / 65536) 254 := by
  have g0 := band_0540
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0541
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38519031025 : ℝ) / 65536) ((38528162148 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_067_2 <;> assumption
