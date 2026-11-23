-- Prove2me | solution 1 for RH1E6S14.part_064_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T06:07:55.8078+00:00
-- url     : https://prove2.me/submissions/91149573-592d-4a02-97fe-361da08b5d53

import Definitions.Def_RH1E6S14_D064_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem band_0512 : RS5.BandZeros ((54702531017 : ℝ) / 65536) ((54706973134 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0512.s0 RH1E6S14_0512.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0512.s0 RH1E6S14_0512.rest = RH1E6S14_0512.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0512.s0 :: RH1E6S14_0512.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0512.s0.t = ((54702531017 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0512.s0]
  have e1 : RH1E6S14_0512.sL.t = ((54706973134 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0512.sL]
  rw [e0, e1] at h
  exact h

theorem band_0513 : RS5.BandZeros ((54706973134 : ℝ) / 65536) ((54711386721 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S14_0513.s0 RH1E6S14_0513.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S14_0513.s0 RH1E6S14_0513.rest = RH1E6S14_0513.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S14_0513.s0 :: RH1E6S14_0513.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S14_0513.s0.t = ((54706973134 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0513.s0]
  have e1 : RH1E6S14_0513.sL.t = ((54711386721 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S14_0513.sL]
  rw [e0, e1] at h
  exact h

theorem part_064_0 : RS5.BandZeros ((54702531017 : ℝ) / 65536) ((54711386721 : ℝ) / 65536) 254 := by
  have g0 := band_0512
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0513
  exact g1

end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54702531017 : ℝ) / 65536) ((54711386721 : ℝ) / 65536) 254 := by
  apply RH1E6S14.part_064_0 <;> assumption
