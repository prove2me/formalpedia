-- Prove2me | solution 1 for RH1E6S07.part_033_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:30:42.306183+00:00
-- url     : https://prove2.me/submissions/ed0183e3-2545-4dbd-bba6-d995aa77ea3f

import Definitions.Def_RH1E6S07_D033_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0270 : RS5.BandZeros ((30751861531 : ℝ) / 65536) ((30756535391 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0270.s0 RH1E6S07_0270.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0270.s0 RH1E6S07_0270.rest = RH1E6S07_0270.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0270.s0 :: RH1E6S07_0270.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0270.s0.t = ((30751861531 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0270.s0]
  have e1 : RH1E6S07_0270.sL.t = ((30756535391 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0270.sL]
  rw [e0, e1] at h
  exact h

theorem band_0271 : RS5.BandZeros ((30756535391 : ℝ) / 65536) ((30761187120 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0271.s0 RH1E6S07_0271.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0271.s0 RH1E6S07_0271.rest = RH1E6S07_0271.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0271.s0 :: RH1E6S07_0271.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0271.s0.t = ((30756535391 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0271.s0]
  have e1 : RH1E6S07_0271.sL.t = ((30761187120 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0271.sL]
  rw [e0, e1] at h
  exact h

theorem part_033_3 : RS5.BandZeros ((30751861531 : ℝ) / 65536) ((30761187120 : ℝ) / 65536) 254 := by
  have g0 := band_0270
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0271
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30751861531 : ℝ) / 65536) ((30761187120 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_033_3 <;> assumption
