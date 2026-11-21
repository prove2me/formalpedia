-- Prove2me | solution 1 for RH1E6S07.part_087_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T03:54:07.441635+00:00
-- url     : https://prove2.me/submissions/b06c781c-e300-4609-873c-731997d33b84

import Definitions.Def_RH1E6S07_D087_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0696 : RS5.BandZeros ((32731670549 : ℝ) / 65536) ((32736316261 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0696.s0 RH1E6S07_0696.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0696.s0 RH1E6S07_0696.rest = RH1E6S07_0696.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0696.s0 :: RH1E6S07_0696.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0696.s0.t = ((32731670549 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0696.s0]
  have e1 : RH1E6S07_0696.sL.t = ((32736316261 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0696.sL]
  rw [e0, e1] at h
  exact h

theorem band_0697 : RS5.BandZeros ((32736316261 : ℝ) / 65536) ((32740940080 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0697.s0 RH1E6S07_0697.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0697.s0 RH1E6S07_0697.rest = RH1E6S07_0697.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0697.s0 :: RH1E6S07_0697.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0697.s0.t = ((32736316261 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0697.s0]
  have e1 : RH1E6S07_0697.sL.t = ((32740940080 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0697.sL]
  rw [e0, e1] at h
  exact h

theorem part_087_0 : RS5.BandZeros ((32731670549 : ℝ) / 65536) ((32740940080 : ℝ) / 65536) 254 := by
  have g0 := band_0696
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0697
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32731670549 : ℝ) / 65536) ((32740940080 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_087_0 <;> assumption
