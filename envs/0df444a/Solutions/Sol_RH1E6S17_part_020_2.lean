-- Prove2me | solution 1 for RH1E6S17.part_020_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T20:40:08.97148+00:00
-- url     : https://prove2.me/submissions/fed2cfb4-0d7a-48bc-853a-55c800fda07b

import Definitions.Def_RH1E6S17_D020_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0164 : RS5.BandZeros ((62977958543 : ℝ) / 65536) ((62982365050 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0164.s0 RH1E6S17_0164.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0164.s0 RH1E6S17_0164.rest = RH1E6S17_0164.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0164.s0 :: RH1E6S17_0164.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0164.s0.t = ((62977958543 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0164.s0]
  have e1 : RH1E6S17_0164.sL.t = ((62982365050 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0164.sL]
  rw [e0, e1] at h
  exact h

theorem band_0165 : RS5.BandZeros ((62982365050 : ℝ) / 65536) ((62986745662 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0165.s0 RH1E6S17_0165.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0165.s0 RH1E6S17_0165.rest = RH1E6S17_0165.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0165.s0 :: RH1E6S17_0165.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0165.s0.t = ((62982365050 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0165.s0]
  have e1 : RH1E6S17_0165.sL.t = ((62986745662 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0165.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_2 : RS5.BandZeros ((62977958543 : ℝ) / 65536) ((62986745662 : ℝ) / 65536) 254 := by
  have g0 := band_0164
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0165
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((62977958543 : ℝ) / 65536) ((62986745662 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_020_2 <;> assumption
