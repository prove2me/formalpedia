-- Prove2me | solution 1 for RH1E6S00.part_013_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:14:15.982989+00:00
-- url     : https://prove2.me/submissions/ed0feab0-d672-4cf7-b2e4-2df66fd5c7d9

import Definitions.Def_RH1E6S00_D013_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0104 : RS5.BandZeros ((7113365057 : ℝ) / 65536) ((7118714078 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0104.s0 RH1E6S00_0104.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0104.s0 RH1E6S00_0104.rest = RH1E6S00_0104.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0104.s0 :: RH1E6S00_0104.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0104.s0.t = ((7113365057 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0104.s0]
  have e1 : RH1E6S00_0104.sL.t = ((7118714078 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0104.sL]
  rw [e0, e1] at h
  exact h

theorem band_0105 : RS5.BandZeros ((7118714078 : ℝ) / 65536) ((7124073236 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0105.s0 RH1E6S00_0105.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0105.s0 RH1E6S00_0105.rest = RH1E6S00_0105.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0105.s0 :: RH1E6S00_0105.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0105.s0.t = ((7118714078 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0105.s0]
  have e1 : RH1E6S00_0105.sL.t = ((7124073236 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0105.sL]
  rw [e0, e1] at h
  exact h

theorem part_013_0 : RS5.BandZeros ((7113365057 : ℝ) / 65536) ((7124073236 : ℝ) / 65536) 254 := by
  have g0 := band_0104
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0105
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7113365057 : ℝ) / 65536) ((7124073236 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_013_0 <;> assumption
