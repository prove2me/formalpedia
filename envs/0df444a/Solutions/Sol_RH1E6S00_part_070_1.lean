-- Prove2me | solution 1 for RH1E6S00.part_070_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:08:50.113182+00:00
-- url     : https://prove2.me/submissions/d6278347-2810-4a66-87ac-f66004247bb3

import Definitions.Def_RH1E6S00_D070_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0562 : RS5.BandZeros ((9530166251 : ℝ) / 65536) ((9535359650 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0562.s0 RH1E6S00_0562.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0562.s0 RH1E6S00_0562.rest = RH1E6S00_0562.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0562.s0 :: RH1E6S00_0562.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0562.s0.t = ((9530166251 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0562.s0]
  have e1 : RH1E6S00_0562.sL.t = ((9535359650 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0562.sL]
  rw [e0, e1] at h
  exact h

theorem band_0563 : RS5.BandZeros ((9535359650 : ℝ) / 65536) ((9540552768 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0563.s0 RH1E6S00_0563.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0563.s0 RH1E6S00_0563.rest = RH1E6S00_0563.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0563.s0 :: RH1E6S00_0563.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0563.s0.t = ((9535359650 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0563.s0]
  have e1 : RH1E6S00_0563.sL.t = ((9540552768 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0563.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_1 : RS5.BandZeros ((9530166251 : ℝ) / 65536) ((9540552768 : ℝ) / 65536) 254 := by
  have g0 := band_0562
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0563
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9530166251 : ℝ) / 65536) ((9540552768 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_070_1 <;> assumption
