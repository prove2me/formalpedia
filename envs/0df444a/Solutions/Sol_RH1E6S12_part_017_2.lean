-- Prove2me | solution 1 for RH1E6S12.part_017_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:17:07.890707+00:00
-- url     : https://prove2.me/submissions/49dda5cb-951d-42a3-b9ec-ba624917749d

import Definitions.Def_RH1E6S12_D017_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0140 : RS5.BandZeros ((46504869109 : ℝ) / 65536) ((46509342044 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0140.s0 RH1E6S12_0140.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0140.s0 RH1E6S12_0140.rest = RH1E6S12_0140.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0140.s0 :: RH1E6S12_0140.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0140.s0.t = ((46504869109 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0140.s0]
  have e1 : RH1E6S12_0140.sL.t = ((46509342044 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0140.sL]
  rw [e0, e1] at h
  exact h

theorem band_0141 : RS5.BandZeros ((46509342044 : ℝ) / 65536) ((46513849828 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0141.s0 RH1E6S12_0141.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0141.s0 RH1E6S12_0141.rest = RH1E6S12_0141.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0141.s0 :: RH1E6S12_0141.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0141.s0.t = ((46509342044 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0141.s0]
  have e1 : RH1E6S12_0141.sL.t = ((46513849828 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0141.sL]
  rw [e0, e1] at h
  exact h

theorem part_017_2 : RS5.BandZeros ((46504869109 : ℝ) / 65536) ((46513849828 : ℝ) / 65536) 254 := by
  have g0 := band_0140
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0141
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46504869109 : ℝ) / 65536) ((46513849828 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_017_2 <;> assumption
