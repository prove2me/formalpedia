-- Prove2me | solution 1 for RH1E6S07.part_044_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:01:51.203304+00:00
-- url     : https://prove2.me/submissions/362b0021-f267-4c8f-af3c-f8c18f35fbd5

import Definitions.Def_RH1E6S07_D044_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0352 : RS5.BandZeros ((31133810960 : ℝ) / 65536) ((31138467930 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0352.s0 RH1E6S07_0352.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0352.s0 RH1E6S07_0352.rest = RH1E6S07_0352.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0352.s0 :: RH1E6S07_0352.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0352.s0.t = ((31133810960 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0352.s0]
  have e1 : RH1E6S07_0352.sL.t = ((31138467930 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0352.sL]
  rw [e0, e1] at h
  exact h

theorem band_0353 : RS5.BandZeros ((31138467930 : ℝ) / 65536) ((31143127223 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0353.s0 RH1E6S07_0353.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0353.s0 RH1E6S07_0353.rest = RH1E6S07_0353.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0353.s0 :: RH1E6S07_0353.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0353.s0.t = ((31138467930 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0353.s0]
  have e1 : RH1E6S07_0353.sL.t = ((31143127223 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0353.sL]
  rw [e0, e1] at h
  exact h

theorem part_044_0 : RS5.BandZeros ((31133810960 : ℝ) / 65536) ((31143127223 : ℝ) / 65536) 254 := by
  have g0 := band_0352
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0353
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31133810960 : ℝ) / 65536) ((31143127223 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_044_0 <;> assumption
