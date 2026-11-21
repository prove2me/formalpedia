-- Prove2me | solution 1 for RH1E6S07.part_050_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:19:12.822254+00:00
-- url     : https://prove2.me/submissions/ee4cc79b-f199-4c1f-863c-e6e162ac9473

import Definitions.Def_RH1E6S07_D050_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0402 : RS5.BandZeros ((31366507115 : ℝ) / 65536) ((31371167275 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0402.s0 RH1E6S07_0402.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0402.s0 RH1E6S07_0402.rest = RH1E6S07_0402.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0402.s0 :: RH1E6S07_0402.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0402.s0.t = ((31366507115 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0402.s0]
  have e1 : RH1E6S07_0402.sL.t = ((31371167275 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0402.sL]
  rw [e0, e1] at h
  exact h

theorem band_0403 : RS5.BandZeros ((31371167275 : ℝ) / 65536) ((31375823280 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0403.s0 RH1E6S07_0403.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0403.s0 RH1E6S07_0403.rest = RH1E6S07_0403.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0403.s0 :: RH1E6S07_0403.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0403.s0.t = ((31371167275 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0403.s0]
  have e1 : RH1E6S07_0403.sL.t = ((31375823280 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0403.sL]
  rw [e0, e1] at h
  exact h

theorem part_050_1 : RS5.BandZeros ((31366507115 : ℝ) / 65536) ((31375823280 : ℝ) / 65536) 254 := by
  have g0 := band_0402
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0403
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31366507115 : ℝ) / 65536) ((31375823280 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_050_1 <;> assumption
