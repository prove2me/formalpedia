-- Prove2me | solution 1 for RH1E6S08.part_080_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T07:45:06.049666+00:00
-- url     : https://prove2.me/submissions/de92fb25-d450-40c6-b9b7-482bbdadebfa

import Definitions.Def_RH1E6S08_D080_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0644 : RS5.BandZeros ((35740895202 : ℝ) / 65536) ((35745483855 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0644.s0 RH1E6S08_0644.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0644.s0 RH1E6S08_0644.rest = RH1E6S08_0644.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0644.s0 :: RH1E6S08_0644.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0644.s0.t = ((35740895202 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0644.s0]
  have e1 : RH1E6S08_0644.sL.t = ((35745483855 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0644.sL]
  rw [e0, e1] at h
  exact h

theorem band_0645 : RS5.BandZeros ((35745483855 : ℝ) / 65536) ((35750082093 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0645.s0 RH1E6S08_0645.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0645.s0 RH1E6S08_0645.rest = RH1E6S08_0645.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0645.s0 :: RH1E6S08_0645.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0645.s0.t = ((35745483855 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0645.s0]
  have e1 : RH1E6S08_0645.sL.t = ((35750082093 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0645.sL]
  rw [e0, e1] at h
  exact h

theorem part_080_2 : RS5.BandZeros ((35740895202 : ℝ) / 65536) ((35750082093 : ℝ) / 65536) 254 := by
  have g0 := band_0644
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0645
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35740895202 : ℝ) / 65536) ((35750082093 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_080_2 <;> assumption
