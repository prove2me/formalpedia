-- Prove2me | solution 1 for RH1E6S11.part_038_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T04:50:44.045904+00:00
-- url     : https://prove2.me/submissions/b4bc38c4-3231-41a6-8c33-7fceca35040a

import Definitions.Def_RH1E6S11_D038_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0306 : RS5.BandZeros ((43982337246 : ℝ) / 65536) ((43986853696 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0306.s0 RH1E6S11_0306.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0306.s0 RH1E6S11_0306.rest = RH1E6S11_0306.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0306.s0 :: RH1E6S11_0306.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0306.s0.t = ((43982337246 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0306.s0]
  have e1 : RH1E6S11_0306.sL.t = ((43986853696 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0306.sL]
  rw [e0, e1] at h
  exact h

theorem band_0307 : RS5.BandZeros ((43986853696 : ℝ) / 65536) ((43991370106 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0307.s0 RH1E6S11_0307.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0307.s0 RH1E6S11_0307.rest = RH1E6S11_0307.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0307.s0 :: RH1E6S11_0307.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0307.s0.t = ((43986853696 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0307.s0]
  have e1 : RH1E6S11_0307.sL.t = ((43991370106 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0307.sL]
  rw [e0, e1] at h
  exact h

theorem part_038_1 : RS5.BandZeros ((43982337246 : ℝ) / 65536) ((43991370106 : ℝ) / 65536) 254 := by
  have g0 := band_0306
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0307
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43982337246 : ℝ) / 65536) ((43991370106 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_038_1 <;> assumption
