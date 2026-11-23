-- Prove2me | solution 1 for RH1E6S15.part_024_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T09:18:15.679641+00:00
-- url     : https://prove2.me/submissions/cd98bb30-dde7-4474-8087-dc0eb5a51cb7

import Definitions.Def_RH1E6S15_D024_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem band_0194 : RS5.BandZeros ((56563681567 : ℝ) / 65536) ((56568104034 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0194.s0 RH1E6S15_0194.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0194.s0 RH1E6S15_0194.rest = RH1E6S15_0194.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0194.s0 :: RH1E6S15_0194.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0194.s0.t = ((56563681567 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0194.s0]
  have e1 : RH1E6S15_0194.sL.t = ((56568104034 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0194.sL]
  rw [e0, e1] at h
  exact h

theorem band_0195 : RS5.BandZeros ((56568104034 : ℝ) / 65536) ((56572515601 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S15_0195.s0 RH1E6S15_0195.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S15_0195.s0 RH1E6S15_0195.rest = RH1E6S15_0195.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S15_0195.s0 :: RH1E6S15_0195.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S15_0195.s0.t = ((56568104034 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0195.s0]
  have e1 : RH1E6S15_0195.sL.t = ((56572515601 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S15_0195.sL]
  rw [e0, e1] at h
  exact h

theorem part_024_1 : RS5.BandZeros ((56563681567 : ℝ) / 65536) ((56572515601 : ℝ) / 65536) 254 := by
  have g0 := band_0194
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0195
  exact g1

end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56563681567 : ℝ) / 65536) ((56572515601 : ℝ) / 65536) 254 := by
  apply RH1E6S15.part_024_1 <;> assumption
