-- Prove2me | solution 1 for RH1E6S06.part_026_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:19:22.373171+00:00
-- url     : https://prove2.me/submissions/27c22e58-0a99-4551-b4a0-b9efc6a0e303

import Definitions.Def_RH1E6S06_D026_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0208 : RS5.BandZeros ((27196135072 : ℝ) / 65536) ((27200850768 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0208.s0 RH1E6S06_0208.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0208.s0 RH1E6S06_0208.rest = RH1E6S06_0208.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0208.s0 :: RH1E6S06_0208.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0208.s0.t = ((27196135072 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0208.s0]
  have e1 : RH1E6S06_0208.sL.t = ((27200850768 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0208.sL]
  rw [e0, e1] at h
  exact h

theorem band_0209 : RS5.BandZeros ((27200850768 : ℝ) / 65536) ((27205565173 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0209.s0 RH1E6S06_0209.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0209.s0 RH1E6S06_0209.rest = RH1E6S06_0209.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0209.s0 :: RH1E6S06_0209.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0209.s0.t = ((27200850768 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0209.s0]
  have e1 : RH1E6S06_0209.sL.t = ((27205565173 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0209.sL]
  rw [e0, e1] at h
  exact h

theorem part_026_0 : RS5.BandZeros ((27196135072 : ℝ) / 65536) ((27205565173 : ℝ) / 65536) 254 := by
  have g0 := band_0208
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0209
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27196135072 : ℝ) / 65536) ((27205565173 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_026_0 <;> assumption
