-- Prove2me | solution 1 for RH1E6S16.part_073_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:28:07.206971+00:00
-- url     : https://prove2.me/submissions/747b4bd1-126a-415c-a57f-9b32847983f0

import Definitions.Def_RH1E6S16_D073_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem band_0586 : RS5.BandZeros ((61558953809 : ℝ) / 65536) ((61563331980 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0586.s0 RH1E6S16_0586.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0586.s0 RH1E6S16_0586.rest = RH1E6S16_0586.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0586.s0 :: RH1E6S16_0586.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0586.s0.t = ((61558953809 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0586.s0]
  have e1 : RH1E6S16_0586.sL.t = ((61563331980 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0586.sL]
  rw [e0, e1] at h
  exact h

theorem band_0587 : RS5.BandZeros ((61563331980 : ℝ) / 65536) ((61567725935 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S16_0587.s0 RH1E6S16_0587.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S16_0587.s0 RH1E6S16_0587.rest = RH1E6S16_0587.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S16_0587.s0 :: RH1E6S16_0587.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S16_0587.s0.t = ((61563331980 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0587.s0]
  have e1 : RH1E6S16_0587.sL.t = ((61567725935 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S16_0587.sL]
  rw [e0, e1] at h
  exact h

theorem part_073_1 : RS5.BandZeros ((61558953809 : ℝ) / 65536) ((61567725935 : ℝ) / 65536) 254 := by
  have g0 := band_0586
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0587
  exact g1

end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61558953809 : ℝ) / 65536) ((61567725935 : ℝ) / 65536) 254 := by
  apply RH1E6S16.part_073_1 <;> assumption
