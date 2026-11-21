-- Prove2me | solution 1 for RH1E6S06.part_046_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T19:13:08.556628+00:00
-- url     : https://prove2.me/submissions/16c677ec-d108-4c6b-9108-b9324ac680ce

import Definitions.Def_RH1E6S06_D046_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0368 : RS5.BandZeros ((27949161023 : ℝ) / 65536) ((27953844510 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0368.s0 RH1E6S06_0368.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0368.s0 RH1E6S06_0368.rest = RH1E6S06_0368.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0368.s0 :: RH1E6S06_0368.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0368.s0.t = ((27949161023 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0368.s0]
  have e1 : RH1E6S06_0368.sL.t = ((27953844510 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0368.sL]
  rw [e0, e1] at h
  exact h

theorem band_0369 : RS5.BandZeros ((27953844510 : ℝ) / 65536) ((27958554189 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0369.s0 RH1E6S06_0369.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0369.s0 RH1E6S06_0369.rest = RH1E6S06_0369.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0369.s0 :: RH1E6S06_0369.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0369.s0.t = ((27953844510 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0369.s0]
  have e1 : RH1E6S06_0369.sL.t = ((27958554189 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0369.sL]
  rw [e0, e1] at h
  exact h

theorem part_046_0 : RS5.BandZeros ((27949161023 : ℝ) / 65536) ((27958554189 : ℝ) / 65536) 254 := by
  have g0 := band_0368
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0369
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27949161023 : ℝ) / 65536) ((27958554189 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_046_0 <;> assumption
