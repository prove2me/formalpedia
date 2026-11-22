-- Prove2me | solution 1 for RH1E6S11.part_047_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T05:13:32.376256+00:00
-- url     : https://prove2.me/submissions/9a22e8b5-0713-4268-94a2-b1c6cab52b9d

import Definitions.Def_RH1E6S11_D047_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0376 : RS5.BandZeros ((44298392315 : ℝ) / 65536) ((44302888204 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0376.s0 RH1E6S11_0376.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0376.s0 RH1E6S11_0376.rest = RH1E6S11_0376.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0376.s0 :: RH1E6S11_0376.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0376.s0.t = ((44298392315 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0376.s0]
  have e1 : RH1E6S11_0376.sL.t = ((44302888204 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0376.sL]
  rw [e0, e1] at h
  exact h

theorem band_0377 : RS5.BandZeros ((44302888204 : ℝ) / 65536) ((44307419593 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0377.s0 RH1E6S11_0377.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0377.s0 RH1E6S11_0377.rest = RH1E6S11_0377.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0377.s0 :: RH1E6S11_0377.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0377.s0.t = ((44302888204 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0377.s0]
  have e1 : RH1E6S11_0377.sL.t = ((44307419593 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0377.sL]
  rw [e0, e1] at h
  exact h

theorem part_047_0 : RS5.BandZeros ((44298392315 : ℝ) / 65536) ((44307419593 : ℝ) / 65536) 254 := by
  have g0 := band_0376
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0377
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44298392315 : ℝ) / 65536) ((44307419593 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_047_0 <;> assumption
