-- Prove2me | solution 1 for RH1E6S06.part_052_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T19:29:13.836591+00:00
-- url     : https://prove2.me/submissions/4e829b11-b4f3-4192-abe9-fb3b81760c33

import Definitions.Def_RH1E6S06_D052_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem band_0416 : RS5.BandZeros ((28174678761 : ℝ) / 65536) ((28179385111 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0416.s0 RH1E6S06_0416.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0416.s0 RH1E6S06_0416.rest = RH1E6S06_0416.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0416.s0 :: RH1E6S06_0416.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0416.s0.t = ((28174678761 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0416.s0]
  have e1 : RH1E6S06_0416.sL.t = ((28179385111 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0416.sL]
  rw [e0, e1] at h
  exact h

theorem band_0417 : RS5.BandZeros ((28179385111 : ℝ) / 65536) ((28184063653 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S06_0417.s0 RH1E6S06_0417.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S06_0417.s0 RH1E6S06_0417.rest = RH1E6S06_0417.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S06_0417.s0 :: RH1E6S06_0417.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S06_0417.s0.t = ((28179385111 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0417.s0]
  have e1 : RH1E6S06_0417.sL.t = ((28184063653 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S06_0417.sL]
  rw [e0, e1] at h
  exact h

theorem part_052_0 : RS5.BandZeros ((28174678761 : ℝ) / 65536) ((28184063653 : ℝ) / 65536) 254 := by
  have g0 := band_0416
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0417
  exact g1

end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28174678761 : ℝ) / 65536) ((28184063653 : ℝ) / 65536) 254 := by
  apply RH1E6S06.part_052_0 <;> assumption
