-- Prove2me | solution 1 for RH1E6S11.part_082_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:55:48.069738+00:00
-- url     : https://prove2.me/submissions/d41e03ca-8bb7-46c6-8046-92489aa061f9

import Definitions.Def_RH1E6S11_D082_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0656 : RS5.BandZeros ((45560684668 : ℝ) / 65536) ((45565178545 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0656.s0 RH1E6S11_0656.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0656.s0 RH1E6S11_0656.rest = RH1E6S11_0656.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0656.s0 :: RH1E6S11_0656.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0656.s0.t = ((45560684668 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0656.s0]
  have e1 : RH1E6S11_0656.sL.t = ((45565178545 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0656.sL]
  rw [e0, e1] at h
  exact h

theorem band_0657 : RS5.BandZeros ((45565178545 : ℝ) / 65536) ((45569690110 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0657.s0 RH1E6S11_0657.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0657.s0 RH1E6S11_0657.rest = RH1E6S11_0657.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0657.s0 :: RH1E6S11_0657.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0657.s0.t = ((45565178545 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0657.s0]
  have e1 : RH1E6S11_0657.sL.t = ((45569690110 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0657.sL]
  rw [e0, e1] at h
  exact h

theorem part_082_0 : RS5.BandZeros ((45560684668 : ℝ) / 65536) ((45569690110 : ℝ) / 65536) 254 := by
  have g0 := band_0656
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0657
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45560684668 : ℝ) / 65536) ((45569690110 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_082_0 <;> assumption
