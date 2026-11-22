-- Prove2me | solution 1 for RH1E6S11.part_068_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:15:51.113208+00:00
-- url     : https://prove2.me/submissions/28145b6d-f427-48ac-ad44-52f61fd64b44

import Definitions.Def_RH1E6S11_D068_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0546 : RS5.BandZeros ((45065139384 : ℝ) / 65536) ((45069655240 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0546.s0 RH1E6S11_0546.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0546.s0 RH1E6S11_0546.rest = RH1E6S11_0546.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0546.s0 :: RH1E6S11_0546.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0546.s0.t = ((45065139384 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0546.s0]
  have e1 : RH1E6S11_0546.sL.t = ((45069655240 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0546.sL]
  rw [e0, e1] at h
  exact h

theorem band_0547 : RS5.BandZeros ((45069655240 : ℝ) / 65536) ((45074179929 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0547.s0 RH1E6S11_0547.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0547.s0 RH1E6S11_0547.rest = RH1E6S11_0547.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0547.s0 :: RH1E6S11_0547.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0547.s0.t = ((45069655240 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0547.s0]
  have e1 : RH1E6S11_0547.sL.t = ((45074179929 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0547.sL]
  rw [e0, e1] at h
  exact h

theorem part_068_1 : RS5.BandZeros ((45065139384 : ℝ) / 65536) ((45074179929 : ℝ) / 65536) 254 := by
  have g0 := band_0546
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0547
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45065139384 : ℝ) / 65536) ((45074179929 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_068_1 <;> assumption
