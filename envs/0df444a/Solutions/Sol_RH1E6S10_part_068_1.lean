-- Prove2me | solution 1 for RH1E6S10.part_068_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:01:50.2218+00:00
-- url     : https://prove2.me/submissions/aa92bfa7-1cfb-43e3-8824-32b3e421d7e0

import Definitions.Def_RH1E6S10_D068_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0546 : RS5.BandZeros ((41805003990 : ℝ) / 65536) ((41809540331 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0546.s0 RH1E6S10_0546.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0546.s0 RH1E6S10_0546.rest = RH1E6S10_0546.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0546.s0 :: RH1E6S10_0546.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0546.s0.t = ((41805003990 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0546.s0]
  have e1 : RH1E6S10_0546.sL.t = ((41809540331 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0546.sL]
  rw [e0, e1] at h
  exact h

theorem band_0547 : RS5.BandZeros ((41809540331 : ℝ) / 65536) ((41814076628 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0547.s0 RH1E6S10_0547.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0547.s0 RH1E6S10_0547.rest = RH1E6S10_0547.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0547.s0 :: RH1E6S10_0547.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0547.s0.t = ((41809540331 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0547.s0]
  have e1 : RH1E6S10_0547.sL.t = ((41814076628 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0547.sL]
  rw [e0, e1] at h
  exact h

theorem part_068_1 : RS5.BandZeros ((41805003990 : ℝ) / 65536) ((41814076628 : ℝ) / 65536) 254 := by
  have g0 := band_0546
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0547
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41805003990 : ℝ) / 65536) ((41814076628 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_068_1 <;> assumption
