-- Prove2me | solution 1 for RH1E6S10.part_011_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T18:01:25.215128+00:00
-- url     : https://prove2.me/submissions/3bbf6fa7-bc69-494d-8f12-4cf4c0b831e6

import Definitions.Def_RH1E6S10_D011_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0088 : RS5.BandZeros ((39722775509 : ℝ) / 65536) ((39727332042 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0088.s0 RH1E6S10_0088.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0088.s0 RH1E6S10_0088.rest = RH1E6S10_0088.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0088.s0 :: RH1E6S10_0088.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0088.s0.t = ((39722775509 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0088.s0]
  have e1 : RH1E6S10_0088.sL.t = ((39727332042 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0088.sL]
  rw [e0, e1] at h
  exact h

theorem band_0089 : RS5.BandZeros ((39727332042 : ℝ) / 65536) ((39731897499 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0089.s0 RH1E6S10_0089.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0089.s0 RH1E6S10_0089.rest = RH1E6S10_0089.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0089.s0 :: RH1E6S10_0089.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0089.s0.t = ((39727332042 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0089.s0]
  have e1 : RH1E6S10_0089.sL.t = ((39731897499 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0089.sL]
  rw [e0, e1] at h
  exact h

theorem part_011_0 : RS5.BandZeros ((39722775509 : ℝ) / 65536) ((39731897499 : ℝ) / 65536) 254 := by
  have g0 := band_0088
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0089
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39722775509 : ℝ) / 65536) ((39731897499 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_011_0 <;> assumption
