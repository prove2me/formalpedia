-- Prove2me | solution 1 for RH1E6S07.part_012_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T23:28:24.096186+00:00
-- url     : https://prove2.me/submissions/e11a8a18-77c7-44f6-abdf-5f93cd253b9e

import Definitions.Def_RH1E6S07_D012_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0098 : RS5.BandZeros ((29949327177 : ℝ) / 65536) ((29954000429 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0098.s0 RH1E6S07_0098.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0098.s0 RH1E6S07_0098.rest = RH1E6S07_0098.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0098.s0 :: RH1E6S07_0098.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0098.s0.t = ((29949327177 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0098.s0]
  have e1 : RH1E6S07_0098.sL.t = ((29954000429 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0098.sL]
  rw [e0, e1] at h
  exact h

theorem band_0099 : RS5.BandZeros ((29954000429 : ℝ) / 65536) ((29958648332 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0099.s0 RH1E6S07_0099.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0099.s0 RH1E6S07_0099.rest = RH1E6S07_0099.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0099.s0 :: RH1E6S07_0099.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0099.s0.t = ((29954000429 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0099.s0]
  have e1 : RH1E6S07_0099.sL.t = ((29958648332 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0099.sL]
  rw [e0, e1] at h
  exact h

theorem part_012_1 : RS5.BandZeros ((29949327177 : ℝ) / 65536) ((29958648332 : ℝ) / 65536) 254 := by
  have g0 := band_0098
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0099
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((29949327177 : ℝ) / 65536) ((29958648332 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_012_1 <;> assumption
