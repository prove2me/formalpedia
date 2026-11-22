-- Prove2me | solution 1 for RH1E6S12.part_068_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T16:35:54.268304+00:00
-- url     : https://prove2.me/submissions/8ffdd44f-dfec-4e63-a47f-1b7fc4458d37

import Definitions.Def_RH1E6S12_D068_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0546 : RS5.BandZeros ((48326732805 : ℝ) / 65536) ((48331214503 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0546.s0 RH1E6S12_0546.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0546.s0 RH1E6S12_0546.rest = RH1E6S12_0546.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0546.s0 :: RH1E6S12_0546.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0546.s0.t = ((48326732805 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0546.s0]
  have e1 : RH1E6S12_0546.sL.t = ((48331214503 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0546.sL]
  rw [e0, e1] at h
  exact h

theorem band_0547 : RS5.BandZeros ((48331214503 : ℝ) / 65536) ((48335707235 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0547.s0 RH1E6S12_0547.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0547.s0 RH1E6S12_0547.rest = RH1E6S12_0547.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0547.s0 :: RH1E6S12_0547.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0547.s0.t = ((48331214503 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0547.s0]
  have e1 : RH1E6S12_0547.sL.t = ((48335707235 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0547.sL]
  rw [e0, e1] at h
  exact h

theorem part_068_1 : RS5.BandZeros ((48326732805 : ℝ) / 65536) ((48335707235 : ℝ) / 65536) 254 := by
  have g0 := band_0546
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0547
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48326732805 : ℝ) / 65536) ((48335707235 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_068_1 <;> assumption
