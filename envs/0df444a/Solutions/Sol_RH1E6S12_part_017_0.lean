-- Prove2me | solution 1 for RH1E6S12.part_017_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:14:18.465002+00:00
-- url     : https://prove2.me/submissions/22b9880c-3eea-4cfd-b7ad-abbc64d70e03

import Definitions.Def_RH1E6S12_D017_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0136 : RS5.BandZeros ((46486884654 : ℝ) / 65536) ((46491372568 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0136.s0 RH1E6S12_0136.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0136.s0 RH1E6S12_0136.rest = RH1E6S12_0136.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0136.s0 :: RH1E6S12_0136.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0136.s0.t = ((46486884654 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0136.s0]
  have e1 : RH1E6S12_0136.sL.t = ((46491372568 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0136.sL]
  rw [e0, e1] at h
  exact h

theorem band_0137 : RS5.BandZeros ((46491372568 : ℝ) / 65536) ((46495870544 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0137.s0 RH1E6S12_0137.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0137.s0 RH1E6S12_0137.rest = RH1E6S12_0137.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0137.s0 :: RH1E6S12_0137.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0137.s0.t = ((46491372568 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0137.s0]
  have e1 : RH1E6S12_0137.sL.t = ((46495870544 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0137.sL]
  rw [e0, e1] at h
  exact h

theorem part_017_0 : RS5.BandZeros ((46486884654 : ℝ) / 65536) ((46495870544 : ℝ) / 65536) 254 := by
  have g0 := band_0136
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0137
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46486884654 : ℝ) / 65536) ((46495870544 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_017_0 <;> assumption
