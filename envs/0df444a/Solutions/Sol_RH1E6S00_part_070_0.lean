-- Prove2me | solution 1 for RH1E6S00.part_070_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:06:40.216726+00:00
-- url     : https://prove2.me/submissions/3a31f853-7409-4e3a-ac17-cf0c29c9591a

import Definitions.Def_RH1E6S00_D070_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0560 : RS5.BandZeros ((9519737628 : ℝ) / 65536) ((9524941837 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0560.s0 RH1E6S00_0560.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0560.s0 RH1E6S00_0560.rest = RH1E6S00_0560.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0560.s0 :: RH1E6S00_0560.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0560.s0.t = ((9519737628 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0560.s0]
  have e1 : RH1E6S00_0560.sL.t = ((9524941837 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0560.sL]
  rw [e0, e1] at h
  exact h

theorem band_0561 : RS5.BandZeros ((9524941837 : ℝ) / 65536) ((9530166251 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0561.s0 RH1E6S00_0561.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0561.s0 RH1E6S00_0561.rest = RH1E6S00_0561.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0561.s0 :: RH1E6S00_0561.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0561.s0.t = ((9524941837 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0561.s0]
  have e1 : RH1E6S00_0561.sL.t = ((9530166251 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0561.sL]
  rw [e0, e1] at h
  exact h

theorem part_070_0 : RS5.BandZeros ((9519737628 : ℝ) / 65536) ((9530166251 : ℝ) / 65536) 254 := by
  have g0 := band_0560
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0561
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9519737628 : ℝ) / 65536) ((9530166251 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_070_0 <;> assumption
