-- Prove2me | solution 1 for RH1E6S00.part_066_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:01:44.774854+00:00
-- url     : https://prove2.me/submissions/3b1befe4-3f1f-4125-a0e4-1b3a700efb10

import Definitions.Def_RH1E6S00_D066_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0534 : RS5.BandZeros ((9384328212 : ℝ) / 65536) ((9389539849 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0534.s0 RH1E6S00_0534.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0534.s0 RH1E6S00_0534.rest = RH1E6S00_0534.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0534.s0 :: RH1E6S00_0534.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0534.s0.t = ((9384328212 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0534.s0]
  have e1 : RH1E6S00_0534.sL.t = ((9389539849 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0534.sL]
  rw [e0, e1] at h
  exact h

theorem band_0535 : RS5.BandZeros ((9389539849 : ℝ) / 65536) ((9394761456 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0535.s0 RH1E6S00_0535.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0535.s0 RH1E6S00_0535.rest = RH1E6S00_0535.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0535.s0 :: RH1E6S00_0535.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0535.s0.t = ((9389539849 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0535.s0]
  have e1 : RH1E6S00_0535.sL.t = ((9394761456 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0535.sL]
  rw [e0, e1] at h
  exact h

theorem part_066_3 : RS5.BandZeros ((9384328212 : ℝ) / 65536) ((9394761456 : ℝ) / 65536) 254 := by
  have g0 := band_0534
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0535
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9384328212 : ℝ) / 65536) ((9394761456 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_066_3 <;> assumption
