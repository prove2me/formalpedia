-- Prove2me | solution 1 for RH1E6S02.part_029_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:10:27.868048+00:00
-- url     : https://prove2.me/submissions/20ea7012-8482-415d-af5b-248b773f86cc

import Definitions.Def_RH1E6S02_D029_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0232 : RS5.BandZeros ((14272531522 : ℝ) / 65536) ((14277521278 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0232.s0 RH1E6S02_0232.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0232.s0 RH1E6S02_0232.rest = RH1E6S02_0232.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0232.s0 :: RH1E6S02_0232.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0232.s0.t = ((14272531522 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0232.s0]
  have e1 : RH1E6S02_0232.sL.t = ((14277521278 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0232.sL]
  rw [e0, e1] at h
  exact h

theorem band_0233 : RS5.BandZeros ((14277521278 : ℝ) / 65536) ((14282511668 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0233.s0 RH1E6S02_0233.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0233.s0 RH1E6S02_0233.rest = RH1E6S02_0233.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0233.s0 :: RH1E6S02_0233.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0233.s0.t = ((14277521278 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0233.s0]
  have e1 : RH1E6S02_0233.sL.t = ((14282511668 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0233.sL]
  rw [e0, e1] at h
  exact h

theorem part_029_0 : RS5.BandZeros ((14272531522 : ℝ) / 65536) ((14282511668 : ℝ) / 65536) 254 := by
  have g0 := band_0232
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0233
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14272531522 : ℝ) / 65536) ((14282511668 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_029_0 <;> assumption
