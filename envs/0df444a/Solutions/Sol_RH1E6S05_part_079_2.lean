-- Prove2me | solution 1 for RH1E6S05.part_079_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T16:25:46.112289+00:00
-- url     : https://prove2.me/submissions/4455a00d-4e6c-4eac-bb6d-8b8925c47171

import Definitions.Def_RH1E6S05_D079_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0636 : RS5.BandZeros ((25963688249 : ℝ) / 65536) ((25968429398 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0636.s0 RH1E6S05_0636.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0636.s0 RH1E6S05_0636.rest = RH1E6S05_0636.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0636.s0 :: RH1E6S05_0636.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0636.s0.t = ((25963688249 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0636.s0]
  have e1 : RH1E6S05_0636.sL.t = ((25968429398 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0636.sL]
  rw [e0, e1] at h
  exact h

theorem band_0637 : RS5.BandZeros ((25968429398 : ℝ) / 65536) ((25973161154 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0637.s0 RH1E6S05_0637.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0637.s0 RH1E6S05_0637.rest = RH1E6S05_0637.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0637.s0 :: RH1E6S05_0637.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0637.s0.t = ((25968429398 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0637.s0]
  have e1 : RH1E6S05_0637.sL.t = ((25973161154 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0637.sL]
  rw [e0, e1] at h
  exact h

theorem part_079_2 : RS5.BandZeros ((25963688249 : ℝ) / 65536) ((25973161154 : ℝ) / 65536) 254 := by
  have g0 := band_0636
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0637
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25963688249 : ℝ) / 65536) ((25973161154 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_079_2 <;> assumption
