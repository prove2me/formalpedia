-- Prove2me | solution 1 for RH1E6S11.part_029_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T04:25:19.79384+00:00
-- url     : https://prove2.me/submissions/ef2b2316-8e98-4b6a-8405-8c157f83cf8b

import Definitions.Def_RH1E6S11_D029_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem band_0236 : RS5.BandZeros ((43666077009 : ℝ) / 65536) ((43670605171 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0236.s0 RH1E6S11_0236.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0236.s0 RH1E6S11_0236.rest = RH1E6S11_0236.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0236.s0 :: RH1E6S11_0236.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0236.s0.t = ((43666077009 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0236.s0]
  have e1 : RH1E6S11_0236.sL.t = ((43670605171 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0236.sL]
  rw [e0, e1] at h
  exact h

theorem band_0237 : RS5.BandZeros ((43670605171 : ℝ) / 65536) ((43675124398 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S11_0237.s0 RH1E6S11_0237.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S11_0237.s0 RH1E6S11_0237.rest = RH1E6S11_0237.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S11_0237.s0 :: RH1E6S11_0237.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S11_0237.s0.t = ((43670605171 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0237.s0]
  have e1 : RH1E6S11_0237.sL.t = ((43675124398 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S11_0237.sL]
  rw [e0, e1] at h
  exact h

theorem part_029_2 : RS5.BandZeros ((43666077009 : ℝ) / 65536) ((43675124398 : ℝ) / 65536) 254 := by
  have g0 := band_0236
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0237
  exact g1

end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((43666077009 : ℝ) / 65536) ((43675124398 : ℝ) / 65536) 254 := by
  apply RH1E6S11.part_029_2 <;> assumption
