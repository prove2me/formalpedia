-- Prove2me | solution 1 for RH1E5.group_039
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:20:15.178841+00:00
-- url     : https://prove2.me/submissions/66ab2745-f4d4-4b6a-9dd7-e398de0ec8c7

import Definitions.Def_RH1E5_Data039
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0312 : RS5.BandZeros RH1E5_0312.s0.t RH1E5_0312.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0312.s0 RH1E5_0312.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0312.s0 RH1E5_0312.rest = RH1E5_0312.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0312.s0 :: RH1E5_0312.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0313 : RS5.BandZeros RH1E5_0313.s0.t RH1E5_0313.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0313.s0 RH1E5_0313.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0313.s0 RH1E5_0313.rest = RH1E5_0313.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0313.s0 :: RH1E5_0313.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0314 : RS5.BandZeros RH1E5_0314.s0.t RH1E5_0314.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0314.s0 RH1E5_0314.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0314.s0 RH1E5_0314.rest = RH1E5_0314.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0314.s0 :: RH1E5_0314.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0315 : RS5.BandZeros RH1E5_0315.s0.t RH1E5_0315.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0315.s0 RH1E5_0315.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0315.s0 RH1E5_0315.rest = RH1E5_0315.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0315.s0 :: RH1E5_0315.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0316 : RS5.BandZeros RH1E5_0316.s0.t RH1E5_0316.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0316.s0 RH1E5_0316.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0316.s0 RH1E5_0316.rest = RH1E5_0316.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0316.s0 :: RH1E5_0316.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0317 : RS5.BandZeros RH1E5_0317.s0.t RH1E5_0317.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0317.s0 RH1E5_0317.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0317.s0 RH1E5_0317.rest = RH1E5_0317.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0317.s0 :: RH1E5_0317.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0318 : RS5.BandZeros RH1E5_0318.s0.t RH1E5_0318.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0318.s0 RH1E5_0318.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0318.s0 RH1E5_0318.rest = RH1E5_0318.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0318.s0 :: RH1E5_0318.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0319 : RS5.BandZeros RH1E5_0319.s0.t RH1E5_0319.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0319.s0 RH1E5_0319.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0319.s0 RH1E5_0319.rest = RH1E5_0319.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0319.s0 :: RH1E5_0319.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_039 : RS5.BandZeros RH1E5_0312.s0.t RH1E5_0319.sL.t 1016 := by
  have g312 := band_0312
  have g313 := RS5.BandZeros.glue (a := RH1E5_0312.s0.t) (b := RH1E5_0312.sL.t) (c := RH1E5_0313.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0312.s0, RH1E5_0311.sL, RH1E5_0312.sL]) (by norm_num [RS5.Sample.t, RH1E5_0312.sL, RH1E5_0313.sL]) g312 band_0313
  have g314 := RS5.BandZeros.glue (a := RH1E5_0312.s0.t) (b := RH1E5_0313.sL.t) (c := RH1E5_0314.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0312.s0, RH1E5_0311.sL, RH1E5_0313.sL]) (by norm_num [RS5.Sample.t, RH1E5_0313.sL, RH1E5_0314.sL]) g313 band_0314
  have g315 := RS5.BandZeros.glue (a := RH1E5_0312.s0.t) (b := RH1E5_0314.sL.t) (c := RH1E5_0315.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0312.s0, RH1E5_0311.sL, RH1E5_0314.sL]) (by norm_num [RS5.Sample.t, RH1E5_0314.sL, RH1E5_0315.sL]) g314 band_0315
  have g316 := RS5.BandZeros.glue (a := RH1E5_0312.s0.t) (b := RH1E5_0315.sL.t) (c := RH1E5_0316.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0312.s0, RH1E5_0311.sL, RH1E5_0315.sL]) (by norm_num [RS5.Sample.t, RH1E5_0315.sL, RH1E5_0316.sL]) g315 band_0316
  have g317 := RS5.BandZeros.glue (a := RH1E5_0312.s0.t) (b := RH1E5_0316.sL.t) (c := RH1E5_0317.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0312.s0, RH1E5_0311.sL, RH1E5_0316.sL]) (by norm_num [RS5.Sample.t, RH1E5_0316.sL, RH1E5_0317.sL]) g316 band_0317
  have g318 := RS5.BandZeros.glue (a := RH1E5_0312.s0.t) (b := RH1E5_0317.sL.t) (c := RH1E5_0318.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0312.s0, RH1E5_0311.sL, RH1E5_0317.sL]) (by norm_num [RS5.Sample.t, RH1E5_0317.sL, RH1E5_0318.sL]) g317 band_0318
  have g319 := RS5.BandZeros.glue (a := RH1E5_0312.s0.t) (b := RH1E5_0318.sL.t) (c := RH1E5_0319.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0312.s0, RH1E5_0311.sL, RH1E5_0318.sL]) (by norm_num [RS5.Sample.t, RH1E5_0318.sL, RH1E5_0319.sL]) g318 band_0319
  exact g319

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0312.s0.t RH1E5_0319.sL.t 1016 := by
  apply RH1E5.group_039 <;> assumption
