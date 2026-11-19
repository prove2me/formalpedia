-- Prove2me | solution 1 for RH1E5.group_034
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:07:40.710444+00:00
-- url     : https://prove2.me/submissions/7469b909-43a0-43c4-a2c3-7ec354b75f4a

import Definitions.Def_RH1E5_Data034
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0272 : RS5.BandZeros RH1E5_0272.s0.t RH1E5_0272.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0272.s0 RH1E5_0272.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0272.s0 RH1E5_0272.rest = RH1E5_0272.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0272.s0 :: RH1E5_0272.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0273 : RS5.BandZeros RH1E5_0273.s0.t RH1E5_0273.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0273.s0 RH1E5_0273.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0273.s0 RH1E5_0273.rest = RH1E5_0273.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0273.s0 :: RH1E5_0273.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0274 : RS5.BandZeros RH1E5_0274.s0.t RH1E5_0274.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0274.s0 RH1E5_0274.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0274.s0 RH1E5_0274.rest = RH1E5_0274.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0274.s0 :: RH1E5_0274.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0275 : RS5.BandZeros RH1E5_0275.s0.t RH1E5_0275.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0275.s0 RH1E5_0275.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0275.s0 RH1E5_0275.rest = RH1E5_0275.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0275.s0 :: RH1E5_0275.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0276 : RS5.BandZeros RH1E5_0276.s0.t RH1E5_0276.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0276.s0 RH1E5_0276.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0276.s0 RH1E5_0276.rest = RH1E5_0276.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0276.s0 :: RH1E5_0276.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0277 : RS5.BandZeros RH1E5_0277.s0.t RH1E5_0277.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0277.s0 RH1E5_0277.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0277.s0 RH1E5_0277.rest = RH1E5_0277.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0277.s0 :: RH1E5_0277.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0278 : RS5.BandZeros RH1E5_0278.s0.t RH1E5_0278.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0278.s0 RH1E5_0278.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0278.s0 RH1E5_0278.rest = RH1E5_0278.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0278.s0 :: RH1E5_0278.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0279 : RS5.BandZeros RH1E5_0279.s0.t RH1E5_0279.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0279.s0 RH1E5_0279.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0279.s0 RH1E5_0279.rest = RH1E5_0279.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0279.s0 :: RH1E5_0279.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_034 : RS5.BandZeros RH1E5_0272.s0.t RH1E5_0279.sL.t 1016 := by
  have g272 := band_0272
  have g273 := RS5.BandZeros.glue (a := RH1E5_0272.s0.t) (b := RH1E5_0272.sL.t) (c := RH1E5_0273.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0272.s0, RH1E5_0271.sL, RH1E5_0272.sL]) (by norm_num [RS5.Sample.t, RH1E5_0272.sL, RH1E5_0273.sL]) g272 band_0273
  have g274 := RS5.BandZeros.glue (a := RH1E5_0272.s0.t) (b := RH1E5_0273.sL.t) (c := RH1E5_0274.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0272.s0, RH1E5_0271.sL, RH1E5_0273.sL]) (by norm_num [RS5.Sample.t, RH1E5_0273.sL, RH1E5_0274.sL]) g273 band_0274
  have g275 := RS5.BandZeros.glue (a := RH1E5_0272.s0.t) (b := RH1E5_0274.sL.t) (c := RH1E5_0275.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0272.s0, RH1E5_0271.sL, RH1E5_0274.sL]) (by norm_num [RS5.Sample.t, RH1E5_0274.sL, RH1E5_0275.sL]) g274 band_0275
  have g276 := RS5.BandZeros.glue (a := RH1E5_0272.s0.t) (b := RH1E5_0275.sL.t) (c := RH1E5_0276.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0272.s0, RH1E5_0271.sL, RH1E5_0275.sL]) (by norm_num [RS5.Sample.t, RH1E5_0275.sL, RH1E5_0276.sL]) g275 band_0276
  have g277 := RS5.BandZeros.glue (a := RH1E5_0272.s0.t) (b := RH1E5_0276.sL.t) (c := RH1E5_0277.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0272.s0, RH1E5_0271.sL, RH1E5_0276.sL]) (by norm_num [RS5.Sample.t, RH1E5_0276.sL, RH1E5_0277.sL]) g276 band_0277
  have g278 := RS5.BandZeros.glue (a := RH1E5_0272.s0.t) (b := RH1E5_0277.sL.t) (c := RH1E5_0278.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0272.s0, RH1E5_0271.sL, RH1E5_0277.sL]) (by norm_num [RS5.Sample.t, RH1E5_0277.sL, RH1E5_0278.sL]) g277 band_0278
  have g279 := RS5.BandZeros.glue (a := RH1E5_0272.s0.t) (b := RH1E5_0278.sL.t) (c := RH1E5_0279.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0272.s0, RH1E5_0271.sL, RH1E5_0278.sL]) (by norm_num [RS5.Sample.t, RH1E5_0278.sL, RH1E5_0279.sL]) g278 band_0279
  exact g279

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0272.s0.t RH1E5_0279.sL.t 1016 := by
  apply RH1E5.group_034 <;> assumption
