-- Prove2me | solution 1 for RH1E5.group_031
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:00:15.396199+00:00
-- url     : https://prove2.me/submissions/94b3c0eb-c850-4cd7-832c-99c679c337f8

import Definitions.Def_RH1E5_Data031
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0248 : RS5.BandZeros RH1E5_0248.s0.t RH1E5_0248.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0248.s0 RH1E5_0248.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0248.s0 RH1E5_0248.rest = RH1E5_0248.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0248.s0 :: RH1E5_0248.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0249 : RS5.BandZeros RH1E5_0249.s0.t RH1E5_0249.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0249.s0 RH1E5_0249.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0249.s0 RH1E5_0249.rest = RH1E5_0249.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0249.s0 :: RH1E5_0249.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0250 : RS5.BandZeros RH1E5_0250.s0.t RH1E5_0250.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0250.s0 RH1E5_0250.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0250.s0 RH1E5_0250.rest = RH1E5_0250.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0250.s0 :: RH1E5_0250.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0251 : RS5.BandZeros RH1E5_0251.s0.t RH1E5_0251.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0251.s0 RH1E5_0251.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0251.s0 RH1E5_0251.rest = RH1E5_0251.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0251.s0 :: RH1E5_0251.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0252 : RS5.BandZeros RH1E5_0252.s0.t RH1E5_0252.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0252.s0 RH1E5_0252.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0252.s0 RH1E5_0252.rest = RH1E5_0252.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0252.s0 :: RH1E5_0252.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0253 : RS5.BandZeros RH1E5_0253.s0.t RH1E5_0253.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0253.s0 RH1E5_0253.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0253.s0 RH1E5_0253.rest = RH1E5_0253.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0253.s0 :: RH1E5_0253.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0254 : RS5.BandZeros RH1E5_0254.s0.t RH1E5_0254.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0254.s0 RH1E5_0254.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0254.s0 RH1E5_0254.rest = RH1E5_0254.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0254.s0 :: RH1E5_0254.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0255 : RS5.BandZeros RH1E5_0255.s0.t RH1E5_0255.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0255.s0 RH1E5_0255.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0255.s0 RH1E5_0255.rest = RH1E5_0255.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0255.s0 :: RH1E5_0255.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_031 : RS5.BandZeros RH1E5_0248.s0.t RH1E5_0255.sL.t 1016 := by
  have g248 := band_0248
  have g249 := RS5.BandZeros.glue (a := RH1E5_0248.s0.t) (b := RH1E5_0248.sL.t) (c := RH1E5_0249.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0248.s0, RH1E5_0247.sL, RH1E5_0248.sL]) (by norm_num [RS5.Sample.t, RH1E5_0248.sL, RH1E5_0249.sL]) g248 band_0249
  have g250 := RS5.BandZeros.glue (a := RH1E5_0248.s0.t) (b := RH1E5_0249.sL.t) (c := RH1E5_0250.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0248.s0, RH1E5_0247.sL, RH1E5_0249.sL]) (by norm_num [RS5.Sample.t, RH1E5_0249.sL, RH1E5_0250.sL]) g249 band_0250
  have g251 := RS5.BandZeros.glue (a := RH1E5_0248.s0.t) (b := RH1E5_0250.sL.t) (c := RH1E5_0251.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0248.s0, RH1E5_0247.sL, RH1E5_0250.sL]) (by norm_num [RS5.Sample.t, RH1E5_0250.sL, RH1E5_0251.sL]) g250 band_0251
  have g252 := RS5.BandZeros.glue (a := RH1E5_0248.s0.t) (b := RH1E5_0251.sL.t) (c := RH1E5_0252.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0248.s0, RH1E5_0247.sL, RH1E5_0251.sL]) (by norm_num [RS5.Sample.t, RH1E5_0251.sL, RH1E5_0252.sL]) g251 band_0252
  have g253 := RS5.BandZeros.glue (a := RH1E5_0248.s0.t) (b := RH1E5_0252.sL.t) (c := RH1E5_0253.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0248.s0, RH1E5_0247.sL, RH1E5_0252.sL]) (by norm_num [RS5.Sample.t, RH1E5_0252.sL, RH1E5_0253.sL]) g252 band_0253
  have g254 := RS5.BandZeros.glue (a := RH1E5_0248.s0.t) (b := RH1E5_0253.sL.t) (c := RH1E5_0254.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0248.s0, RH1E5_0247.sL, RH1E5_0253.sL]) (by norm_num [RS5.Sample.t, RH1E5_0253.sL, RH1E5_0254.sL]) g253 band_0254
  have g255 := RS5.BandZeros.glue (a := RH1E5_0248.s0.t) (b := RH1E5_0254.sL.t) (c := RH1E5_0255.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0248.s0, RH1E5_0247.sL, RH1E5_0254.sL]) (by norm_num [RS5.Sample.t, RH1E5_0254.sL, RH1E5_0255.sL]) g254 band_0255
  exact g255

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0248.s0.t RH1E5_0255.sL.t 1016 := by
  apply RH1E5.group_031 <;> assumption
