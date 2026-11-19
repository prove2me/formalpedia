-- Prove2me | solution 1 for RH1E5.group_050
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:48:12.193149+00:00
-- url     : https://prove2.me/submissions/7d2c1558-08bc-4123-a0f9-28f89be948c0

import Definitions.Def_RH1E5_Data050
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0400 : RS5.BandZeros RH1E5_0400.s0.t RH1E5_0400.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0400.s0 RH1E5_0400.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0400.s0 RH1E5_0400.rest = RH1E5_0400.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0400.s0 :: RH1E5_0400.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0401 : RS5.BandZeros RH1E5_0401.s0.t RH1E5_0401.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0401.s0 RH1E5_0401.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0401.s0 RH1E5_0401.rest = RH1E5_0401.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0401.s0 :: RH1E5_0401.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0402 : RS5.BandZeros RH1E5_0402.s0.t RH1E5_0402.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0402.s0 RH1E5_0402.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0402.s0 RH1E5_0402.rest = RH1E5_0402.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0402.s0 :: RH1E5_0402.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0403 : RS5.BandZeros RH1E5_0403.s0.t RH1E5_0403.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0403.s0 RH1E5_0403.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0403.s0 RH1E5_0403.rest = RH1E5_0403.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0403.s0 :: RH1E5_0403.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0404 : RS5.BandZeros RH1E5_0404.s0.t RH1E5_0404.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0404.s0 RH1E5_0404.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0404.s0 RH1E5_0404.rest = RH1E5_0404.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0404.s0 :: RH1E5_0404.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0405 : RS5.BandZeros RH1E5_0405.s0.t RH1E5_0405.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0405.s0 RH1E5_0405.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0405.s0 RH1E5_0405.rest = RH1E5_0405.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0405.s0 :: RH1E5_0405.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0406 : RS5.BandZeros RH1E5_0406.s0.t RH1E5_0406.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0406.s0 RH1E5_0406.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0406.s0 RH1E5_0406.rest = RH1E5_0406.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0406.s0 :: RH1E5_0406.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0407 : RS5.BandZeros RH1E5_0407.s0.t RH1E5_0407.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0407.s0 RH1E5_0407.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0407.s0 RH1E5_0407.rest = RH1E5_0407.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0407.s0 :: RH1E5_0407.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_050 : RS5.BandZeros RH1E5_0400.s0.t RH1E5_0407.sL.t 1016 := by
  have g400 := band_0400
  have g401 := RS5.BandZeros.glue (a := RH1E5_0400.s0.t) (b := RH1E5_0400.sL.t) (c := RH1E5_0401.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0400.s0, RH1E5_0399.sL, RH1E5_0400.sL]) (by norm_num [RS5.Sample.t, RH1E5_0400.sL, RH1E5_0401.sL]) g400 band_0401
  have g402 := RS5.BandZeros.glue (a := RH1E5_0400.s0.t) (b := RH1E5_0401.sL.t) (c := RH1E5_0402.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0400.s0, RH1E5_0399.sL, RH1E5_0401.sL]) (by norm_num [RS5.Sample.t, RH1E5_0401.sL, RH1E5_0402.sL]) g401 band_0402
  have g403 := RS5.BandZeros.glue (a := RH1E5_0400.s0.t) (b := RH1E5_0402.sL.t) (c := RH1E5_0403.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0400.s0, RH1E5_0399.sL, RH1E5_0402.sL]) (by norm_num [RS5.Sample.t, RH1E5_0402.sL, RH1E5_0403.sL]) g402 band_0403
  have g404 := RS5.BandZeros.glue (a := RH1E5_0400.s0.t) (b := RH1E5_0403.sL.t) (c := RH1E5_0404.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0400.s0, RH1E5_0399.sL, RH1E5_0403.sL]) (by norm_num [RS5.Sample.t, RH1E5_0403.sL, RH1E5_0404.sL]) g403 band_0404
  have g405 := RS5.BandZeros.glue (a := RH1E5_0400.s0.t) (b := RH1E5_0404.sL.t) (c := RH1E5_0405.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0400.s0, RH1E5_0399.sL, RH1E5_0404.sL]) (by norm_num [RS5.Sample.t, RH1E5_0404.sL, RH1E5_0405.sL]) g404 band_0405
  have g406 := RS5.BandZeros.glue (a := RH1E5_0400.s0.t) (b := RH1E5_0405.sL.t) (c := RH1E5_0406.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0400.s0, RH1E5_0399.sL, RH1E5_0405.sL]) (by norm_num [RS5.Sample.t, RH1E5_0405.sL, RH1E5_0406.sL]) g405 band_0406
  have g407 := RS5.BandZeros.glue (a := RH1E5_0400.s0.t) (b := RH1E5_0406.sL.t) (c := RH1E5_0407.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0400.s0, RH1E5_0399.sL, RH1E5_0406.sL]) (by norm_num [RS5.Sample.t, RH1E5_0406.sL, RH1E5_0407.sL]) g406 band_0407
  exact g407

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0400.s0.t RH1E5_0407.sL.t 1016 := by
  apply RH1E5.group_050 <;> assumption
