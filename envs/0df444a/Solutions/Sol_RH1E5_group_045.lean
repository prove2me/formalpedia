-- Prove2me | solution 1 for RH1E5.group_045
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:35:33.795882+00:00
-- url     : https://prove2.me/submissions/96146f09-0ce1-4d72-85d8-badff8b6ef0d

import Definitions.Def_RH1E5_Data045
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0360 : RS5.BandZeros RH1E5_0360.s0.t RH1E5_0360.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0360.s0 RH1E5_0360.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0360.s0 RH1E5_0360.rest = RH1E5_0360.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0360.s0 :: RH1E5_0360.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0361 : RS5.BandZeros RH1E5_0361.s0.t RH1E5_0361.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0361.s0 RH1E5_0361.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0361.s0 RH1E5_0361.rest = RH1E5_0361.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0361.s0 :: RH1E5_0361.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0362 : RS5.BandZeros RH1E5_0362.s0.t RH1E5_0362.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0362.s0 RH1E5_0362.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0362.s0 RH1E5_0362.rest = RH1E5_0362.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0362.s0 :: RH1E5_0362.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0363 : RS5.BandZeros RH1E5_0363.s0.t RH1E5_0363.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0363.s0 RH1E5_0363.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0363.s0 RH1E5_0363.rest = RH1E5_0363.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0363.s0 :: RH1E5_0363.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0364 : RS5.BandZeros RH1E5_0364.s0.t RH1E5_0364.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0364.s0 RH1E5_0364.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0364.s0 RH1E5_0364.rest = RH1E5_0364.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0364.s0 :: RH1E5_0364.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0365 : RS5.BandZeros RH1E5_0365.s0.t RH1E5_0365.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0365.s0 RH1E5_0365.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0365.s0 RH1E5_0365.rest = RH1E5_0365.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0365.s0 :: RH1E5_0365.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0366 : RS5.BandZeros RH1E5_0366.s0.t RH1E5_0366.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0366.s0 RH1E5_0366.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0366.s0 RH1E5_0366.rest = RH1E5_0366.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0366.s0 :: RH1E5_0366.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0367 : RS5.BandZeros RH1E5_0367.s0.t RH1E5_0367.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0367.s0 RH1E5_0367.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0367.s0 RH1E5_0367.rest = RH1E5_0367.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0367.s0 :: RH1E5_0367.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_045 : RS5.BandZeros RH1E5_0360.s0.t RH1E5_0367.sL.t 1016 := by
  have g360 := band_0360
  have g361 := RS5.BandZeros.glue (a := RH1E5_0360.s0.t) (b := RH1E5_0360.sL.t) (c := RH1E5_0361.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0360.s0, RH1E5_0359.sL, RH1E5_0360.sL]) (by norm_num [RS5.Sample.t, RH1E5_0360.sL, RH1E5_0361.sL]) g360 band_0361
  have g362 := RS5.BandZeros.glue (a := RH1E5_0360.s0.t) (b := RH1E5_0361.sL.t) (c := RH1E5_0362.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0360.s0, RH1E5_0359.sL, RH1E5_0361.sL]) (by norm_num [RS5.Sample.t, RH1E5_0361.sL, RH1E5_0362.sL]) g361 band_0362
  have g363 := RS5.BandZeros.glue (a := RH1E5_0360.s0.t) (b := RH1E5_0362.sL.t) (c := RH1E5_0363.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0360.s0, RH1E5_0359.sL, RH1E5_0362.sL]) (by norm_num [RS5.Sample.t, RH1E5_0362.sL, RH1E5_0363.sL]) g362 band_0363
  have g364 := RS5.BandZeros.glue (a := RH1E5_0360.s0.t) (b := RH1E5_0363.sL.t) (c := RH1E5_0364.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0360.s0, RH1E5_0359.sL, RH1E5_0363.sL]) (by norm_num [RS5.Sample.t, RH1E5_0363.sL, RH1E5_0364.sL]) g363 band_0364
  have g365 := RS5.BandZeros.glue (a := RH1E5_0360.s0.t) (b := RH1E5_0364.sL.t) (c := RH1E5_0365.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0360.s0, RH1E5_0359.sL, RH1E5_0364.sL]) (by norm_num [RS5.Sample.t, RH1E5_0364.sL, RH1E5_0365.sL]) g364 band_0365
  have g366 := RS5.BandZeros.glue (a := RH1E5_0360.s0.t) (b := RH1E5_0365.sL.t) (c := RH1E5_0366.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0360.s0, RH1E5_0359.sL, RH1E5_0365.sL]) (by norm_num [RS5.Sample.t, RH1E5_0365.sL, RH1E5_0366.sL]) g365 band_0366
  have g367 := RS5.BandZeros.glue (a := RH1E5_0360.s0.t) (b := RH1E5_0366.sL.t) (c := RH1E5_0367.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0360.s0, RH1E5_0359.sL, RH1E5_0366.sL]) (by norm_num [RS5.Sample.t, RH1E5_0366.sL, RH1E5_0367.sL]) g366 band_0367
  exact g367

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0360.s0.t RH1E5_0367.sL.t 1016 := by
  apply RH1E5.group_045 <;> assumption
