-- Prove2me | solution 1 for RH1E5.group_049
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:45:40.333952+00:00
-- url     : https://prove2.me/submissions/ad685c65-133a-4745-8836-a4c7c570e263

import Definitions.Def_RH1E5_Data049
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0392 : RS5.BandZeros RH1E5_0392.s0.t RH1E5_0392.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0392.s0 RH1E5_0392.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0392.s0 RH1E5_0392.rest = RH1E5_0392.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0392.s0 :: RH1E5_0392.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0393 : RS5.BandZeros RH1E5_0393.s0.t RH1E5_0393.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0393.s0 RH1E5_0393.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0393.s0 RH1E5_0393.rest = RH1E5_0393.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0393.s0 :: RH1E5_0393.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0394 : RS5.BandZeros RH1E5_0394.s0.t RH1E5_0394.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0394.s0 RH1E5_0394.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0394.s0 RH1E5_0394.rest = RH1E5_0394.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0394.s0 :: RH1E5_0394.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0395 : RS5.BandZeros RH1E5_0395.s0.t RH1E5_0395.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0395.s0 RH1E5_0395.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0395.s0 RH1E5_0395.rest = RH1E5_0395.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0395.s0 :: RH1E5_0395.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0396 : RS5.BandZeros RH1E5_0396.s0.t RH1E5_0396.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0396.s0 RH1E5_0396.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0396.s0 RH1E5_0396.rest = RH1E5_0396.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0396.s0 :: RH1E5_0396.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0397 : RS5.BandZeros RH1E5_0397.s0.t RH1E5_0397.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0397.s0 RH1E5_0397.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0397.s0 RH1E5_0397.rest = RH1E5_0397.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0397.s0 :: RH1E5_0397.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0398 : RS5.BandZeros RH1E5_0398.s0.t RH1E5_0398.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0398.s0 RH1E5_0398.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0398.s0 RH1E5_0398.rest = RH1E5_0398.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0398.s0 :: RH1E5_0398.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0399 : RS5.BandZeros RH1E5_0399.s0.t RH1E5_0399.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0399.s0 RH1E5_0399.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0399.s0 RH1E5_0399.rest = RH1E5_0399.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0399.s0 :: RH1E5_0399.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_049 : RS5.BandZeros RH1E5_0392.s0.t RH1E5_0399.sL.t 1016 := by
  have g392 := band_0392
  have g393 := RS5.BandZeros.glue (a := RH1E5_0392.s0.t) (b := RH1E5_0392.sL.t) (c := RH1E5_0393.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0392.s0, RH1E5_0391.sL, RH1E5_0392.sL]) (by norm_num [RS5.Sample.t, RH1E5_0392.sL, RH1E5_0393.sL]) g392 band_0393
  have g394 := RS5.BandZeros.glue (a := RH1E5_0392.s0.t) (b := RH1E5_0393.sL.t) (c := RH1E5_0394.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0392.s0, RH1E5_0391.sL, RH1E5_0393.sL]) (by norm_num [RS5.Sample.t, RH1E5_0393.sL, RH1E5_0394.sL]) g393 band_0394
  have g395 := RS5.BandZeros.glue (a := RH1E5_0392.s0.t) (b := RH1E5_0394.sL.t) (c := RH1E5_0395.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0392.s0, RH1E5_0391.sL, RH1E5_0394.sL]) (by norm_num [RS5.Sample.t, RH1E5_0394.sL, RH1E5_0395.sL]) g394 band_0395
  have g396 := RS5.BandZeros.glue (a := RH1E5_0392.s0.t) (b := RH1E5_0395.sL.t) (c := RH1E5_0396.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0392.s0, RH1E5_0391.sL, RH1E5_0395.sL]) (by norm_num [RS5.Sample.t, RH1E5_0395.sL, RH1E5_0396.sL]) g395 band_0396
  have g397 := RS5.BandZeros.glue (a := RH1E5_0392.s0.t) (b := RH1E5_0396.sL.t) (c := RH1E5_0397.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0392.s0, RH1E5_0391.sL, RH1E5_0396.sL]) (by norm_num [RS5.Sample.t, RH1E5_0396.sL, RH1E5_0397.sL]) g396 band_0397
  have g398 := RS5.BandZeros.glue (a := RH1E5_0392.s0.t) (b := RH1E5_0397.sL.t) (c := RH1E5_0398.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0392.s0, RH1E5_0391.sL, RH1E5_0397.sL]) (by norm_num [RS5.Sample.t, RH1E5_0397.sL, RH1E5_0398.sL]) g397 band_0398
  have g399 := RS5.BandZeros.glue (a := RH1E5_0392.s0.t) (b := RH1E5_0398.sL.t) (c := RH1E5_0399.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0392.s0, RH1E5_0391.sL, RH1E5_0398.sL]) (by norm_num [RS5.Sample.t, RH1E5_0398.sL, RH1E5_0399.sL]) g398 band_0399
  exact g399

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0392.s0.t RH1E5_0399.sL.t 1016 := by
  apply RH1E5.group_049 <;> assumption
