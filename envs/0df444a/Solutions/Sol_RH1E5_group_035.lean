-- Prove2me | solution 1 for RH1E5.group_035
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:12:37.920742+00:00
-- url     : https://prove2.me/submissions/09243985-920c-4efe-83ef-150d426681ce

import Definitions.Def_RH1E5_Data035
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0280 : RS5.BandZeros RH1E5_0280.s0.t RH1E5_0280.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0280.s0 RH1E5_0280.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0280.s0 RH1E5_0280.rest = RH1E5_0280.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0280.s0 :: RH1E5_0280.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0281 : RS5.BandZeros RH1E5_0281.s0.t RH1E5_0281.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0281.s0 RH1E5_0281.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0281.s0 RH1E5_0281.rest = RH1E5_0281.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0281.s0 :: RH1E5_0281.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0282 : RS5.BandZeros RH1E5_0282.s0.t RH1E5_0282.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0282.s0 RH1E5_0282.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0282.s0 RH1E5_0282.rest = RH1E5_0282.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0282.s0 :: RH1E5_0282.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0283 : RS5.BandZeros RH1E5_0283.s0.t RH1E5_0283.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0283.s0 RH1E5_0283.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0283.s0 RH1E5_0283.rest = RH1E5_0283.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0283.s0 :: RH1E5_0283.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0284 : RS5.BandZeros RH1E5_0284.s0.t RH1E5_0284.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0284.s0 RH1E5_0284.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0284.s0 RH1E5_0284.rest = RH1E5_0284.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0284.s0 :: RH1E5_0284.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0285 : RS5.BandZeros RH1E5_0285.s0.t RH1E5_0285.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0285.s0 RH1E5_0285.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0285.s0 RH1E5_0285.rest = RH1E5_0285.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0285.s0 :: RH1E5_0285.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0286 : RS5.BandZeros RH1E5_0286.s0.t RH1E5_0286.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0286.s0 RH1E5_0286.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0286.s0 RH1E5_0286.rest = RH1E5_0286.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0286.s0 :: RH1E5_0286.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0287 : RS5.BandZeros RH1E5_0287.s0.t RH1E5_0287.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0287.s0 RH1E5_0287.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0287.s0 RH1E5_0287.rest = RH1E5_0287.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0287.s0 :: RH1E5_0287.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_035 : RS5.BandZeros RH1E5_0280.s0.t RH1E5_0287.sL.t 1016 := by
  have g280 := band_0280
  have g281 := RS5.BandZeros.glue (a := RH1E5_0280.s0.t) (b := RH1E5_0280.sL.t) (c := RH1E5_0281.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0280.s0, RH1E5_0279.sL, RH1E5_0280.sL]) (by norm_num [RS5.Sample.t, RH1E5_0280.sL, RH1E5_0281.sL]) g280 band_0281
  have g282 := RS5.BandZeros.glue (a := RH1E5_0280.s0.t) (b := RH1E5_0281.sL.t) (c := RH1E5_0282.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0280.s0, RH1E5_0279.sL, RH1E5_0281.sL]) (by norm_num [RS5.Sample.t, RH1E5_0281.sL, RH1E5_0282.sL]) g281 band_0282
  have g283 := RS5.BandZeros.glue (a := RH1E5_0280.s0.t) (b := RH1E5_0282.sL.t) (c := RH1E5_0283.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0280.s0, RH1E5_0279.sL, RH1E5_0282.sL]) (by norm_num [RS5.Sample.t, RH1E5_0282.sL, RH1E5_0283.sL]) g282 band_0283
  have g284 := RS5.BandZeros.glue (a := RH1E5_0280.s0.t) (b := RH1E5_0283.sL.t) (c := RH1E5_0284.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0280.s0, RH1E5_0279.sL, RH1E5_0283.sL]) (by norm_num [RS5.Sample.t, RH1E5_0283.sL, RH1E5_0284.sL]) g283 band_0284
  have g285 := RS5.BandZeros.glue (a := RH1E5_0280.s0.t) (b := RH1E5_0284.sL.t) (c := RH1E5_0285.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0280.s0, RH1E5_0279.sL, RH1E5_0284.sL]) (by norm_num [RS5.Sample.t, RH1E5_0284.sL, RH1E5_0285.sL]) g284 band_0285
  have g286 := RS5.BandZeros.glue (a := RH1E5_0280.s0.t) (b := RH1E5_0285.sL.t) (c := RH1E5_0286.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0280.s0, RH1E5_0279.sL, RH1E5_0285.sL]) (by norm_num [RS5.Sample.t, RH1E5_0285.sL, RH1E5_0286.sL]) g285 band_0286
  have g287 := RS5.BandZeros.glue (a := RH1E5_0280.s0.t) (b := RH1E5_0286.sL.t) (c := RH1E5_0287.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0280.s0, RH1E5_0279.sL, RH1E5_0286.sL]) (by norm_num [RS5.Sample.t, RH1E5_0286.sL, RH1E5_0287.sL]) g286 band_0287
  exact g287

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0280.s0.t RH1E5_0287.sL.t 1016 := by
  apply RH1E5.group_035 <;> assumption
