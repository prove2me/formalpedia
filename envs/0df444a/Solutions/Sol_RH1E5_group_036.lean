-- Prove2me | solution 1 for RH1E5.group_036
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:12:39.906353+00:00
-- url     : https://prove2.me/submissions/6d947d53-2726-4f67-a02d-f651c5caeeea

import Definitions.Def_RH1E5_Data036
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0288 : RS5.BandZeros RH1E5_0288.s0.t RH1E5_0288.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0288.s0 RH1E5_0288.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0288.s0 RH1E5_0288.rest = RH1E5_0288.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0288.s0 :: RH1E5_0288.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0289 : RS5.BandZeros RH1E5_0289.s0.t RH1E5_0289.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0289.s0 RH1E5_0289.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0289.s0 RH1E5_0289.rest = RH1E5_0289.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0289.s0 :: RH1E5_0289.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0290 : RS5.BandZeros RH1E5_0290.s0.t RH1E5_0290.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0290.s0 RH1E5_0290.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0290.s0 RH1E5_0290.rest = RH1E5_0290.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0290.s0 :: RH1E5_0290.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0291 : RS5.BandZeros RH1E5_0291.s0.t RH1E5_0291.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0291.s0 RH1E5_0291.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0291.s0 RH1E5_0291.rest = RH1E5_0291.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0291.s0 :: RH1E5_0291.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0292 : RS5.BandZeros RH1E5_0292.s0.t RH1E5_0292.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0292.s0 RH1E5_0292.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0292.s0 RH1E5_0292.rest = RH1E5_0292.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0292.s0 :: RH1E5_0292.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0293 : RS5.BandZeros RH1E5_0293.s0.t RH1E5_0293.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0293.s0 RH1E5_0293.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0293.s0 RH1E5_0293.rest = RH1E5_0293.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0293.s0 :: RH1E5_0293.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0294 : RS5.BandZeros RH1E5_0294.s0.t RH1E5_0294.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0294.s0 RH1E5_0294.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0294.s0 RH1E5_0294.rest = RH1E5_0294.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0294.s0 :: RH1E5_0294.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0295 : RS5.BandZeros RH1E5_0295.s0.t RH1E5_0295.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0295.s0 RH1E5_0295.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0295.s0 RH1E5_0295.rest = RH1E5_0295.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0295.s0 :: RH1E5_0295.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_036 : RS5.BandZeros RH1E5_0288.s0.t RH1E5_0295.sL.t 1016 := by
  have g288 := band_0288
  have g289 := RS5.BandZeros.glue (a := RH1E5_0288.s0.t) (b := RH1E5_0288.sL.t) (c := RH1E5_0289.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0288.s0, RH1E5_0287.sL, RH1E5_0288.sL]) (by norm_num [RS5.Sample.t, RH1E5_0288.sL, RH1E5_0289.sL]) g288 band_0289
  have g290 := RS5.BandZeros.glue (a := RH1E5_0288.s0.t) (b := RH1E5_0289.sL.t) (c := RH1E5_0290.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0288.s0, RH1E5_0287.sL, RH1E5_0289.sL]) (by norm_num [RS5.Sample.t, RH1E5_0289.sL, RH1E5_0290.sL]) g289 band_0290
  have g291 := RS5.BandZeros.glue (a := RH1E5_0288.s0.t) (b := RH1E5_0290.sL.t) (c := RH1E5_0291.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0288.s0, RH1E5_0287.sL, RH1E5_0290.sL]) (by norm_num [RS5.Sample.t, RH1E5_0290.sL, RH1E5_0291.sL]) g290 band_0291
  have g292 := RS5.BandZeros.glue (a := RH1E5_0288.s0.t) (b := RH1E5_0291.sL.t) (c := RH1E5_0292.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0288.s0, RH1E5_0287.sL, RH1E5_0291.sL]) (by norm_num [RS5.Sample.t, RH1E5_0291.sL, RH1E5_0292.sL]) g291 band_0292
  have g293 := RS5.BandZeros.glue (a := RH1E5_0288.s0.t) (b := RH1E5_0292.sL.t) (c := RH1E5_0293.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0288.s0, RH1E5_0287.sL, RH1E5_0292.sL]) (by norm_num [RS5.Sample.t, RH1E5_0292.sL, RH1E5_0293.sL]) g292 band_0293
  have g294 := RS5.BandZeros.glue (a := RH1E5_0288.s0.t) (b := RH1E5_0293.sL.t) (c := RH1E5_0294.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0288.s0, RH1E5_0287.sL, RH1E5_0293.sL]) (by norm_num [RS5.Sample.t, RH1E5_0293.sL, RH1E5_0294.sL]) g293 band_0294
  have g295 := RS5.BandZeros.glue (a := RH1E5_0288.s0.t) (b := RH1E5_0294.sL.t) (c := RH1E5_0295.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0288.s0, RH1E5_0287.sL, RH1E5_0294.sL]) (by norm_num [RS5.Sample.t, RH1E5_0294.sL, RH1E5_0295.sL]) g294 band_0295
  exact g295

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0288.s0.t RH1E5_0295.sL.t 1016 := by
  apply RH1E5.group_036 <;> assumption
