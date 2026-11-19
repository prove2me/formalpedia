-- Prove2me | solution 1 for RH1E5.group_044
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:31:41.444216+00:00
-- url     : https://prove2.me/submissions/74419cc2-5d8d-4dc4-907a-7b7e883ca222

import Definitions.Def_RH1E5_Data044
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0352 : RS5.BandZeros RH1E5_0352.s0.t RH1E5_0352.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0352.s0 RH1E5_0352.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0352.s0 RH1E5_0352.rest = RH1E5_0352.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0352.s0 :: RH1E5_0352.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0353 : RS5.BandZeros RH1E5_0353.s0.t RH1E5_0353.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0353.s0 RH1E5_0353.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0353.s0 RH1E5_0353.rest = RH1E5_0353.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0353.s0 :: RH1E5_0353.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0354 : RS5.BandZeros RH1E5_0354.s0.t RH1E5_0354.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0354.s0 RH1E5_0354.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0354.s0 RH1E5_0354.rest = RH1E5_0354.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0354.s0 :: RH1E5_0354.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0355 : RS5.BandZeros RH1E5_0355.s0.t RH1E5_0355.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0355.s0 RH1E5_0355.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0355.s0 RH1E5_0355.rest = RH1E5_0355.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0355.s0 :: RH1E5_0355.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0356 : RS5.BandZeros RH1E5_0356.s0.t RH1E5_0356.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0356.s0 RH1E5_0356.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0356.s0 RH1E5_0356.rest = RH1E5_0356.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0356.s0 :: RH1E5_0356.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0357 : RS5.BandZeros RH1E5_0357.s0.t RH1E5_0357.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0357.s0 RH1E5_0357.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0357.s0 RH1E5_0357.rest = RH1E5_0357.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0357.s0 :: RH1E5_0357.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0358 : RS5.BandZeros RH1E5_0358.s0.t RH1E5_0358.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0358.s0 RH1E5_0358.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0358.s0 RH1E5_0358.rest = RH1E5_0358.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0358.s0 :: RH1E5_0358.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0359 : RS5.BandZeros RH1E5_0359.s0.t RH1E5_0359.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0359.s0 RH1E5_0359.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0359.s0 RH1E5_0359.rest = RH1E5_0359.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0359.s0 :: RH1E5_0359.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_044 : RS5.BandZeros RH1E5_0352.s0.t RH1E5_0359.sL.t 1016 := by
  have g352 := band_0352
  have g353 := RS5.BandZeros.glue (a := RH1E5_0352.s0.t) (b := RH1E5_0352.sL.t) (c := RH1E5_0353.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0352.s0, RH1E5_0351.sL, RH1E5_0352.sL]) (by norm_num [RS5.Sample.t, RH1E5_0352.sL, RH1E5_0353.sL]) g352 band_0353
  have g354 := RS5.BandZeros.glue (a := RH1E5_0352.s0.t) (b := RH1E5_0353.sL.t) (c := RH1E5_0354.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0352.s0, RH1E5_0351.sL, RH1E5_0353.sL]) (by norm_num [RS5.Sample.t, RH1E5_0353.sL, RH1E5_0354.sL]) g353 band_0354
  have g355 := RS5.BandZeros.glue (a := RH1E5_0352.s0.t) (b := RH1E5_0354.sL.t) (c := RH1E5_0355.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0352.s0, RH1E5_0351.sL, RH1E5_0354.sL]) (by norm_num [RS5.Sample.t, RH1E5_0354.sL, RH1E5_0355.sL]) g354 band_0355
  have g356 := RS5.BandZeros.glue (a := RH1E5_0352.s0.t) (b := RH1E5_0355.sL.t) (c := RH1E5_0356.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0352.s0, RH1E5_0351.sL, RH1E5_0355.sL]) (by norm_num [RS5.Sample.t, RH1E5_0355.sL, RH1E5_0356.sL]) g355 band_0356
  have g357 := RS5.BandZeros.glue (a := RH1E5_0352.s0.t) (b := RH1E5_0356.sL.t) (c := RH1E5_0357.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0352.s0, RH1E5_0351.sL, RH1E5_0356.sL]) (by norm_num [RS5.Sample.t, RH1E5_0356.sL, RH1E5_0357.sL]) g356 band_0357
  have g358 := RS5.BandZeros.glue (a := RH1E5_0352.s0.t) (b := RH1E5_0357.sL.t) (c := RH1E5_0358.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0352.s0, RH1E5_0351.sL, RH1E5_0357.sL]) (by norm_num [RS5.Sample.t, RH1E5_0357.sL, RH1E5_0358.sL]) g357 band_0358
  have g359 := RS5.BandZeros.glue (a := RH1E5_0352.s0.t) (b := RH1E5_0358.sL.t) (c := RH1E5_0359.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0352.s0, RH1E5_0351.sL, RH1E5_0358.sL]) (by norm_num [RS5.Sample.t, RH1E5_0358.sL, RH1E5_0359.sL]) g358 band_0359
  exact g359

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0352.s0.t RH1E5_0359.sL.t 1016 := by
  apply RH1E5.group_044 <;> assumption
