-- Prove2me | solution 1 for RH1E5.group_043
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:29:07.294137+00:00
-- url     : https://prove2.me/submissions/958c5b2d-c2ea-48de-96d8-3be103768613

import Definitions.Def_RH1E5_Data043
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0344 : RS5.BandZeros RH1E5_0344.s0.t RH1E5_0344.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0344.s0 RH1E5_0344.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0344.s0 RH1E5_0344.rest = RH1E5_0344.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0344.s0 :: RH1E5_0344.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0345 : RS5.BandZeros RH1E5_0345.s0.t RH1E5_0345.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0345.s0 RH1E5_0345.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0345.s0 RH1E5_0345.rest = RH1E5_0345.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0345.s0 :: RH1E5_0345.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0346 : RS5.BandZeros RH1E5_0346.s0.t RH1E5_0346.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0346.s0 RH1E5_0346.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0346.s0 RH1E5_0346.rest = RH1E5_0346.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0346.s0 :: RH1E5_0346.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0347 : RS5.BandZeros RH1E5_0347.s0.t RH1E5_0347.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0347.s0 RH1E5_0347.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0347.s0 RH1E5_0347.rest = RH1E5_0347.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0347.s0 :: RH1E5_0347.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0348 : RS5.BandZeros RH1E5_0348.s0.t RH1E5_0348.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0348.s0 RH1E5_0348.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0348.s0 RH1E5_0348.rest = RH1E5_0348.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0348.s0 :: RH1E5_0348.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0349 : RS5.BandZeros RH1E5_0349.s0.t RH1E5_0349.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0349.s0 RH1E5_0349.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0349.s0 RH1E5_0349.rest = RH1E5_0349.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0349.s0 :: RH1E5_0349.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0350 : RS5.BandZeros RH1E5_0350.s0.t RH1E5_0350.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0350.s0 RH1E5_0350.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0350.s0 RH1E5_0350.rest = RH1E5_0350.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0350.s0 :: RH1E5_0350.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0351 : RS5.BandZeros RH1E5_0351.s0.t RH1E5_0351.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0351.s0 RH1E5_0351.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0351.s0 RH1E5_0351.rest = RH1E5_0351.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0351.s0 :: RH1E5_0351.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_043 : RS5.BandZeros RH1E5_0344.s0.t RH1E5_0351.sL.t 1016 := by
  have g344 := band_0344
  have g345 := RS5.BandZeros.glue (a := RH1E5_0344.s0.t) (b := RH1E5_0344.sL.t) (c := RH1E5_0345.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0344.s0, RH1E5_0343.sL, RH1E5_0344.sL]) (by norm_num [RS5.Sample.t, RH1E5_0344.sL, RH1E5_0345.sL]) g344 band_0345
  have g346 := RS5.BandZeros.glue (a := RH1E5_0344.s0.t) (b := RH1E5_0345.sL.t) (c := RH1E5_0346.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0344.s0, RH1E5_0343.sL, RH1E5_0345.sL]) (by norm_num [RS5.Sample.t, RH1E5_0345.sL, RH1E5_0346.sL]) g345 band_0346
  have g347 := RS5.BandZeros.glue (a := RH1E5_0344.s0.t) (b := RH1E5_0346.sL.t) (c := RH1E5_0347.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0344.s0, RH1E5_0343.sL, RH1E5_0346.sL]) (by norm_num [RS5.Sample.t, RH1E5_0346.sL, RH1E5_0347.sL]) g346 band_0347
  have g348 := RS5.BandZeros.glue (a := RH1E5_0344.s0.t) (b := RH1E5_0347.sL.t) (c := RH1E5_0348.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0344.s0, RH1E5_0343.sL, RH1E5_0347.sL]) (by norm_num [RS5.Sample.t, RH1E5_0347.sL, RH1E5_0348.sL]) g347 band_0348
  have g349 := RS5.BandZeros.glue (a := RH1E5_0344.s0.t) (b := RH1E5_0348.sL.t) (c := RH1E5_0349.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0344.s0, RH1E5_0343.sL, RH1E5_0348.sL]) (by norm_num [RS5.Sample.t, RH1E5_0348.sL, RH1E5_0349.sL]) g348 band_0349
  have g350 := RS5.BandZeros.glue (a := RH1E5_0344.s0.t) (b := RH1E5_0349.sL.t) (c := RH1E5_0350.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0344.s0, RH1E5_0343.sL, RH1E5_0349.sL]) (by norm_num [RS5.Sample.t, RH1E5_0349.sL, RH1E5_0350.sL]) g349 band_0350
  have g351 := RS5.BandZeros.glue (a := RH1E5_0344.s0.t) (b := RH1E5_0350.sL.t) (c := RH1E5_0351.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0344.s0, RH1E5_0343.sL, RH1E5_0350.sL]) (by norm_num [RS5.Sample.t, RH1E5_0350.sL, RH1E5_0351.sL]) g350 band_0351
  exact g351

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0344.s0.t RH1E5_0351.sL.t 1016 := by
  apply RH1E5.group_043 <;> assumption
