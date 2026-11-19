-- Prove2me | solution 1 for RH1E5.group_042
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:30:26.433868+00:00
-- url     : https://prove2.me/submissions/26b65a67-0799-41c9-a01d-17b8424ed054

import Definitions.Def_RH1E5_Data042
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0336 : RS5.BandZeros RH1E5_0336.s0.t RH1E5_0336.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0336.s0 RH1E5_0336.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0336.s0 RH1E5_0336.rest = RH1E5_0336.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0336.s0 :: RH1E5_0336.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0337 : RS5.BandZeros RH1E5_0337.s0.t RH1E5_0337.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0337.s0 RH1E5_0337.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0337.s0 RH1E5_0337.rest = RH1E5_0337.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0337.s0 :: RH1E5_0337.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0338 : RS5.BandZeros RH1E5_0338.s0.t RH1E5_0338.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0338.s0 RH1E5_0338.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0338.s0 RH1E5_0338.rest = RH1E5_0338.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0338.s0 :: RH1E5_0338.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0339 : RS5.BandZeros RH1E5_0339.s0.t RH1E5_0339.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0339.s0 RH1E5_0339.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0339.s0 RH1E5_0339.rest = RH1E5_0339.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0339.s0 :: RH1E5_0339.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0340 : RS5.BandZeros RH1E5_0340.s0.t RH1E5_0340.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0340.s0 RH1E5_0340.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0340.s0 RH1E5_0340.rest = RH1E5_0340.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0340.s0 :: RH1E5_0340.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0341 : RS5.BandZeros RH1E5_0341.s0.t RH1E5_0341.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0341.s0 RH1E5_0341.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0341.s0 RH1E5_0341.rest = RH1E5_0341.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0341.s0 :: RH1E5_0341.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0342 : RS5.BandZeros RH1E5_0342.s0.t RH1E5_0342.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0342.s0 RH1E5_0342.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0342.s0 RH1E5_0342.rest = RH1E5_0342.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0342.s0 :: RH1E5_0342.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0343 : RS5.BandZeros RH1E5_0343.s0.t RH1E5_0343.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0343.s0 RH1E5_0343.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0343.s0 RH1E5_0343.rest = RH1E5_0343.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0343.s0 :: RH1E5_0343.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_042 : RS5.BandZeros RH1E5_0336.s0.t RH1E5_0343.sL.t 1016 := by
  have g336 := band_0336
  have g337 := RS5.BandZeros.glue (a := RH1E5_0336.s0.t) (b := RH1E5_0336.sL.t) (c := RH1E5_0337.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0336.s0, RH1E5_0335.sL, RH1E5_0336.sL]) (by norm_num [RS5.Sample.t, RH1E5_0336.sL, RH1E5_0337.sL]) g336 band_0337
  have g338 := RS5.BandZeros.glue (a := RH1E5_0336.s0.t) (b := RH1E5_0337.sL.t) (c := RH1E5_0338.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0336.s0, RH1E5_0335.sL, RH1E5_0337.sL]) (by norm_num [RS5.Sample.t, RH1E5_0337.sL, RH1E5_0338.sL]) g337 band_0338
  have g339 := RS5.BandZeros.glue (a := RH1E5_0336.s0.t) (b := RH1E5_0338.sL.t) (c := RH1E5_0339.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0336.s0, RH1E5_0335.sL, RH1E5_0338.sL]) (by norm_num [RS5.Sample.t, RH1E5_0338.sL, RH1E5_0339.sL]) g338 band_0339
  have g340 := RS5.BandZeros.glue (a := RH1E5_0336.s0.t) (b := RH1E5_0339.sL.t) (c := RH1E5_0340.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0336.s0, RH1E5_0335.sL, RH1E5_0339.sL]) (by norm_num [RS5.Sample.t, RH1E5_0339.sL, RH1E5_0340.sL]) g339 band_0340
  have g341 := RS5.BandZeros.glue (a := RH1E5_0336.s0.t) (b := RH1E5_0340.sL.t) (c := RH1E5_0341.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0336.s0, RH1E5_0335.sL, RH1E5_0340.sL]) (by norm_num [RS5.Sample.t, RH1E5_0340.sL, RH1E5_0341.sL]) g340 band_0341
  have g342 := RS5.BandZeros.glue (a := RH1E5_0336.s0.t) (b := RH1E5_0341.sL.t) (c := RH1E5_0342.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0336.s0, RH1E5_0335.sL, RH1E5_0341.sL]) (by norm_num [RS5.Sample.t, RH1E5_0341.sL, RH1E5_0342.sL]) g341 band_0342
  have g343 := RS5.BandZeros.glue (a := RH1E5_0336.s0.t) (b := RH1E5_0342.sL.t) (c := RH1E5_0343.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0336.s0, RH1E5_0335.sL, RH1E5_0342.sL]) (by norm_num [RS5.Sample.t, RH1E5_0342.sL, RH1E5_0343.sL]) g342 band_0343
  exact g343

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0336.s0.t RH1E5_0343.sL.t 1016 := by
  apply RH1E5.group_042 <;> assumption
