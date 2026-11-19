-- Prove2me | solution 1 for RH1E5.group_029
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:57:45.839106+00:00
-- url     : https://prove2.me/submissions/3cf4555e-d9f8-4a28-a5f6-3f8acb448de4

import Definitions.Def_RH1E5_Data029
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0232 : RS5.BandZeros RH1E5_0232.s0.t RH1E5_0232.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0232.s0 RH1E5_0232.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0232.s0 RH1E5_0232.rest = RH1E5_0232.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0232.s0 :: RH1E5_0232.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0233 : RS5.BandZeros RH1E5_0233.s0.t RH1E5_0233.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0233.s0 RH1E5_0233.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0233.s0 RH1E5_0233.rest = RH1E5_0233.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0233.s0 :: RH1E5_0233.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0234 : RS5.BandZeros RH1E5_0234.s0.t RH1E5_0234.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0234.s0 RH1E5_0234.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0234.s0 RH1E5_0234.rest = RH1E5_0234.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0234.s0 :: RH1E5_0234.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0235 : RS5.BandZeros RH1E5_0235.s0.t RH1E5_0235.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0235.s0 RH1E5_0235.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0235.s0 RH1E5_0235.rest = RH1E5_0235.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0235.s0 :: RH1E5_0235.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0236 : RS5.BandZeros RH1E5_0236.s0.t RH1E5_0236.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0236.s0 RH1E5_0236.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0236.s0 RH1E5_0236.rest = RH1E5_0236.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0236.s0 :: RH1E5_0236.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0237 : RS5.BandZeros RH1E5_0237.s0.t RH1E5_0237.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0237.s0 RH1E5_0237.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0237.s0 RH1E5_0237.rest = RH1E5_0237.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0237.s0 :: RH1E5_0237.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0238 : RS5.BandZeros RH1E5_0238.s0.t RH1E5_0238.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0238.s0 RH1E5_0238.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0238.s0 RH1E5_0238.rest = RH1E5_0238.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0238.s0 :: RH1E5_0238.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0239 : RS5.BandZeros RH1E5_0239.s0.t RH1E5_0239.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0239.s0 RH1E5_0239.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0239.s0 RH1E5_0239.rest = RH1E5_0239.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0239.s0 :: RH1E5_0239.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_029 : RS5.BandZeros RH1E5_0232.s0.t RH1E5_0239.sL.t 1016 := by
  have g232 := band_0232
  have g233 := RS5.BandZeros.glue (a := RH1E5_0232.s0.t) (b := RH1E5_0232.sL.t) (c := RH1E5_0233.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0232.s0, RH1E5_0231.sL, RH1E5_0232.sL]) (by norm_num [RS5.Sample.t, RH1E5_0232.sL, RH1E5_0233.sL]) g232 band_0233
  have g234 := RS5.BandZeros.glue (a := RH1E5_0232.s0.t) (b := RH1E5_0233.sL.t) (c := RH1E5_0234.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0232.s0, RH1E5_0231.sL, RH1E5_0233.sL]) (by norm_num [RS5.Sample.t, RH1E5_0233.sL, RH1E5_0234.sL]) g233 band_0234
  have g235 := RS5.BandZeros.glue (a := RH1E5_0232.s0.t) (b := RH1E5_0234.sL.t) (c := RH1E5_0235.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0232.s0, RH1E5_0231.sL, RH1E5_0234.sL]) (by norm_num [RS5.Sample.t, RH1E5_0234.sL, RH1E5_0235.sL]) g234 band_0235
  have g236 := RS5.BandZeros.glue (a := RH1E5_0232.s0.t) (b := RH1E5_0235.sL.t) (c := RH1E5_0236.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0232.s0, RH1E5_0231.sL, RH1E5_0235.sL]) (by norm_num [RS5.Sample.t, RH1E5_0235.sL, RH1E5_0236.sL]) g235 band_0236
  have g237 := RS5.BandZeros.glue (a := RH1E5_0232.s0.t) (b := RH1E5_0236.sL.t) (c := RH1E5_0237.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0232.s0, RH1E5_0231.sL, RH1E5_0236.sL]) (by norm_num [RS5.Sample.t, RH1E5_0236.sL, RH1E5_0237.sL]) g236 band_0237
  have g238 := RS5.BandZeros.glue (a := RH1E5_0232.s0.t) (b := RH1E5_0237.sL.t) (c := RH1E5_0238.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0232.s0, RH1E5_0231.sL, RH1E5_0237.sL]) (by norm_num [RS5.Sample.t, RH1E5_0237.sL, RH1E5_0238.sL]) g237 band_0238
  have g239 := RS5.BandZeros.glue (a := RH1E5_0232.s0.t) (b := RH1E5_0238.sL.t) (c := RH1E5_0239.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0232.s0, RH1E5_0231.sL, RH1E5_0238.sL]) (by norm_num [RS5.Sample.t, RH1E5_0238.sL, RH1E5_0239.sL]) g238 band_0239
  exact g239

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0232.s0.t RH1E5_0239.sL.t 1016 := by
  apply RH1E5.group_029 <;> assumption
