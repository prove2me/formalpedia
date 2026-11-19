-- Prove2me | solution 1 for RH1E5.group_033
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:07:38.701848+00:00
-- url     : https://prove2.me/submissions/f7918cce-60ec-4006-aceb-4d5d7db6804a

import Definitions.Def_RH1E5_Data033
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0264 : RS5.BandZeros RH1E5_0264.s0.t RH1E5_0264.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0264.s0 RH1E5_0264.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0264.s0 RH1E5_0264.rest = RH1E5_0264.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0264.s0 :: RH1E5_0264.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0265 : RS5.BandZeros RH1E5_0265.s0.t RH1E5_0265.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0265.s0 RH1E5_0265.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0265.s0 RH1E5_0265.rest = RH1E5_0265.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0265.s0 :: RH1E5_0265.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0266 : RS5.BandZeros RH1E5_0266.s0.t RH1E5_0266.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0266.s0 RH1E5_0266.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0266.s0 RH1E5_0266.rest = RH1E5_0266.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0266.s0 :: RH1E5_0266.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0267 : RS5.BandZeros RH1E5_0267.s0.t RH1E5_0267.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0267.s0 RH1E5_0267.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0267.s0 RH1E5_0267.rest = RH1E5_0267.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0267.s0 :: RH1E5_0267.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0268 : RS5.BandZeros RH1E5_0268.s0.t RH1E5_0268.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0268.s0 RH1E5_0268.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0268.s0 RH1E5_0268.rest = RH1E5_0268.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0268.s0 :: RH1E5_0268.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0269 : RS5.BandZeros RH1E5_0269.s0.t RH1E5_0269.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0269.s0 RH1E5_0269.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0269.s0 RH1E5_0269.rest = RH1E5_0269.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0269.s0 :: RH1E5_0269.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0270 : RS5.BandZeros RH1E5_0270.s0.t RH1E5_0270.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0270.s0 RH1E5_0270.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0270.s0 RH1E5_0270.rest = RH1E5_0270.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0270.s0 :: RH1E5_0270.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0271 : RS5.BandZeros RH1E5_0271.s0.t RH1E5_0271.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0271.s0 RH1E5_0271.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0271.s0 RH1E5_0271.rest = RH1E5_0271.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0271.s0 :: RH1E5_0271.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_033 : RS5.BandZeros RH1E5_0264.s0.t RH1E5_0271.sL.t 1016 := by
  have g264 := band_0264
  have g265 := RS5.BandZeros.glue (a := RH1E5_0264.s0.t) (b := RH1E5_0264.sL.t) (c := RH1E5_0265.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0264.s0, RH1E5_0263.sL, RH1E5_0264.sL]) (by norm_num [RS5.Sample.t, RH1E5_0264.sL, RH1E5_0265.sL]) g264 band_0265
  have g266 := RS5.BandZeros.glue (a := RH1E5_0264.s0.t) (b := RH1E5_0265.sL.t) (c := RH1E5_0266.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0264.s0, RH1E5_0263.sL, RH1E5_0265.sL]) (by norm_num [RS5.Sample.t, RH1E5_0265.sL, RH1E5_0266.sL]) g265 band_0266
  have g267 := RS5.BandZeros.glue (a := RH1E5_0264.s0.t) (b := RH1E5_0266.sL.t) (c := RH1E5_0267.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0264.s0, RH1E5_0263.sL, RH1E5_0266.sL]) (by norm_num [RS5.Sample.t, RH1E5_0266.sL, RH1E5_0267.sL]) g266 band_0267
  have g268 := RS5.BandZeros.glue (a := RH1E5_0264.s0.t) (b := RH1E5_0267.sL.t) (c := RH1E5_0268.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0264.s0, RH1E5_0263.sL, RH1E5_0267.sL]) (by norm_num [RS5.Sample.t, RH1E5_0267.sL, RH1E5_0268.sL]) g267 band_0268
  have g269 := RS5.BandZeros.glue (a := RH1E5_0264.s0.t) (b := RH1E5_0268.sL.t) (c := RH1E5_0269.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0264.s0, RH1E5_0263.sL, RH1E5_0268.sL]) (by norm_num [RS5.Sample.t, RH1E5_0268.sL, RH1E5_0269.sL]) g268 band_0269
  have g270 := RS5.BandZeros.glue (a := RH1E5_0264.s0.t) (b := RH1E5_0269.sL.t) (c := RH1E5_0270.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0264.s0, RH1E5_0263.sL, RH1E5_0269.sL]) (by norm_num [RS5.Sample.t, RH1E5_0269.sL, RH1E5_0270.sL]) g269 band_0270
  have g271 := RS5.BandZeros.glue (a := RH1E5_0264.s0.t) (b := RH1E5_0270.sL.t) (c := RH1E5_0271.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0264.s0, RH1E5_0263.sL, RH1E5_0270.sL]) (by norm_num [RS5.Sample.t, RH1E5_0270.sL, RH1E5_0271.sL]) g270 band_0271
  exact g271

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0264.s0.t RH1E5_0271.sL.t 1016 := by
  apply RH1E5.group_033 <;> assumption
