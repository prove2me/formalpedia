-- Prove2me | solution 1 for RH1E5.group_026
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:47:52.929236+00:00
-- url     : https://prove2.me/submissions/87409763-96ab-4502-85e5-25bad627b68d

import Definitions.Def_RH1E5_Data026
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0208 : RS5.BandZeros RH1E5_0208.s0.t RH1E5_0208.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0208.s0 RH1E5_0208.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0208.s0 RH1E5_0208.rest = RH1E5_0208.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0208.s0 :: RH1E5_0208.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0209 : RS5.BandZeros RH1E5_0209.s0.t RH1E5_0209.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0209.s0 RH1E5_0209.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0209.s0 RH1E5_0209.rest = RH1E5_0209.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0209.s0 :: RH1E5_0209.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0210 : RS5.BandZeros RH1E5_0210.s0.t RH1E5_0210.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0210.s0 RH1E5_0210.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0210.s0 RH1E5_0210.rest = RH1E5_0210.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0210.s0 :: RH1E5_0210.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0211 : RS5.BandZeros RH1E5_0211.s0.t RH1E5_0211.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0211.s0 RH1E5_0211.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0211.s0 RH1E5_0211.rest = RH1E5_0211.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0211.s0 :: RH1E5_0211.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0212 : RS5.BandZeros RH1E5_0212.s0.t RH1E5_0212.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0212.s0 RH1E5_0212.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0212.s0 RH1E5_0212.rest = RH1E5_0212.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0212.s0 :: RH1E5_0212.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0213 : RS5.BandZeros RH1E5_0213.s0.t RH1E5_0213.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0213.s0 RH1E5_0213.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0213.s0 RH1E5_0213.rest = RH1E5_0213.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0213.s0 :: RH1E5_0213.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0214 : RS5.BandZeros RH1E5_0214.s0.t RH1E5_0214.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0214.s0 RH1E5_0214.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0214.s0 RH1E5_0214.rest = RH1E5_0214.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0214.s0 :: RH1E5_0214.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0215 : RS5.BandZeros RH1E5_0215.s0.t RH1E5_0215.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0215.s0 RH1E5_0215.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0215.s0 RH1E5_0215.rest = RH1E5_0215.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0215.s0 :: RH1E5_0215.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_026 : RS5.BandZeros RH1E5_0208.s0.t RH1E5_0215.sL.t 1016 := by
  have g208 := band_0208
  have g209 := RS5.BandZeros.glue (a := RH1E5_0208.s0.t) (b := RH1E5_0208.sL.t) (c := RH1E5_0209.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0208.s0, RH1E5_0207.sL, RH1E5_0208.sL]) (by norm_num [RS5.Sample.t, RH1E5_0208.sL, RH1E5_0209.sL]) g208 band_0209
  have g210 := RS5.BandZeros.glue (a := RH1E5_0208.s0.t) (b := RH1E5_0209.sL.t) (c := RH1E5_0210.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0208.s0, RH1E5_0207.sL, RH1E5_0209.sL]) (by norm_num [RS5.Sample.t, RH1E5_0209.sL, RH1E5_0210.sL]) g209 band_0210
  have g211 := RS5.BandZeros.glue (a := RH1E5_0208.s0.t) (b := RH1E5_0210.sL.t) (c := RH1E5_0211.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0208.s0, RH1E5_0207.sL, RH1E5_0210.sL]) (by norm_num [RS5.Sample.t, RH1E5_0210.sL, RH1E5_0211.sL]) g210 band_0211
  have g212 := RS5.BandZeros.glue (a := RH1E5_0208.s0.t) (b := RH1E5_0211.sL.t) (c := RH1E5_0212.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0208.s0, RH1E5_0207.sL, RH1E5_0211.sL]) (by norm_num [RS5.Sample.t, RH1E5_0211.sL, RH1E5_0212.sL]) g211 band_0212
  have g213 := RS5.BandZeros.glue (a := RH1E5_0208.s0.t) (b := RH1E5_0212.sL.t) (c := RH1E5_0213.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0208.s0, RH1E5_0207.sL, RH1E5_0212.sL]) (by norm_num [RS5.Sample.t, RH1E5_0212.sL, RH1E5_0213.sL]) g212 band_0213
  have g214 := RS5.BandZeros.glue (a := RH1E5_0208.s0.t) (b := RH1E5_0213.sL.t) (c := RH1E5_0214.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0208.s0, RH1E5_0207.sL, RH1E5_0213.sL]) (by norm_num [RS5.Sample.t, RH1E5_0213.sL, RH1E5_0214.sL]) g213 band_0214
  have g215 := RS5.BandZeros.glue (a := RH1E5_0208.s0.t) (b := RH1E5_0214.sL.t) (c := RH1E5_0215.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0208.s0, RH1E5_0207.sL, RH1E5_0214.sL]) (by norm_num [RS5.Sample.t, RH1E5_0214.sL, RH1E5_0215.sL]) g214 band_0215
  exact g215

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0208.s0.t RH1E5_0215.sL.t 1016 := by
  apply RH1E5.group_026 <;> assumption
