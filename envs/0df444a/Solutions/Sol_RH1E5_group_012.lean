-- Prove2me | solution 1 for RH1E5.group_012
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:14:11.817876+00:00
-- url     : https://prove2.me/submissions/33977fc5-94a7-4b0b-974d-60f68a03e2a4

import Definitions.Def_RH1E5_Data012
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0096 : RS5.BandZeros RH1E5_0096.s0.t RH1E5_0096.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0096.s0 RH1E5_0096.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0096.s0 RH1E5_0096.rest = RH1E5_0096.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0096.s0 :: RH1E5_0096.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0097 : RS5.BandZeros RH1E5_0097.s0.t RH1E5_0097.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0097.s0 RH1E5_0097.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0097.s0 RH1E5_0097.rest = RH1E5_0097.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0097.s0 :: RH1E5_0097.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0098 : RS5.BandZeros RH1E5_0098.s0.t RH1E5_0098.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0098.s0 RH1E5_0098.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0098.s0 RH1E5_0098.rest = RH1E5_0098.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0098.s0 :: RH1E5_0098.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0099 : RS5.BandZeros RH1E5_0099.s0.t RH1E5_0099.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0099.s0 RH1E5_0099.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0099.s0 RH1E5_0099.rest = RH1E5_0099.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0099.s0 :: RH1E5_0099.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0100 : RS5.BandZeros RH1E5_0100.s0.t RH1E5_0100.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0100.s0 RH1E5_0100.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0100.s0 RH1E5_0100.rest = RH1E5_0100.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0100.s0 :: RH1E5_0100.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0101 : RS5.BandZeros RH1E5_0101.s0.t RH1E5_0101.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0101.s0 RH1E5_0101.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0101.s0 RH1E5_0101.rest = RH1E5_0101.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0101.s0 :: RH1E5_0101.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0102 : RS5.BandZeros RH1E5_0102.s0.t RH1E5_0102.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0102.s0 RH1E5_0102.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0102.s0 RH1E5_0102.rest = RH1E5_0102.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0102.s0 :: RH1E5_0102.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0103 : RS5.BandZeros RH1E5_0103.s0.t RH1E5_0103.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0103.s0 RH1E5_0103.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0103.s0 RH1E5_0103.rest = RH1E5_0103.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0103.s0 :: RH1E5_0103.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_012 : RS5.BandZeros RH1E5_0096.s0.t RH1E5_0103.sL.t 1016 := by
  have g96 := band_0096
  have g97 := RS5.BandZeros.glue (a := RH1E5_0096.s0.t) (b := RH1E5_0096.sL.t) (c := RH1E5_0097.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0096.s0, RH1E5_0095.sL, RH1E5_0096.sL]) (by norm_num [RS5.Sample.t, RH1E5_0096.sL, RH1E5_0097.sL]) g96 band_0097
  have g98 := RS5.BandZeros.glue (a := RH1E5_0096.s0.t) (b := RH1E5_0097.sL.t) (c := RH1E5_0098.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0096.s0, RH1E5_0095.sL, RH1E5_0097.sL]) (by norm_num [RS5.Sample.t, RH1E5_0097.sL, RH1E5_0098.sL]) g97 band_0098
  have g99 := RS5.BandZeros.glue (a := RH1E5_0096.s0.t) (b := RH1E5_0098.sL.t) (c := RH1E5_0099.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0096.s0, RH1E5_0095.sL, RH1E5_0098.sL]) (by norm_num [RS5.Sample.t, RH1E5_0098.sL, RH1E5_0099.sL]) g98 band_0099
  have g100 := RS5.BandZeros.glue (a := RH1E5_0096.s0.t) (b := RH1E5_0099.sL.t) (c := RH1E5_0100.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0096.s0, RH1E5_0095.sL, RH1E5_0099.sL]) (by norm_num [RS5.Sample.t, RH1E5_0099.sL, RH1E5_0100.sL]) g99 band_0100
  have g101 := RS5.BandZeros.glue (a := RH1E5_0096.s0.t) (b := RH1E5_0100.sL.t) (c := RH1E5_0101.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0096.s0, RH1E5_0095.sL, RH1E5_0100.sL]) (by norm_num [RS5.Sample.t, RH1E5_0100.sL, RH1E5_0101.sL]) g100 band_0101
  have g102 := RS5.BandZeros.glue (a := RH1E5_0096.s0.t) (b := RH1E5_0101.sL.t) (c := RH1E5_0102.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0096.s0, RH1E5_0095.sL, RH1E5_0101.sL]) (by norm_num [RS5.Sample.t, RH1E5_0101.sL, RH1E5_0102.sL]) g101 band_0102
  have g103 := RS5.BandZeros.glue (a := RH1E5_0096.s0.t) (b := RH1E5_0102.sL.t) (c := RH1E5_0103.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0096.s0, RH1E5_0095.sL, RH1E5_0102.sL]) (by norm_num [RS5.Sample.t, RH1E5_0102.sL, RH1E5_0103.sL]) g102 band_0103
  exact g103

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0096.s0.t RH1E5_0103.sL.t 1016 := by
  apply RH1E5.group_012 <;> assumption
