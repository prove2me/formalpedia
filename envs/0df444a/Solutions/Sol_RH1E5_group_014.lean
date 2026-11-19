-- Prove2me | solution 1 for RH1E5.group_014
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:16:43.500789+00:00
-- url     : https://prove2.me/submissions/1cd25bd1-3e5b-43f4-995f-fc720e854ee0

import Definitions.Def_RH1E5_Data014
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0112 : RS5.BandZeros RH1E5_0112.s0.t RH1E5_0112.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0112.s0 RH1E5_0112.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0112.s0 RH1E5_0112.rest = RH1E5_0112.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0112.s0 :: RH1E5_0112.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0113 : RS5.BandZeros RH1E5_0113.s0.t RH1E5_0113.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0113.s0 RH1E5_0113.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0113.s0 RH1E5_0113.rest = RH1E5_0113.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0113.s0 :: RH1E5_0113.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0114 : RS5.BandZeros RH1E5_0114.s0.t RH1E5_0114.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0114.s0 RH1E5_0114.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0114.s0 RH1E5_0114.rest = RH1E5_0114.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0114.s0 :: RH1E5_0114.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0115 : RS5.BandZeros RH1E5_0115.s0.t RH1E5_0115.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0115.s0 RH1E5_0115.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0115.s0 RH1E5_0115.rest = RH1E5_0115.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0115.s0 :: RH1E5_0115.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0116 : RS5.BandZeros RH1E5_0116.s0.t RH1E5_0116.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0116.s0 RH1E5_0116.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0116.s0 RH1E5_0116.rest = RH1E5_0116.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0116.s0 :: RH1E5_0116.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0117 : RS5.BandZeros RH1E5_0117.s0.t RH1E5_0117.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0117.s0 RH1E5_0117.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0117.s0 RH1E5_0117.rest = RH1E5_0117.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0117.s0 :: RH1E5_0117.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0118 : RS5.BandZeros RH1E5_0118.s0.t RH1E5_0118.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0118.s0 RH1E5_0118.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0118.s0 RH1E5_0118.rest = RH1E5_0118.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0118.s0 :: RH1E5_0118.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0119 : RS5.BandZeros RH1E5_0119.s0.t RH1E5_0119.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0119.s0 RH1E5_0119.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0119.s0 RH1E5_0119.rest = RH1E5_0119.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0119.s0 :: RH1E5_0119.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_014 : RS5.BandZeros RH1E5_0112.s0.t RH1E5_0119.sL.t 1016 := by
  have g112 := band_0112
  have g113 := RS5.BandZeros.glue (a := RH1E5_0112.s0.t) (b := RH1E5_0112.sL.t) (c := RH1E5_0113.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0112.s0, RH1E5_0111.sL, RH1E5_0112.sL]) (by norm_num [RS5.Sample.t, RH1E5_0112.sL, RH1E5_0113.sL]) g112 band_0113
  have g114 := RS5.BandZeros.glue (a := RH1E5_0112.s0.t) (b := RH1E5_0113.sL.t) (c := RH1E5_0114.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0112.s0, RH1E5_0111.sL, RH1E5_0113.sL]) (by norm_num [RS5.Sample.t, RH1E5_0113.sL, RH1E5_0114.sL]) g113 band_0114
  have g115 := RS5.BandZeros.glue (a := RH1E5_0112.s0.t) (b := RH1E5_0114.sL.t) (c := RH1E5_0115.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0112.s0, RH1E5_0111.sL, RH1E5_0114.sL]) (by norm_num [RS5.Sample.t, RH1E5_0114.sL, RH1E5_0115.sL]) g114 band_0115
  have g116 := RS5.BandZeros.glue (a := RH1E5_0112.s0.t) (b := RH1E5_0115.sL.t) (c := RH1E5_0116.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0112.s0, RH1E5_0111.sL, RH1E5_0115.sL]) (by norm_num [RS5.Sample.t, RH1E5_0115.sL, RH1E5_0116.sL]) g115 band_0116
  have g117 := RS5.BandZeros.glue (a := RH1E5_0112.s0.t) (b := RH1E5_0116.sL.t) (c := RH1E5_0117.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0112.s0, RH1E5_0111.sL, RH1E5_0116.sL]) (by norm_num [RS5.Sample.t, RH1E5_0116.sL, RH1E5_0117.sL]) g116 band_0117
  have g118 := RS5.BandZeros.glue (a := RH1E5_0112.s0.t) (b := RH1E5_0117.sL.t) (c := RH1E5_0118.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0112.s0, RH1E5_0111.sL, RH1E5_0117.sL]) (by norm_num [RS5.Sample.t, RH1E5_0117.sL, RH1E5_0118.sL]) g117 band_0118
  have g119 := RS5.BandZeros.glue (a := RH1E5_0112.s0.t) (b := RH1E5_0118.sL.t) (c := RH1E5_0119.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0112.s0, RH1E5_0111.sL, RH1E5_0118.sL]) (by norm_num [RS5.Sample.t, RH1E5_0118.sL, RH1E5_0119.sL]) g118 band_0119
  exact g119

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0112.s0.t RH1E5_0119.sL.t 1016 := by
  apply RH1E5.group_014 <;> assumption
