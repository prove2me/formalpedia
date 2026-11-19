-- Prove2me | solution 1 for RH1E5.group_018
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:27:48.20675+00:00
-- url     : https://prove2.me/submissions/31eeac96-4047-41cb-8b87-c99bd1e08f40

import Definitions.Def_RH1E5_Data018
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0144 : RS5.BandZeros RH1E5_0144.s0.t RH1E5_0144.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0144.s0 RH1E5_0144.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0144.s0 RH1E5_0144.rest = RH1E5_0144.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0144.s0 :: RH1E5_0144.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0145 : RS5.BandZeros RH1E5_0145.s0.t RH1E5_0145.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0145.s0 RH1E5_0145.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0145.s0 RH1E5_0145.rest = RH1E5_0145.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0145.s0 :: RH1E5_0145.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0146 : RS5.BandZeros RH1E5_0146.s0.t RH1E5_0146.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0146.s0 RH1E5_0146.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0146.s0 RH1E5_0146.rest = RH1E5_0146.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0146.s0 :: RH1E5_0146.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0147 : RS5.BandZeros RH1E5_0147.s0.t RH1E5_0147.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0147.s0 RH1E5_0147.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0147.s0 RH1E5_0147.rest = RH1E5_0147.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0147.s0 :: RH1E5_0147.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0148 : RS5.BandZeros RH1E5_0148.s0.t RH1E5_0148.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0148.s0 RH1E5_0148.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0148.s0 RH1E5_0148.rest = RH1E5_0148.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0148.s0 :: RH1E5_0148.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0149 : RS5.BandZeros RH1E5_0149.s0.t RH1E5_0149.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0149.s0 RH1E5_0149.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0149.s0 RH1E5_0149.rest = RH1E5_0149.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0149.s0 :: RH1E5_0149.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0150 : RS5.BandZeros RH1E5_0150.s0.t RH1E5_0150.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0150.s0 RH1E5_0150.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0150.s0 RH1E5_0150.rest = RH1E5_0150.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0150.s0 :: RH1E5_0150.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0151 : RS5.BandZeros RH1E5_0151.s0.t RH1E5_0151.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0151.s0 RH1E5_0151.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0151.s0 RH1E5_0151.rest = RH1E5_0151.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0151.s0 :: RH1E5_0151.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_018 : RS5.BandZeros RH1E5_0144.s0.t RH1E5_0151.sL.t 1016 := by
  have g144 := band_0144
  have g145 := RS5.BandZeros.glue (a := RH1E5_0144.s0.t) (b := RH1E5_0144.sL.t) (c := RH1E5_0145.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0144.s0, RH1E5_0143.sL, RH1E5_0144.sL]) (by norm_num [RS5.Sample.t, RH1E5_0144.sL, RH1E5_0145.sL]) g144 band_0145
  have g146 := RS5.BandZeros.glue (a := RH1E5_0144.s0.t) (b := RH1E5_0145.sL.t) (c := RH1E5_0146.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0144.s0, RH1E5_0143.sL, RH1E5_0145.sL]) (by norm_num [RS5.Sample.t, RH1E5_0145.sL, RH1E5_0146.sL]) g145 band_0146
  have g147 := RS5.BandZeros.glue (a := RH1E5_0144.s0.t) (b := RH1E5_0146.sL.t) (c := RH1E5_0147.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0144.s0, RH1E5_0143.sL, RH1E5_0146.sL]) (by norm_num [RS5.Sample.t, RH1E5_0146.sL, RH1E5_0147.sL]) g146 band_0147
  have g148 := RS5.BandZeros.glue (a := RH1E5_0144.s0.t) (b := RH1E5_0147.sL.t) (c := RH1E5_0148.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0144.s0, RH1E5_0143.sL, RH1E5_0147.sL]) (by norm_num [RS5.Sample.t, RH1E5_0147.sL, RH1E5_0148.sL]) g147 band_0148
  have g149 := RS5.BandZeros.glue (a := RH1E5_0144.s0.t) (b := RH1E5_0148.sL.t) (c := RH1E5_0149.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0144.s0, RH1E5_0143.sL, RH1E5_0148.sL]) (by norm_num [RS5.Sample.t, RH1E5_0148.sL, RH1E5_0149.sL]) g148 band_0149
  have g150 := RS5.BandZeros.glue (a := RH1E5_0144.s0.t) (b := RH1E5_0149.sL.t) (c := RH1E5_0150.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0144.s0, RH1E5_0143.sL, RH1E5_0149.sL]) (by norm_num [RS5.Sample.t, RH1E5_0149.sL, RH1E5_0150.sL]) g149 band_0150
  have g151 := RS5.BandZeros.glue (a := RH1E5_0144.s0.t) (b := RH1E5_0150.sL.t) (c := RH1E5_0151.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0144.s0, RH1E5_0143.sL, RH1E5_0150.sL]) (by norm_num [RS5.Sample.t, RH1E5_0150.sL, RH1E5_0151.sL]) g150 band_0151
  exact g151

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0144.s0.t RH1E5_0151.sL.t 1016 := by
  apply RH1E5.group_018 <;> assumption
