-- Prove2me | solution 1 for RH1E5.group_015
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:20:22.136079+00:00
-- url     : https://prove2.me/submissions/d0a89cae-15d5-4fa5-b8a8-49a7c3814393

import Definitions.Def_RH1E5_Data015
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0120 : RS5.BandZeros RH1E5_0120.s0.t RH1E5_0120.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0120.s0 RH1E5_0120.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0120.s0 RH1E5_0120.rest = RH1E5_0120.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0120.s0 :: RH1E5_0120.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0121 : RS5.BandZeros RH1E5_0121.s0.t RH1E5_0121.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0121.s0 RH1E5_0121.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0121.s0 RH1E5_0121.rest = RH1E5_0121.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0121.s0 :: RH1E5_0121.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0122 : RS5.BandZeros RH1E5_0122.s0.t RH1E5_0122.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0122.s0 RH1E5_0122.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0122.s0 RH1E5_0122.rest = RH1E5_0122.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0122.s0 :: RH1E5_0122.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0123 : RS5.BandZeros RH1E5_0123.s0.t RH1E5_0123.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0123.s0 RH1E5_0123.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0123.s0 RH1E5_0123.rest = RH1E5_0123.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0123.s0 :: RH1E5_0123.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0124 : RS5.BandZeros RH1E5_0124.s0.t RH1E5_0124.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0124.s0 RH1E5_0124.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0124.s0 RH1E5_0124.rest = RH1E5_0124.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0124.s0 :: RH1E5_0124.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0125 : RS5.BandZeros RH1E5_0125.s0.t RH1E5_0125.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0125.s0 RH1E5_0125.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0125.s0 RH1E5_0125.rest = RH1E5_0125.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0125.s0 :: RH1E5_0125.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0126 : RS5.BandZeros RH1E5_0126.s0.t RH1E5_0126.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0126.s0 RH1E5_0126.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0126.s0 RH1E5_0126.rest = RH1E5_0126.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0126.s0 :: RH1E5_0126.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0127 : RS5.BandZeros RH1E5_0127.s0.t RH1E5_0127.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0127.s0 RH1E5_0127.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0127.s0 RH1E5_0127.rest = RH1E5_0127.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0127.s0 :: RH1E5_0127.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_015 : RS5.BandZeros RH1E5_0120.s0.t RH1E5_0127.sL.t 1016 := by
  have g120 := band_0120
  have g121 := RS5.BandZeros.glue (a := RH1E5_0120.s0.t) (b := RH1E5_0120.sL.t) (c := RH1E5_0121.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0120.s0, RH1E5_0119.sL, RH1E5_0120.sL]) (by norm_num [RS5.Sample.t, RH1E5_0120.sL, RH1E5_0121.sL]) g120 band_0121
  have g122 := RS5.BandZeros.glue (a := RH1E5_0120.s0.t) (b := RH1E5_0121.sL.t) (c := RH1E5_0122.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0120.s0, RH1E5_0119.sL, RH1E5_0121.sL]) (by norm_num [RS5.Sample.t, RH1E5_0121.sL, RH1E5_0122.sL]) g121 band_0122
  have g123 := RS5.BandZeros.glue (a := RH1E5_0120.s0.t) (b := RH1E5_0122.sL.t) (c := RH1E5_0123.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0120.s0, RH1E5_0119.sL, RH1E5_0122.sL]) (by norm_num [RS5.Sample.t, RH1E5_0122.sL, RH1E5_0123.sL]) g122 band_0123
  have g124 := RS5.BandZeros.glue (a := RH1E5_0120.s0.t) (b := RH1E5_0123.sL.t) (c := RH1E5_0124.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0120.s0, RH1E5_0119.sL, RH1E5_0123.sL]) (by norm_num [RS5.Sample.t, RH1E5_0123.sL, RH1E5_0124.sL]) g123 band_0124
  have g125 := RS5.BandZeros.glue (a := RH1E5_0120.s0.t) (b := RH1E5_0124.sL.t) (c := RH1E5_0125.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0120.s0, RH1E5_0119.sL, RH1E5_0124.sL]) (by norm_num [RS5.Sample.t, RH1E5_0124.sL, RH1E5_0125.sL]) g124 band_0125
  have g126 := RS5.BandZeros.glue (a := RH1E5_0120.s0.t) (b := RH1E5_0125.sL.t) (c := RH1E5_0126.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0120.s0, RH1E5_0119.sL, RH1E5_0125.sL]) (by norm_num [RS5.Sample.t, RH1E5_0125.sL, RH1E5_0126.sL]) g125 band_0126
  have g127 := RS5.BandZeros.glue (a := RH1E5_0120.s0.t) (b := RH1E5_0126.sL.t) (c := RH1E5_0127.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0120.s0, RH1E5_0119.sL, RH1E5_0126.sL]) (by norm_num [RS5.Sample.t, RH1E5_0126.sL, RH1E5_0127.sL]) g126 band_0127
  exact g127

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0120.s0.t RH1E5_0127.sL.t 1016 := by
  apply RH1E5.group_015 <;> assumption
