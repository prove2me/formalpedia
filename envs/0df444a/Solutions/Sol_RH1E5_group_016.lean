-- Prove2me | solution 1 for RH1E5.group_016
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:24:09.83842+00:00
-- url     : https://prove2.me/submissions/329a21ed-5fb9-4d1a-83a4-5bf485428407

import Definitions.Def_RH1E5_Data016
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0128 : RS5.BandZeros RH1E5_0128.s0.t RH1E5_0128.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0128.s0 RH1E5_0128.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0128.s0 RH1E5_0128.rest = RH1E5_0128.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0128.s0 :: RH1E5_0128.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0129 : RS5.BandZeros RH1E5_0129.s0.t RH1E5_0129.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0129.s0 RH1E5_0129.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0129.s0 RH1E5_0129.rest = RH1E5_0129.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0129.s0 :: RH1E5_0129.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0130 : RS5.BandZeros RH1E5_0130.s0.t RH1E5_0130.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0130.s0 RH1E5_0130.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0130.s0 RH1E5_0130.rest = RH1E5_0130.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0130.s0 :: RH1E5_0130.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0131 : RS5.BandZeros RH1E5_0131.s0.t RH1E5_0131.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0131.s0 RH1E5_0131.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0131.s0 RH1E5_0131.rest = RH1E5_0131.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0131.s0 :: RH1E5_0131.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0132 : RS5.BandZeros RH1E5_0132.s0.t RH1E5_0132.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0132.s0 RH1E5_0132.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0132.s0 RH1E5_0132.rest = RH1E5_0132.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0132.s0 :: RH1E5_0132.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0133 : RS5.BandZeros RH1E5_0133.s0.t RH1E5_0133.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0133.s0 RH1E5_0133.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0133.s0 RH1E5_0133.rest = RH1E5_0133.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0133.s0 :: RH1E5_0133.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0134 : RS5.BandZeros RH1E5_0134.s0.t RH1E5_0134.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0134.s0 RH1E5_0134.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0134.s0 RH1E5_0134.rest = RH1E5_0134.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0134.s0 :: RH1E5_0134.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0135 : RS5.BandZeros RH1E5_0135.s0.t RH1E5_0135.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0135.s0 RH1E5_0135.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0135.s0 RH1E5_0135.rest = RH1E5_0135.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0135.s0 :: RH1E5_0135.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_016 : RS5.BandZeros RH1E5_0128.s0.t RH1E5_0135.sL.t 1016 := by
  have g128 := band_0128
  have g129 := RS5.BandZeros.glue (a := RH1E5_0128.s0.t) (b := RH1E5_0128.sL.t) (c := RH1E5_0129.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0128.s0, RH1E5_0127.sL, RH1E5_0128.sL]) (by norm_num [RS5.Sample.t, RH1E5_0128.sL, RH1E5_0129.sL]) g128 band_0129
  have g130 := RS5.BandZeros.glue (a := RH1E5_0128.s0.t) (b := RH1E5_0129.sL.t) (c := RH1E5_0130.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0128.s0, RH1E5_0127.sL, RH1E5_0129.sL]) (by norm_num [RS5.Sample.t, RH1E5_0129.sL, RH1E5_0130.sL]) g129 band_0130
  have g131 := RS5.BandZeros.glue (a := RH1E5_0128.s0.t) (b := RH1E5_0130.sL.t) (c := RH1E5_0131.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0128.s0, RH1E5_0127.sL, RH1E5_0130.sL]) (by norm_num [RS5.Sample.t, RH1E5_0130.sL, RH1E5_0131.sL]) g130 band_0131
  have g132 := RS5.BandZeros.glue (a := RH1E5_0128.s0.t) (b := RH1E5_0131.sL.t) (c := RH1E5_0132.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0128.s0, RH1E5_0127.sL, RH1E5_0131.sL]) (by norm_num [RS5.Sample.t, RH1E5_0131.sL, RH1E5_0132.sL]) g131 band_0132
  have g133 := RS5.BandZeros.glue (a := RH1E5_0128.s0.t) (b := RH1E5_0132.sL.t) (c := RH1E5_0133.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0128.s0, RH1E5_0127.sL, RH1E5_0132.sL]) (by norm_num [RS5.Sample.t, RH1E5_0132.sL, RH1E5_0133.sL]) g132 band_0133
  have g134 := RS5.BandZeros.glue (a := RH1E5_0128.s0.t) (b := RH1E5_0133.sL.t) (c := RH1E5_0134.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0128.s0, RH1E5_0127.sL, RH1E5_0133.sL]) (by norm_num [RS5.Sample.t, RH1E5_0133.sL, RH1E5_0134.sL]) g133 band_0134
  have g135 := RS5.BandZeros.glue (a := RH1E5_0128.s0.t) (b := RH1E5_0134.sL.t) (c := RH1E5_0135.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0128.s0, RH1E5_0127.sL, RH1E5_0134.sL]) (by norm_num [RS5.Sample.t, RH1E5_0134.sL, RH1E5_0135.sL]) g134 band_0135
  exact g135

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0128.s0.t RH1E5_0135.sL.t 1016 := by
  apply RH1E5.group_016 <;> assumption
