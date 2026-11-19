-- Prove2me | solution 1 for RH1E5.group_006
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:59:18.203402+00:00
-- url     : https://prove2.me/submissions/08f2db39-ff10-42a8-87da-b00a2d25577d

import Definitions.Def_RH1E5_Data006
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0048 : RS5.BandZeros RH1E5_0048.s0.t RH1E5_0048.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0048.s0 RH1E5_0048.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0048.s0 RH1E5_0048.rest = RH1E5_0048.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0048.s0 :: RH1E5_0048.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0049 : RS5.BandZeros RH1E5_0049.s0.t RH1E5_0049.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0049.s0 RH1E5_0049.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0049.s0 RH1E5_0049.rest = RH1E5_0049.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0049.s0 :: RH1E5_0049.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0050 : RS5.BandZeros RH1E5_0050.s0.t RH1E5_0050.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0050.s0 RH1E5_0050.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0050.s0 RH1E5_0050.rest = RH1E5_0050.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0050.s0 :: RH1E5_0050.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0051 : RS5.BandZeros RH1E5_0051.s0.t RH1E5_0051.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0051.s0 RH1E5_0051.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0051.s0 RH1E5_0051.rest = RH1E5_0051.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0051.s0 :: RH1E5_0051.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0052 : RS5.BandZeros RH1E5_0052.s0.t RH1E5_0052.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0052.s0 RH1E5_0052.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0052.s0 RH1E5_0052.rest = RH1E5_0052.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0052.s0 :: RH1E5_0052.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0053 : RS5.BandZeros RH1E5_0053.s0.t RH1E5_0053.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0053.s0 RH1E5_0053.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0053.s0 RH1E5_0053.rest = RH1E5_0053.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0053.s0 :: RH1E5_0053.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0054 : RS5.BandZeros RH1E5_0054.s0.t RH1E5_0054.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0054.s0 RH1E5_0054.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0054.s0 RH1E5_0054.rest = RH1E5_0054.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0054.s0 :: RH1E5_0054.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0055 : RS5.BandZeros RH1E5_0055.s0.t RH1E5_0055.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0055.s0 RH1E5_0055.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0055.s0 RH1E5_0055.rest = RH1E5_0055.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0055.s0 :: RH1E5_0055.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_006 : RS5.BandZeros RH1E5_0048.s0.t RH1E5_0055.sL.t 1016 := by
  have g48 := band_0048
  have g49 := RS5.BandZeros.glue (a := RH1E5_0048.s0.t) (b := RH1E5_0048.sL.t) (c := RH1E5_0049.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0048.s0, RH1E5_0047.sL, RH1E5_0048.sL]) (by norm_num [RS5.Sample.t, RH1E5_0048.sL, RH1E5_0049.sL]) g48 band_0049
  have g50 := RS5.BandZeros.glue (a := RH1E5_0048.s0.t) (b := RH1E5_0049.sL.t) (c := RH1E5_0050.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0048.s0, RH1E5_0047.sL, RH1E5_0049.sL]) (by norm_num [RS5.Sample.t, RH1E5_0049.sL, RH1E5_0050.sL]) g49 band_0050
  have g51 := RS5.BandZeros.glue (a := RH1E5_0048.s0.t) (b := RH1E5_0050.sL.t) (c := RH1E5_0051.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0048.s0, RH1E5_0047.sL, RH1E5_0050.sL]) (by norm_num [RS5.Sample.t, RH1E5_0050.sL, RH1E5_0051.sL]) g50 band_0051
  have g52 := RS5.BandZeros.glue (a := RH1E5_0048.s0.t) (b := RH1E5_0051.sL.t) (c := RH1E5_0052.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0048.s0, RH1E5_0047.sL, RH1E5_0051.sL]) (by norm_num [RS5.Sample.t, RH1E5_0051.sL, RH1E5_0052.sL]) g51 band_0052
  have g53 := RS5.BandZeros.glue (a := RH1E5_0048.s0.t) (b := RH1E5_0052.sL.t) (c := RH1E5_0053.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0048.s0, RH1E5_0047.sL, RH1E5_0052.sL]) (by norm_num [RS5.Sample.t, RH1E5_0052.sL, RH1E5_0053.sL]) g52 band_0053
  have g54 := RS5.BandZeros.glue (a := RH1E5_0048.s0.t) (b := RH1E5_0053.sL.t) (c := RH1E5_0054.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0048.s0, RH1E5_0047.sL, RH1E5_0053.sL]) (by norm_num [RS5.Sample.t, RH1E5_0053.sL, RH1E5_0054.sL]) g53 band_0054
  have g55 := RS5.BandZeros.glue (a := RH1E5_0048.s0.t) (b := RH1E5_0054.sL.t) (c := RH1E5_0055.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0048.s0, RH1E5_0047.sL, RH1E5_0054.sL]) (by norm_num [RS5.Sample.t, RH1E5_0054.sL, RH1E5_0055.sL]) g54 band_0055
  exact g55

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0048.s0.t RH1E5_0055.sL.t 1016 := by
  apply RH1E5.group_006 <;> assumption
