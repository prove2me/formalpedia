-- Prove2me | solution 1 for RH1E5.group_010
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:07:59.67049+00:00
-- url     : https://prove2.me/submissions/f684e320-5327-4668-b37f-55faf6ab52b2

import Definitions.Def_RH1E5_Data010
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0080 : RS5.BandZeros RH1E5_0080.s0.t RH1E5_0080.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0080.s0 RH1E5_0080.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0080.s0 RH1E5_0080.rest = RH1E5_0080.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0080.s0 :: RH1E5_0080.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0081 : RS5.BandZeros RH1E5_0081.s0.t RH1E5_0081.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0081.s0 RH1E5_0081.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0081.s0 RH1E5_0081.rest = RH1E5_0081.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0081.s0 :: RH1E5_0081.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0082 : RS5.BandZeros RH1E5_0082.s0.t RH1E5_0082.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0082.s0 RH1E5_0082.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0082.s0 RH1E5_0082.rest = RH1E5_0082.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0082.s0 :: RH1E5_0082.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0083 : RS5.BandZeros RH1E5_0083.s0.t RH1E5_0083.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0083.s0 RH1E5_0083.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0083.s0 RH1E5_0083.rest = RH1E5_0083.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0083.s0 :: RH1E5_0083.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0084 : RS5.BandZeros RH1E5_0084.s0.t RH1E5_0084.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0084.s0 RH1E5_0084.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0084.s0 RH1E5_0084.rest = RH1E5_0084.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0084.s0 :: RH1E5_0084.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0085 : RS5.BandZeros RH1E5_0085.s0.t RH1E5_0085.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0085.s0 RH1E5_0085.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0085.s0 RH1E5_0085.rest = RH1E5_0085.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0085.s0 :: RH1E5_0085.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0086 : RS5.BandZeros RH1E5_0086.s0.t RH1E5_0086.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0086.s0 RH1E5_0086.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0086.s0 RH1E5_0086.rest = RH1E5_0086.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0086.s0 :: RH1E5_0086.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0087 : RS5.BandZeros RH1E5_0087.s0.t RH1E5_0087.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0087.s0 RH1E5_0087.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0087.s0 RH1E5_0087.rest = RH1E5_0087.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0087.s0 :: RH1E5_0087.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_010 : RS5.BandZeros RH1E5_0080.s0.t RH1E5_0087.sL.t 1016 := by
  have g80 := band_0080
  have g81 := RS5.BandZeros.glue (a := RH1E5_0080.s0.t) (b := RH1E5_0080.sL.t) (c := RH1E5_0081.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0080.s0, RH1E5_0079.sL, RH1E5_0080.sL]) (by norm_num [RS5.Sample.t, RH1E5_0080.sL, RH1E5_0081.sL]) g80 band_0081
  have g82 := RS5.BandZeros.glue (a := RH1E5_0080.s0.t) (b := RH1E5_0081.sL.t) (c := RH1E5_0082.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0080.s0, RH1E5_0079.sL, RH1E5_0081.sL]) (by norm_num [RS5.Sample.t, RH1E5_0081.sL, RH1E5_0082.sL]) g81 band_0082
  have g83 := RS5.BandZeros.glue (a := RH1E5_0080.s0.t) (b := RH1E5_0082.sL.t) (c := RH1E5_0083.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0080.s0, RH1E5_0079.sL, RH1E5_0082.sL]) (by norm_num [RS5.Sample.t, RH1E5_0082.sL, RH1E5_0083.sL]) g82 band_0083
  have g84 := RS5.BandZeros.glue (a := RH1E5_0080.s0.t) (b := RH1E5_0083.sL.t) (c := RH1E5_0084.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0080.s0, RH1E5_0079.sL, RH1E5_0083.sL]) (by norm_num [RS5.Sample.t, RH1E5_0083.sL, RH1E5_0084.sL]) g83 band_0084
  have g85 := RS5.BandZeros.glue (a := RH1E5_0080.s0.t) (b := RH1E5_0084.sL.t) (c := RH1E5_0085.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0080.s0, RH1E5_0079.sL, RH1E5_0084.sL]) (by norm_num [RS5.Sample.t, RH1E5_0084.sL, RH1E5_0085.sL]) g84 band_0085
  have g86 := RS5.BandZeros.glue (a := RH1E5_0080.s0.t) (b := RH1E5_0085.sL.t) (c := RH1E5_0086.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0080.s0, RH1E5_0079.sL, RH1E5_0085.sL]) (by norm_num [RS5.Sample.t, RH1E5_0085.sL, RH1E5_0086.sL]) g85 band_0086
  have g87 := RS5.BandZeros.glue (a := RH1E5_0080.s0.t) (b := RH1E5_0086.sL.t) (c := RH1E5_0087.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0080.s0, RH1E5_0079.sL, RH1E5_0086.sL]) (by norm_num [RS5.Sample.t, RH1E5_0086.sL, RH1E5_0087.sL]) g86 band_0087
  exact g87

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0080.s0.t RH1E5_0087.sL.t 1016 := by
  apply RH1E5.group_010 <;> assumption
