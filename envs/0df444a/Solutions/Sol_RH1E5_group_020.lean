-- Prove2me | solution 1 for RH1E5.group_020
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:32:51.742611+00:00
-- url     : https://prove2.me/submissions/59748077-3731-4625-a54f-0fe5cd6eeb90

import Definitions.Def_RH1E5_Data020
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0160 : RS5.BandZeros RH1E5_0160.s0.t RH1E5_0160.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0160.s0 RH1E5_0160.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0160.s0 RH1E5_0160.rest = RH1E5_0160.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0160.s0 :: RH1E5_0160.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0161 : RS5.BandZeros RH1E5_0161.s0.t RH1E5_0161.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0161.s0 RH1E5_0161.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0161.s0 RH1E5_0161.rest = RH1E5_0161.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0161.s0 :: RH1E5_0161.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0162 : RS5.BandZeros RH1E5_0162.s0.t RH1E5_0162.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0162.s0 RH1E5_0162.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0162.s0 RH1E5_0162.rest = RH1E5_0162.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0162.s0 :: RH1E5_0162.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0163 : RS5.BandZeros RH1E5_0163.s0.t RH1E5_0163.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0163.s0 RH1E5_0163.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0163.s0 RH1E5_0163.rest = RH1E5_0163.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0163.s0 :: RH1E5_0163.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0164 : RS5.BandZeros RH1E5_0164.s0.t RH1E5_0164.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0164.s0 RH1E5_0164.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0164.s0 RH1E5_0164.rest = RH1E5_0164.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0164.s0 :: RH1E5_0164.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0165 : RS5.BandZeros RH1E5_0165.s0.t RH1E5_0165.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0165.s0 RH1E5_0165.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0165.s0 RH1E5_0165.rest = RH1E5_0165.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0165.s0 :: RH1E5_0165.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0166 : RS5.BandZeros RH1E5_0166.s0.t RH1E5_0166.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0166.s0 RH1E5_0166.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0166.s0 RH1E5_0166.rest = RH1E5_0166.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0166.s0 :: RH1E5_0166.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0167 : RS5.BandZeros RH1E5_0167.s0.t RH1E5_0167.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0167.s0 RH1E5_0167.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0167.s0 RH1E5_0167.rest = RH1E5_0167.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0167.s0 :: RH1E5_0167.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_020 : RS5.BandZeros RH1E5_0160.s0.t RH1E5_0167.sL.t 1016 := by
  have g160 := band_0160
  have g161 := RS5.BandZeros.glue (a := RH1E5_0160.s0.t) (b := RH1E5_0160.sL.t) (c := RH1E5_0161.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0160.s0, RH1E5_0159.sL, RH1E5_0160.sL]) (by norm_num [RS5.Sample.t, RH1E5_0160.sL, RH1E5_0161.sL]) g160 band_0161
  have g162 := RS5.BandZeros.glue (a := RH1E5_0160.s0.t) (b := RH1E5_0161.sL.t) (c := RH1E5_0162.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0160.s0, RH1E5_0159.sL, RH1E5_0161.sL]) (by norm_num [RS5.Sample.t, RH1E5_0161.sL, RH1E5_0162.sL]) g161 band_0162
  have g163 := RS5.BandZeros.glue (a := RH1E5_0160.s0.t) (b := RH1E5_0162.sL.t) (c := RH1E5_0163.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0160.s0, RH1E5_0159.sL, RH1E5_0162.sL]) (by norm_num [RS5.Sample.t, RH1E5_0162.sL, RH1E5_0163.sL]) g162 band_0163
  have g164 := RS5.BandZeros.glue (a := RH1E5_0160.s0.t) (b := RH1E5_0163.sL.t) (c := RH1E5_0164.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0160.s0, RH1E5_0159.sL, RH1E5_0163.sL]) (by norm_num [RS5.Sample.t, RH1E5_0163.sL, RH1E5_0164.sL]) g163 band_0164
  have g165 := RS5.BandZeros.glue (a := RH1E5_0160.s0.t) (b := RH1E5_0164.sL.t) (c := RH1E5_0165.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0160.s0, RH1E5_0159.sL, RH1E5_0164.sL]) (by norm_num [RS5.Sample.t, RH1E5_0164.sL, RH1E5_0165.sL]) g164 band_0165
  have g166 := RS5.BandZeros.glue (a := RH1E5_0160.s0.t) (b := RH1E5_0165.sL.t) (c := RH1E5_0166.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0160.s0, RH1E5_0159.sL, RH1E5_0165.sL]) (by norm_num [RS5.Sample.t, RH1E5_0165.sL, RH1E5_0166.sL]) g165 band_0166
  have g167 := RS5.BandZeros.glue (a := RH1E5_0160.s0.t) (b := RH1E5_0166.sL.t) (c := RH1E5_0167.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0160.s0, RH1E5_0159.sL, RH1E5_0166.sL]) (by norm_num [RS5.Sample.t, RH1E5_0166.sL, RH1E5_0167.sL]) g166 band_0167
  exact g167

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0160.s0.t RH1E5_0167.sL.t 1016 := by
  apply RH1E5.group_020 <;> assumption
