-- Prove2me | solution 1 for RH1E5.group_032
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:01:32.354586+00:00
-- url     : https://prove2.me/submissions/6b706c3d-109d-4baa-8835-47ec71c9c45b

import Definitions.Def_RH1E5_Data032
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0256 : RS5.BandZeros RH1E5_0256.s0.t RH1E5_0256.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0256.s0 RH1E5_0256.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0256.s0 RH1E5_0256.rest = RH1E5_0256.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0256.s0 :: RH1E5_0256.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0257 : RS5.BandZeros RH1E5_0257.s0.t RH1E5_0257.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0257.s0 RH1E5_0257.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0257.s0 RH1E5_0257.rest = RH1E5_0257.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0257.s0 :: RH1E5_0257.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0258 : RS5.BandZeros RH1E5_0258.s0.t RH1E5_0258.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0258.s0 RH1E5_0258.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0258.s0 RH1E5_0258.rest = RH1E5_0258.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0258.s0 :: RH1E5_0258.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0259 : RS5.BandZeros RH1E5_0259.s0.t RH1E5_0259.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0259.s0 RH1E5_0259.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0259.s0 RH1E5_0259.rest = RH1E5_0259.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0259.s0 :: RH1E5_0259.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0260 : RS5.BandZeros RH1E5_0260.s0.t RH1E5_0260.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0260.s0 RH1E5_0260.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0260.s0 RH1E5_0260.rest = RH1E5_0260.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0260.s0 :: RH1E5_0260.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0261 : RS5.BandZeros RH1E5_0261.s0.t RH1E5_0261.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0261.s0 RH1E5_0261.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0261.s0 RH1E5_0261.rest = RH1E5_0261.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0261.s0 :: RH1E5_0261.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0262 : RS5.BandZeros RH1E5_0262.s0.t RH1E5_0262.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0262.s0 RH1E5_0262.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0262.s0 RH1E5_0262.rest = RH1E5_0262.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0262.s0 :: RH1E5_0262.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0263 : RS5.BandZeros RH1E5_0263.s0.t RH1E5_0263.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0263.s0 RH1E5_0263.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0263.s0 RH1E5_0263.rest = RH1E5_0263.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0263.s0 :: RH1E5_0263.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_032 : RS5.BandZeros RH1E5_0256.s0.t RH1E5_0263.sL.t 1016 := by
  have g256 := band_0256
  have g257 := RS5.BandZeros.glue (a := RH1E5_0256.s0.t) (b := RH1E5_0256.sL.t) (c := RH1E5_0257.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0256.s0, RH1E5_0255.sL, RH1E5_0256.sL]) (by norm_num [RS5.Sample.t, RH1E5_0256.sL, RH1E5_0257.sL]) g256 band_0257
  have g258 := RS5.BandZeros.glue (a := RH1E5_0256.s0.t) (b := RH1E5_0257.sL.t) (c := RH1E5_0258.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0256.s0, RH1E5_0255.sL, RH1E5_0257.sL]) (by norm_num [RS5.Sample.t, RH1E5_0257.sL, RH1E5_0258.sL]) g257 band_0258
  have g259 := RS5.BandZeros.glue (a := RH1E5_0256.s0.t) (b := RH1E5_0258.sL.t) (c := RH1E5_0259.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0256.s0, RH1E5_0255.sL, RH1E5_0258.sL]) (by norm_num [RS5.Sample.t, RH1E5_0258.sL, RH1E5_0259.sL]) g258 band_0259
  have g260 := RS5.BandZeros.glue (a := RH1E5_0256.s0.t) (b := RH1E5_0259.sL.t) (c := RH1E5_0260.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0256.s0, RH1E5_0255.sL, RH1E5_0259.sL]) (by norm_num [RS5.Sample.t, RH1E5_0259.sL, RH1E5_0260.sL]) g259 band_0260
  have g261 := RS5.BandZeros.glue (a := RH1E5_0256.s0.t) (b := RH1E5_0260.sL.t) (c := RH1E5_0261.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0256.s0, RH1E5_0255.sL, RH1E5_0260.sL]) (by norm_num [RS5.Sample.t, RH1E5_0260.sL, RH1E5_0261.sL]) g260 band_0261
  have g262 := RS5.BandZeros.glue (a := RH1E5_0256.s0.t) (b := RH1E5_0261.sL.t) (c := RH1E5_0262.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0256.s0, RH1E5_0255.sL, RH1E5_0261.sL]) (by norm_num [RS5.Sample.t, RH1E5_0261.sL, RH1E5_0262.sL]) g261 band_0262
  have g263 := RS5.BandZeros.glue (a := RH1E5_0256.s0.t) (b := RH1E5_0262.sL.t) (c := RH1E5_0263.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0256.s0, RH1E5_0255.sL, RH1E5_0262.sL]) (by norm_num [RS5.Sample.t, RH1E5_0262.sL, RH1E5_0263.sL]) g262 band_0263
  exact g263

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0256.s0.t RH1E5_0263.sL.t 1016 := by
  apply RH1E5.group_032 <;> assumption
