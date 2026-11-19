-- Prove2me | solution 1 for RH1E5.group_041
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:24:07.704493+00:00
-- url     : https://prove2.me/submissions/bef9ae2a-b0dd-45ca-ba95-072cda1b9bf7

import Definitions.Def_RH1E5_Data041
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0328 : RS5.BandZeros RH1E5_0328.s0.t RH1E5_0328.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0328.s0 RH1E5_0328.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0328.s0 RH1E5_0328.rest = RH1E5_0328.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0328.s0 :: RH1E5_0328.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0329 : RS5.BandZeros RH1E5_0329.s0.t RH1E5_0329.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0329.s0 RH1E5_0329.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0329.s0 RH1E5_0329.rest = RH1E5_0329.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0329.s0 :: RH1E5_0329.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0330 : RS5.BandZeros RH1E5_0330.s0.t RH1E5_0330.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0330.s0 RH1E5_0330.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0330.s0 RH1E5_0330.rest = RH1E5_0330.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0330.s0 :: RH1E5_0330.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0331 : RS5.BandZeros RH1E5_0331.s0.t RH1E5_0331.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0331.s0 RH1E5_0331.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0331.s0 RH1E5_0331.rest = RH1E5_0331.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0331.s0 :: RH1E5_0331.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0332 : RS5.BandZeros RH1E5_0332.s0.t RH1E5_0332.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0332.s0 RH1E5_0332.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0332.s0 RH1E5_0332.rest = RH1E5_0332.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0332.s0 :: RH1E5_0332.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0333 : RS5.BandZeros RH1E5_0333.s0.t RH1E5_0333.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0333.s0 RH1E5_0333.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0333.s0 RH1E5_0333.rest = RH1E5_0333.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0333.s0 :: RH1E5_0333.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0334 : RS5.BandZeros RH1E5_0334.s0.t RH1E5_0334.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0334.s0 RH1E5_0334.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0334.s0 RH1E5_0334.rest = RH1E5_0334.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0334.s0 :: RH1E5_0334.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0335 : RS5.BandZeros RH1E5_0335.s0.t RH1E5_0335.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0335.s0 RH1E5_0335.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0335.s0 RH1E5_0335.rest = RH1E5_0335.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0335.s0 :: RH1E5_0335.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_041 : RS5.BandZeros RH1E5_0328.s0.t RH1E5_0335.sL.t 1016 := by
  have g328 := band_0328
  have g329 := RS5.BandZeros.glue (a := RH1E5_0328.s0.t) (b := RH1E5_0328.sL.t) (c := RH1E5_0329.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0328.s0, RH1E5_0327.sL, RH1E5_0328.sL]) (by norm_num [RS5.Sample.t, RH1E5_0328.sL, RH1E5_0329.sL]) g328 band_0329
  have g330 := RS5.BandZeros.glue (a := RH1E5_0328.s0.t) (b := RH1E5_0329.sL.t) (c := RH1E5_0330.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0328.s0, RH1E5_0327.sL, RH1E5_0329.sL]) (by norm_num [RS5.Sample.t, RH1E5_0329.sL, RH1E5_0330.sL]) g329 band_0330
  have g331 := RS5.BandZeros.glue (a := RH1E5_0328.s0.t) (b := RH1E5_0330.sL.t) (c := RH1E5_0331.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0328.s0, RH1E5_0327.sL, RH1E5_0330.sL]) (by norm_num [RS5.Sample.t, RH1E5_0330.sL, RH1E5_0331.sL]) g330 band_0331
  have g332 := RS5.BandZeros.glue (a := RH1E5_0328.s0.t) (b := RH1E5_0331.sL.t) (c := RH1E5_0332.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0328.s0, RH1E5_0327.sL, RH1E5_0331.sL]) (by norm_num [RS5.Sample.t, RH1E5_0331.sL, RH1E5_0332.sL]) g331 band_0332
  have g333 := RS5.BandZeros.glue (a := RH1E5_0328.s0.t) (b := RH1E5_0332.sL.t) (c := RH1E5_0333.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0328.s0, RH1E5_0327.sL, RH1E5_0332.sL]) (by norm_num [RS5.Sample.t, RH1E5_0332.sL, RH1E5_0333.sL]) g332 band_0333
  have g334 := RS5.BandZeros.glue (a := RH1E5_0328.s0.t) (b := RH1E5_0333.sL.t) (c := RH1E5_0334.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0328.s0, RH1E5_0327.sL, RH1E5_0333.sL]) (by norm_num [RS5.Sample.t, RH1E5_0333.sL, RH1E5_0334.sL]) g333 band_0334
  have g335 := RS5.BandZeros.glue (a := RH1E5_0328.s0.t) (b := RH1E5_0334.sL.t) (c := RH1E5_0335.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0328.s0, RH1E5_0327.sL, RH1E5_0334.sL]) (by norm_num [RS5.Sample.t, RH1E5_0334.sL, RH1E5_0335.sL]) g334 band_0335
  exact g335

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0328.s0.t RH1E5_0335.sL.t 1016 := by
  apply RH1E5.group_041 <;> assumption
