-- Prove2me | solution 1 for RH1E5.group_004
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:54:16.514205+00:00
-- url     : https://prove2.me/submissions/665115c2-7a22-4cae-a73d-d484328b82ac

import Definitions.Def_RH1E5_Data004
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0032 : RS5.BandZeros RH1E5_0032.s0.t RH1E5_0032.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0032.s0 RH1E5_0032.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0032.s0 RH1E5_0032.rest = RH1E5_0032.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0032.s0 :: RH1E5_0032.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0033 : RS5.BandZeros RH1E5_0033.s0.t RH1E5_0033.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0033.s0 RH1E5_0033.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0033.s0 RH1E5_0033.rest = RH1E5_0033.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0033.s0 :: RH1E5_0033.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0034 : RS5.BandZeros RH1E5_0034.s0.t RH1E5_0034.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0034.s0 RH1E5_0034.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0034.s0 RH1E5_0034.rest = RH1E5_0034.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0034.s0 :: RH1E5_0034.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0035 : RS5.BandZeros RH1E5_0035.s0.t RH1E5_0035.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0035.s0 RH1E5_0035.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0035.s0 RH1E5_0035.rest = RH1E5_0035.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0035.s0 :: RH1E5_0035.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0036 : RS5.BandZeros RH1E5_0036.s0.t RH1E5_0036.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0036.s0 RH1E5_0036.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0036.s0 RH1E5_0036.rest = RH1E5_0036.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0036.s0 :: RH1E5_0036.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0037 : RS5.BandZeros RH1E5_0037.s0.t RH1E5_0037.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0037.s0 RH1E5_0037.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0037.s0 RH1E5_0037.rest = RH1E5_0037.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0037.s0 :: RH1E5_0037.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0038 : RS5.BandZeros RH1E5_0038.s0.t RH1E5_0038.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0038.s0 RH1E5_0038.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0038.s0 RH1E5_0038.rest = RH1E5_0038.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0038.s0 :: RH1E5_0038.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0039 : RS5.BandZeros RH1E5_0039.s0.t RH1E5_0039.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0039.s0 RH1E5_0039.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0039.s0 RH1E5_0039.rest = RH1E5_0039.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0039.s0 :: RH1E5_0039.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_004 : RS5.BandZeros RH1E5_0032.s0.t RH1E5_0039.sL.t 1016 := by
  have g32 := band_0032
  have g33 := RS5.BandZeros.glue (a := RH1E5_0032.s0.t) (b := RH1E5_0032.sL.t) (c := RH1E5_0033.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0032.s0, RH1E5_0031.sL, RH1E5_0032.sL]) (by norm_num [RS5.Sample.t, RH1E5_0032.sL, RH1E5_0033.sL]) g32 band_0033
  have g34 := RS5.BandZeros.glue (a := RH1E5_0032.s0.t) (b := RH1E5_0033.sL.t) (c := RH1E5_0034.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0032.s0, RH1E5_0031.sL, RH1E5_0033.sL]) (by norm_num [RS5.Sample.t, RH1E5_0033.sL, RH1E5_0034.sL]) g33 band_0034
  have g35 := RS5.BandZeros.glue (a := RH1E5_0032.s0.t) (b := RH1E5_0034.sL.t) (c := RH1E5_0035.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0032.s0, RH1E5_0031.sL, RH1E5_0034.sL]) (by norm_num [RS5.Sample.t, RH1E5_0034.sL, RH1E5_0035.sL]) g34 band_0035
  have g36 := RS5.BandZeros.glue (a := RH1E5_0032.s0.t) (b := RH1E5_0035.sL.t) (c := RH1E5_0036.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0032.s0, RH1E5_0031.sL, RH1E5_0035.sL]) (by norm_num [RS5.Sample.t, RH1E5_0035.sL, RH1E5_0036.sL]) g35 band_0036
  have g37 := RS5.BandZeros.glue (a := RH1E5_0032.s0.t) (b := RH1E5_0036.sL.t) (c := RH1E5_0037.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0032.s0, RH1E5_0031.sL, RH1E5_0036.sL]) (by norm_num [RS5.Sample.t, RH1E5_0036.sL, RH1E5_0037.sL]) g36 band_0037
  have g38 := RS5.BandZeros.glue (a := RH1E5_0032.s0.t) (b := RH1E5_0037.sL.t) (c := RH1E5_0038.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0032.s0, RH1E5_0031.sL, RH1E5_0037.sL]) (by norm_num [RS5.Sample.t, RH1E5_0037.sL, RH1E5_0038.sL]) g37 band_0038
  have g39 := RS5.BandZeros.glue (a := RH1E5_0032.s0.t) (b := RH1E5_0038.sL.t) (c := RH1E5_0039.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0032.s0, RH1E5_0031.sL, RH1E5_0038.sL]) (by norm_num [RS5.Sample.t, RH1E5_0038.sL, RH1E5_0039.sL]) g38 band_0039
  exact g39

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0032.s0.t RH1E5_0039.sL.t 1016 := by
  apply RH1E5.group_004 <;> assumption
