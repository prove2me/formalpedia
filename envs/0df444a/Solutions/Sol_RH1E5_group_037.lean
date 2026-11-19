-- Prove2me | solution 1 for RH1E5.group_037
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:15:09.807904+00:00
-- url     : https://prove2.me/submissions/731702e4-49a7-438d-abc2-820d29f2db76

import Definitions.Def_RH1E5_Data037
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0296 : RS5.BandZeros RH1E5_0296.s0.t RH1E5_0296.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0296.s0 RH1E5_0296.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0296.s0 RH1E5_0296.rest = RH1E5_0296.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0296.s0 :: RH1E5_0296.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0297 : RS5.BandZeros RH1E5_0297.s0.t RH1E5_0297.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0297.s0 RH1E5_0297.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0297.s0 RH1E5_0297.rest = RH1E5_0297.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0297.s0 :: RH1E5_0297.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0298 : RS5.BandZeros RH1E5_0298.s0.t RH1E5_0298.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0298.s0 RH1E5_0298.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0298.s0 RH1E5_0298.rest = RH1E5_0298.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0298.s0 :: RH1E5_0298.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0299 : RS5.BandZeros RH1E5_0299.s0.t RH1E5_0299.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0299.s0 RH1E5_0299.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0299.s0 RH1E5_0299.rest = RH1E5_0299.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0299.s0 :: RH1E5_0299.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0300 : RS5.BandZeros RH1E5_0300.s0.t RH1E5_0300.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0300.s0 RH1E5_0300.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0300.s0 RH1E5_0300.rest = RH1E5_0300.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0300.s0 :: RH1E5_0300.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0301 : RS5.BandZeros RH1E5_0301.s0.t RH1E5_0301.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0301.s0 RH1E5_0301.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0301.s0 RH1E5_0301.rest = RH1E5_0301.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0301.s0 :: RH1E5_0301.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0302 : RS5.BandZeros RH1E5_0302.s0.t RH1E5_0302.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0302.s0 RH1E5_0302.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0302.s0 RH1E5_0302.rest = RH1E5_0302.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0302.s0 :: RH1E5_0302.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0303 : RS5.BandZeros RH1E5_0303.s0.t RH1E5_0303.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0303.s0 RH1E5_0303.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0303.s0 RH1E5_0303.rest = RH1E5_0303.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0303.s0 :: RH1E5_0303.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_037 : RS5.BandZeros RH1E5_0296.s0.t RH1E5_0303.sL.t 1016 := by
  have g296 := band_0296
  have g297 := RS5.BandZeros.glue (a := RH1E5_0296.s0.t) (b := RH1E5_0296.sL.t) (c := RH1E5_0297.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0296.s0, RH1E5_0295.sL, RH1E5_0296.sL]) (by norm_num [RS5.Sample.t, RH1E5_0296.sL, RH1E5_0297.sL]) g296 band_0297
  have g298 := RS5.BandZeros.glue (a := RH1E5_0296.s0.t) (b := RH1E5_0297.sL.t) (c := RH1E5_0298.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0296.s0, RH1E5_0295.sL, RH1E5_0297.sL]) (by norm_num [RS5.Sample.t, RH1E5_0297.sL, RH1E5_0298.sL]) g297 band_0298
  have g299 := RS5.BandZeros.glue (a := RH1E5_0296.s0.t) (b := RH1E5_0298.sL.t) (c := RH1E5_0299.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0296.s0, RH1E5_0295.sL, RH1E5_0298.sL]) (by norm_num [RS5.Sample.t, RH1E5_0298.sL, RH1E5_0299.sL]) g298 band_0299
  have g300 := RS5.BandZeros.glue (a := RH1E5_0296.s0.t) (b := RH1E5_0299.sL.t) (c := RH1E5_0300.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0296.s0, RH1E5_0295.sL, RH1E5_0299.sL]) (by norm_num [RS5.Sample.t, RH1E5_0299.sL, RH1E5_0300.sL]) g299 band_0300
  have g301 := RS5.BandZeros.glue (a := RH1E5_0296.s0.t) (b := RH1E5_0300.sL.t) (c := RH1E5_0301.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0296.s0, RH1E5_0295.sL, RH1E5_0300.sL]) (by norm_num [RS5.Sample.t, RH1E5_0300.sL, RH1E5_0301.sL]) g300 band_0301
  have g302 := RS5.BandZeros.glue (a := RH1E5_0296.s0.t) (b := RH1E5_0301.sL.t) (c := RH1E5_0302.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0296.s0, RH1E5_0295.sL, RH1E5_0301.sL]) (by norm_num [RS5.Sample.t, RH1E5_0301.sL, RH1E5_0302.sL]) g301 band_0302
  have g303 := RS5.BandZeros.glue (a := RH1E5_0296.s0.t) (b := RH1E5_0302.sL.t) (c := RH1E5_0303.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0296.s0, RH1E5_0295.sL, RH1E5_0302.sL]) (by norm_num [RS5.Sample.t, RH1E5_0302.sL, RH1E5_0303.sL]) g302 band_0303
  exact g303

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0296.s0.t RH1E5_0303.sL.t 1016 := by
  apply RH1E5.group_037 <;> assumption
