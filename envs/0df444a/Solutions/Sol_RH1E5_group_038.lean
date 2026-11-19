-- Prove2me | solution 1 for RH1E5.group_038
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:17:41.407239+00:00
-- url     : https://prove2.me/submissions/b3a4503f-8585-49c7-a56d-f0a1c285eff6

import Definitions.Def_RH1E5_Data038
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0304 : RS5.BandZeros RH1E5_0304.s0.t RH1E5_0304.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0304.s0 RH1E5_0304.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0304.s0 RH1E5_0304.rest = RH1E5_0304.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0304.s0 :: RH1E5_0304.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0305 : RS5.BandZeros RH1E5_0305.s0.t RH1E5_0305.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0305.s0 RH1E5_0305.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0305.s0 RH1E5_0305.rest = RH1E5_0305.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0305.s0 :: RH1E5_0305.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0306 : RS5.BandZeros RH1E5_0306.s0.t RH1E5_0306.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0306.s0 RH1E5_0306.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0306.s0 RH1E5_0306.rest = RH1E5_0306.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0306.s0 :: RH1E5_0306.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0307 : RS5.BandZeros RH1E5_0307.s0.t RH1E5_0307.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0307.s0 RH1E5_0307.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0307.s0 RH1E5_0307.rest = RH1E5_0307.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0307.s0 :: RH1E5_0307.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0308 : RS5.BandZeros RH1E5_0308.s0.t RH1E5_0308.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0308.s0 RH1E5_0308.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0308.s0 RH1E5_0308.rest = RH1E5_0308.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0308.s0 :: RH1E5_0308.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0309 : RS5.BandZeros RH1E5_0309.s0.t RH1E5_0309.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0309.s0 RH1E5_0309.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0309.s0 RH1E5_0309.rest = RH1E5_0309.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0309.s0 :: RH1E5_0309.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0310 : RS5.BandZeros RH1E5_0310.s0.t RH1E5_0310.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0310.s0 RH1E5_0310.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0310.s0 RH1E5_0310.rest = RH1E5_0310.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0310.s0 :: RH1E5_0310.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0311 : RS5.BandZeros RH1E5_0311.s0.t RH1E5_0311.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0311.s0 RH1E5_0311.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0311.s0 RH1E5_0311.rest = RH1E5_0311.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0311.s0 :: RH1E5_0311.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_038 : RS5.BandZeros RH1E5_0304.s0.t RH1E5_0311.sL.t 1016 := by
  have g304 := band_0304
  have g305 := RS5.BandZeros.glue (a := RH1E5_0304.s0.t) (b := RH1E5_0304.sL.t) (c := RH1E5_0305.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0304.s0, RH1E5_0303.sL, RH1E5_0304.sL]) (by norm_num [RS5.Sample.t, RH1E5_0304.sL, RH1E5_0305.sL]) g304 band_0305
  have g306 := RS5.BandZeros.glue (a := RH1E5_0304.s0.t) (b := RH1E5_0305.sL.t) (c := RH1E5_0306.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0304.s0, RH1E5_0303.sL, RH1E5_0305.sL]) (by norm_num [RS5.Sample.t, RH1E5_0305.sL, RH1E5_0306.sL]) g305 band_0306
  have g307 := RS5.BandZeros.glue (a := RH1E5_0304.s0.t) (b := RH1E5_0306.sL.t) (c := RH1E5_0307.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0304.s0, RH1E5_0303.sL, RH1E5_0306.sL]) (by norm_num [RS5.Sample.t, RH1E5_0306.sL, RH1E5_0307.sL]) g306 band_0307
  have g308 := RS5.BandZeros.glue (a := RH1E5_0304.s0.t) (b := RH1E5_0307.sL.t) (c := RH1E5_0308.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0304.s0, RH1E5_0303.sL, RH1E5_0307.sL]) (by norm_num [RS5.Sample.t, RH1E5_0307.sL, RH1E5_0308.sL]) g307 band_0308
  have g309 := RS5.BandZeros.glue (a := RH1E5_0304.s0.t) (b := RH1E5_0308.sL.t) (c := RH1E5_0309.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0304.s0, RH1E5_0303.sL, RH1E5_0308.sL]) (by norm_num [RS5.Sample.t, RH1E5_0308.sL, RH1E5_0309.sL]) g308 band_0309
  have g310 := RS5.BandZeros.glue (a := RH1E5_0304.s0.t) (b := RH1E5_0309.sL.t) (c := RH1E5_0310.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0304.s0, RH1E5_0303.sL, RH1E5_0309.sL]) (by norm_num [RS5.Sample.t, RH1E5_0309.sL, RH1E5_0310.sL]) g309 band_0310
  have g311 := RS5.BandZeros.glue (a := RH1E5_0304.s0.t) (b := RH1E5_0310.sL.t) (c := RH1E5_0311.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0304.s0, RH1E5_0303.sL, RH1E5_0310.sL]) (by norm_num [RS5.Sample.t, RH1E5_0310.sL, RH1E5_0311.sL]) g310 band_0311
  exact g311

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0304.s0.t RH1E5_0311.sL.t 1016 := by
  apply RH1E5.group_038 <;> assumption
