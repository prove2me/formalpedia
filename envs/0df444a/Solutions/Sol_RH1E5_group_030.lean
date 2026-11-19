-- Prove2me | solution 1 for RH1E5.group_030
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:57:47.766042+00:00
-- url     : https://prove2.me/submissions/6d18a219-66f3-4d28-bbfb-0330a02ad967

import Definitions.Def_RH1E5_Data030
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0240 : RS5.BandZeros RH1E5_0240.s0.t RH1E5_0240.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0240.s0 RH1E5_0240.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0240.s0 RH1E5_0240.rest = RH1E5_0240.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0240.s0 :: RH1E5_0240.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0241 : RS5.BandZeros RH1E5_0241.s0.t RH1E5_0241.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0241.s0 RH1E5_0241.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0241.s0 RH1E5_0241.rest = RH1E5_0241.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0241.s0 :: RH1E5_0241.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0242 : RS5.BandZeros RH1E5_0242.s0.t RH1E5_0242.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0242.s0 RH1E5_0242.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0242.s0 RH1E5_0242.rest = RH1E5_0242.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0242.s0 :: RH1E5_0242.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0243 : RS5.BandZeros RH1E5_0243.s0.t RH1E5_0243.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0243.s0 RH1E5_0243.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0243.s0 RH1E5_0243.rest = RH1E5_0243.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0243.s0 :: RH1E5_0243.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0244 : RS5.BandZeros RH1E5_0244.s0.t RH1E5_0244.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0244.s0 RH1E5_0244.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0244.s0 RH1E5_0244.rest = RH1E5_0244.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0244.s0 :: RH1E5_0244.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0245 : RS5.BandZeros RH1E5_0245.s0.t RH1E5_0245.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0245.s0 RH1E5_0245.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0245.s0 RH1E5_0245.rest = RH1E5_0245.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0245.s0 :: RH1E5_0245.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0246 : RS5.BandZeros RH1E5_0246.s0.t RH1E5_0246.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0246.s0 RH1E5_0246.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0246.s0 RH1E5_0246.rest = RH1E5_0246.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0246.s0 :: RH1E5_0246.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0247 : RS5.BandZeros RH1E5_0247.s0.t RH1E5_0247.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0247.s0 RH1E5_0247.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0247.s0 RH1E5_0247.rest = RH1E5_0247.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0247.s0 :: RH1E5_0247.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_030 : RS5.BandZeros RH1E5_0240.s0.t RH1E5_0247.sL.t 1016 := by
  have g240 := band_0240
  have g241 := RS5.BandZeros.glue (a := RH1E5_0240.s0.t) (b := RH1E5_0240.sL.t) (c := RH1E5_0241.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0240.s0, RH1E5_0239.sL, RH1E5_0240.sL]) (by norm_num [RS5.Sample.t, RH1E5_0240.sL, RH1E5_0241.sL]) g240 band_0241
  have g242 := RS5.BandZeros.glue (a := RH1E5_0240.s0.t) (b := RH1E5_0241.sL.t) (c := RH1E5_0242.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0240.s0, RH1E5_0239.sL, RH1E5_0241.sL]) (by norm_num [RS5.Sample.t, RH1E5_0241.sL, RH1E5_0242.sL]) g241 band_0242
  have g243 := RS5.BandZeros.glue (a := RH1E5_0240.s0.t) (b := RH1E5_0242.sL.t) (c := RH1E5_0243.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0240.s0, RH1E5_0239.sL, RH1E5_0242.sL]) (by norm_num [RS5.Sample.t, RH1E5_0242.sL, RH1E5_0243.sL]) g242 band_0243
  have g244 := RS5.BandZeros.glue (a := RH1E5_0240.s0.t) (b := RH1E5_0243.sL.t) (c := RH1E5_0244.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0240.s0, RH1E5_0239.sL, RH1E5_0243.sL]) (by norm_num [RS5.Sample.t, RH1E5_0243.sL, RH1E5_0244.sL]) g243 band_0244
  have g245 := RS5.BandZeros.glue (a := RH1E5_0240.s0.t) (b := RH1E5_0244.sL.t) (c := RH1E5_0245.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0240.s0, RH1E5_0239.sL, RH1E5_0244.sL]) (by norm_num [RS5.Sample.t, RH1E5_0244.sL, RH1E5_0245.sL]) g244 band_0245
  have g246 := RS5.BandZeros.glue (a := RH1E5_0240.s0.t) (b := RH1E5_0245.sL.t) (c := RH1E5_0246.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0240.s0, RH1E5_0239.sL, RH1E5_0245.sL]) (by norm_num [RS5.Sample.t, RH1E5_0245.sL, RH1E5_0246.sL]) g245 band_0246
  have g247 := RS5.BandZeros.glue (a := RH1E5_0240.s0.t) (b := RH1E5_0246.sL.t) (c := RH1E5_0247.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0240.s0, RH1E5_0239.sL, RH1E5_0246.sL]) (by norm_num [RS5.Sample.t, RH1E5_0246.sL, RH1E5_0247.sL]) g246 band_0247
  exact g247

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0240.s0.t RH1E5_0247.sL.t 1016 := by
  apply RH1E5.group_030 <;> assumption
