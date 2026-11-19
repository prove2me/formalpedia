-- Prove2me | solution 1 for RH1E5.group_024
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:42:53.631433+00:00
-- url     : https://prove2.me/submissions/b60dc781-f9de-4609-9f32-48377a9ec6c2

import Definitions.Def_RH1E5_Data024
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0192 : RS5.BandZeros RH1E5_0192.s0.t RH1E5_0192.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0192.s0 RH1E5_0192.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0192.s0 RH1E5_0192.rest = RH1E5_0192.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0192.s0 :: RH1E5_0192.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0193 : RS5.BandZeros RH1E5_0193.s0.t RH1E5_0193.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0193.s0 RH1E5_0193.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0193.s0 RH1E5_0193.rest = RH1E5_0193.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0193.s0 :: RH1E5_0193.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0194 : RS5.BandZeros RH1E5_0194.s0.t RH1E5_0194.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0194.s0 RH1E5_0194.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0194.s0 RH1E5_0194.rest = RH1E5_0194.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0194.s0 :: RH1E5_0194.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0195 : RS5.BandZeros RH1E5_0195.s0.t RH1E5_0195.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0195.s0 RH1E5_0195.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0195.s0 RH1E5_0195.rest = RH1E5_0195.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0195.s0 :: RH1E5_0195.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0196 : RS5.BandZeros RH1E5_0196.s0.t RH1E5_0196.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0196.s0 RH1E5_0196.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0196.s0 RH1E5_0196.rest = RH1E5_0196.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0196.s0 :: RH1E5_0196.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0197 : RS5.BandZeros RH1E5_0197.s0.t RH1E5_0197.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0197.s0 RH1E5_0197.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0197.s0 RH1E5_0197.rest = RH1E5_0197.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0197.s0 :: RH1E5_0197.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0198 : RS5.BandZeros RH1E5_0198.s0.t RH1E5_0198.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0198.s0 RH1E5_0198.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0198.s0 RH1E5_0198.rest = RH1E5_0198.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0198.s0 :: RH1E5_0198.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0199 : RS5.BandZeros RH1E5_0199.s0.t RH1E5_0199.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0199.s0 RH1E5_0199.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0199.s0 RH1E5_0199.rest = RH1E5_0199.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0199.s0 :: RH1E5_0199.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_024 : RS5.BandZeros RH1E5_0192.s0.t RH1E5_0199.sL.t 1016 := by
  have g192 := band_0192
  have g193 := RS5.BandZeros.glue (a := RH1E5_0192.s0.t) (b := RH1E5_0192.sL.t) (c := RH1E5_0193.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0192.s0, RH1E5_0191.sL, RH1E5_0192.sL]) (by norm_num [RS5.Sample.t, RH1E5_0192.sL, RH1E5_0193.sL]) g192 band_0193
  have g194 := RS5.BandZeros.glue (a := RH1E5_0192.s0.t) (b := RH1E5_0193.sL.t) (c := RH1E5_0194.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0192.s0, RH1E5_0191.sL, RH1E5_0193.sL]) (by norm_num [RS5.Sample.t, RH1E5_0193.sL, RH1E5_0194.sL]) g193 band_0194
  have g195 := RS5.BandZeros.glue (a := RH1E5_0192.s0.t) (b := RH1E5_0194.sL.t) (c := RH1E5_0195.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0192.s0, RH1E5_0191.sL, RH1E5_0194.sL]) (by norm_num [RS5.Sample.t, RH1E5_0194.sL, RH1E5_0195.sL]) g194 band_0195
  have g196 := RS5.BandZeros.glue (a := RH1E5_0192.s0.t) (b := RH1E5_0195.sL.t) (c := RH1E5_0196.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0192.s0, RH1E5_0191.sL, RH1E5_0195.sL]) (by norm_num [RS5.Sample.t, RH1E5_0195.sL, RH1E5_0196.sL]) g195 band_0196
  have g197 := RS5.BandZeros.glue (a := RH1E5_0192.s0.t) (b := RH1E5_0196.sL.t) (c := RH1E5_0197.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0192.s0, RH1E5_0191.sL, RH1E5_0196.sL]) (by norm_num [RS5.Sample.t, RH1E5_0196.sL, RH1E5_0197.sL]) g196 band_0197
  have g198 := RS5.BandZeros.glue (a := RH1E5_0192.s0.t) (b := RH1E5_0197.sL.t) (c := RH1E5_0198.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0192.s0, RH1E5_0191.sL, RH1E5_0197.sL]) (by norm_num [RS5.Sample.t, RH1E5_0197.sL, RH1E5_0198.sL]) g197 band_0198
  have g199 := RS5.BandZeros.glue (a := RH1E5_0192.s0.t) (b := RH1E5_0198.sL.t) (c := RH1E5_0199.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0192.s0, RH1E5_0191.sL, RH1E5_0198.sL]) (by norm_num [RS5.Sample.t, RH1E5_0198.sL, RH1E5_0199.sL]) g198 band_0199
  exact g199

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0192.s0.t RH1E5_0199.sL.t 1016 := by
  apply RH1E5.group_024 <;> assumption
