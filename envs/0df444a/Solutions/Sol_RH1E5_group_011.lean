-- Prove2me | solution 1 for RH1E5.group_011
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:10:27.251902+00:00
-- url     : https://prove2.me/submissions/94e685df-6cae-495c-8ed0-5e18df612e47

import Definitions.Def_RH1E5_Data011
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0088 : RS5.BandZeros RH1E5_0088.s0.t RH1E5_0088.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0088.s0 RH1E5_0088.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0088.s0 RH1E5_0088.rest = RH1E5_0088.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0088.s0 :: RH1E5_0088.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0089 : RS5.BandZeros RH1E5_0089.s0.t RH1E5_0089.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0089.s0 RH1E5_0089.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0089.s0 RH1E5_0089.rest = RH1E5_0089.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0089.s0 :: RH1E5_0089.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0090 : RS5.BandZeros RH1E5_0090.s0.t RH1E5_0090.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0090.s0 RH1E5_0090.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0090.s0 RH1E5_0090.rest = RH1E5_0090.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0090.s0 :: RH1E5_0090.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0091 : RS5.BandZeros RH1E5_0091.s0.t RH1E5_0091.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0091.s0 RH1E5_0091.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0091.s0 RH1E5_0091.rest = RH1E5_0091.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0091.s0 :: RH1E5_0091.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0092 : RS5.BandZeros RH1E5_0092.s0.t RH1E5_0092.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0092.s0 RH1E5_0092.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0092.s0 RH1E5_0092.rest = RH1E5_0092.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0092.s0 :: RH1E5_0092.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0093 : RS5.BandZeros RH1E5_0093.s0.t RH1E5_0093.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0093.s0 RH1E5_0093.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0093.s0 RH1E5_0093.rest = RH1E5_0093.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0093.s0 :: RH1E5_0093.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0094 : RS5.BandZeros RH1E5_0094.s0.t RH1E5_0094.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0094.s0 RH1E5_0094.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0094.s0 RH1E5_0094.rest = RH1E5_0094.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0094.s0 :: RH1E5_0094.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0095 : RS5.BandZeros RH1E5_0095.s0.t RH1E5_0095.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0095.s0 RH1E5_0095.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0095.s0 RH1E5_0095.rest = RH1E5_0095.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0095.s0 :: RH1E5_0095.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_011 : RS5.BandZeros RH1E5_0088.s0.t RH1E5_0095.sL.t 1016 := by
  have g88 := band_0088
  have g89 := RS5.BandZeros.glue (a := RH1E5_0088.s0.t) (b := RH1E5_0088.sL.t) (c := RH1E5_0089.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0088.s0, RH1E5_0087.sL, RH1E5_0088.sL]) (by norm_num [RS5.Sample.t, RH1E5_0088.sL, RH1E5_0089.sL]) g88 band_0089
  have g90 := RS5.BandZeros.glue (a := RH1E5_0088.s0.t) (b := RH1E5_0089.sL.t) (c := RH1E5_0090.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0088.s0, RH1E5_0087.sL, RH1E5_0089.sL]) (by norm_num [RS5.Sample.t, RH1E5_0089.sL, RH1E5_0090.sL]) g89 band_0090
  have g91 := RS5.BandZeros.glue (a := RH1E5_0088.s0.t) (b := RH1E5_0090.sL.t) (c := RH1E5_0091.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0088.s0, RH1E5_0087.sL, RH1E5_0090.sL]) (by norm_num [RS5.Sample.t, RH1E5_0090.sL, RH1E5_0091.sL]) g90 band_0091
  have g92 := RS5.BandZeros.glue (a := RH1E5_0088.s0.t) (b := RH1E5_0091.sL.t) (c := RH1E5_0092.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0088.s0, RH1E5_0087.sL, RH1E5_0091.sL]) (by norm_num [RS5.Sample.t, RH1E5_0091.sL, RH1E5_0092.sL]) g91 band_0092
  have g93 := RS5.BandZeros.glue (a := RH1E5_0088.s0.t) (b := RH1E5_0092.sL.t) (c := RH1E5_0093.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0088.s0, RH1E5_0087.sL, RH1E5_0092.sL]) (by norm_num [RS5.Sample.t, RH1E5_0092.sL, RH1E5_0093.sL]) g92 band_0093
  have g94 := RS5.BandZeros.glue (a := RH1E5_0088.s0.t) (b := RH1E5_0093.sL.t) (c := RH1E5_0094.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0088.s0, RH1E5_0087.sL, RH1E5_0093.sL]) (by norm_num [RS5.Sample.t, RH1E5_0093.sL, RH1E5_0094.sL]) g93 band_0094
  have g95 := RS5.BandZeros.glue (a := RH1E5_0088.s0.t) (b := RH1E5_0094.sL.t) (c := RH1E5_0095.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0088.s0, RH1E5_0087.sL, RH1E5_0094.sL]) (by norm_num [RS5.Sample.t, RH1E5_0094.sL, RH1E5_0095.sL]) g94 band_0095
  exact g95

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0088.s0.t RH1E5_0095.sL.t 1016 := by
  apply RH1E5.group_011 <;> assumption
