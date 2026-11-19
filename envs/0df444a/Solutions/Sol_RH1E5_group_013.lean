-- Prove2me | solution 1 for RH1E5.group_013
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:15:24.616229+00:00
-- url     : https://prove2.me/submissions/50223108-5d64-45d7-a3c8-0e197af5bbe4

import Definitions.Def_RH1E5_Data013
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0104 : RS5.BandZeros RH1E5_0104.s0.t RH1E5_0104.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0104.s0 RH1E5_0104.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0104.s0 RH1E5_0104.rest = RH1E5_0104.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0104.s0 :: RH1E5_0104.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0105 : RS5.BandZeros RH1E5_0105.s0.t RH1E5_0105.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0105.s0 RH1E5_0105.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0105.s0 RH1E5_0105.rest = RH1E5_0105.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0105.s0 :: RH1E5_0105.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0106 : RS5.BandZeros RH1E5_0106.s0.t RH1E5_0106.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0106.s0 RH1E5_0106.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0106.s0 RH1E5_0106.rest = RH1E5_0106.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0106.s0 :: RH1E5_0106.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0107 : RS5.BandZeros RH1E5_0107.s0.t RH1E5_0107.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0107.s0 RH1E5_0107.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0107.s0 RH1E5_0107.rest = RH1E5_0107.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0107.s0 :: RH1E5_0107.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0108 : RS5.BandZeros RH1E5_0108.s0.t RH1E5_0108.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0108.s0 RH1E5_0108.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0108.s0 RH1E5_0108.rest = RH1E5_0108.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0108.s0 :: RH1E5_0108.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0109 : RS5.BandZeros RH1E5_0109.s0.t RH1E5_0109.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0109.s0 RH1E5_0109.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0109.s0 RH1E5_0109.rest = RH1E5_0109.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0109.s0 :: RH1E5_0109.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0110 : RS5.BandZeros RH1E5_0110.s0.t RH1E5_0110.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0110.s0 RH1E5_0110.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0110.s0 RH1E5_0110.rest = RH1E5_0110.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0110.s0 :: RH1E5_0110.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0111 : RS5.BandZeros RH1E5_0111.s0.t RH1E5_0111.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0111.s0 RH1E5_0111.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0111.s0 RH1E5_0111.rest = RH1E5_0111.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0111.s0 :: RH1E5_0111.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_013 : RS5.BandZeros RH1E5_0104.s0.t RH1E5_0111.sL.t 1016 := by
  have g104 := band_0104
  have g105 := RS5.BandZeros.glue (a := RH1E5_0104.s0.t) (b := RH1E5_0104.sL.t) (c := RH1E5_0105.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0104.s0, RH1E5_0103.sL, RH1E5_0104.sL]) (by norm_num [RS5.Sample.t, RH1E5_0104.sL, RH1E5_0105.sL]) g104 band_0105
  have g106 := RS5.BandZeros.glue (a := RH1E5_0104.s0.t) (b := RH1E5_0105.sL.t) (c := RH1E5_0106.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0104.s0, RH1E5_0103.sL, RH1E5_0105.sL]) (by norm_num [RS5.Sample.t, RH1E5_0105.sL, RH1E5_0106.sL]) g105 band_0106
  have g107 := RS5.BandZeros.glue (a := RH1E5_0104.s0.t) (b := RH1E5_0106.sL.t) (c := RH1E5_0107.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0104.s0, RH1E5_0103.sL, RH1E5_0106.sL]) (by norm_num [RS5.Sample.t, RH1E5_0106.sL, RH1E5_0107.sL]) g106 band_0107
  have g108 := RS5.BandZeros.glue (a := RH1E5_0104.s0.t) (b := RH1E5_0107.sL.t) (c := RH1E5_0108.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0104.s0, RH1E5_0103.sL, RH1E5_0107.sL]) (by norm_num [RS5.Sample.t, RH1E5_0107.sL, RH1E5_0108.sL]) g107 band_0108
  have g109 := RS5.BandZeros.glue (a := RH1E5_0104.s0.t) (b := RH1E5_0108.sL.t) (c := RH1E5_0109.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0104.s0, RH1E5_0103.sL, RH1E5_0108.sL]) (by norm_num [RS5.Sample.t, RH1E5_0108.sL, RH1E5_0109.sL]) g108 band_0109
  have g110 := RS5.BandZeros.glue (a := RH1E5_0104.s0.t) (b := RH1E5_0109.sL.t) (c := RH1E5_0110.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0104.s0, RH1E5_0103.sL, RH1E5_0109.sL]) (by norm_num [RS5.Sample.t, RH1E5_0109.sL, RH1E5_0110.sL]) g109 band_0110
  have g111 := RS5.BandZeros.glue (a := RH1E5_0104.s0.t) (b := RH1E5_0110.sL.t) (c := RH1E5_0111.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0104.s0, RH1E5_0103.sL, RH1E5_0110.sL]) (by norm_num [RS5.Sample.t, RH1E5_0110.sL, RH1E5_0111.sL]) g110 band_0111
  exact g111

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0104.s0.t RH1E5_0111.sL.t 1016 := by
  apply RH1E5.group_013 <;> assumption
