-- Prove2me | solution 1 for RH1E5.group_009
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:07:57.623195+00:00
-- url     : https://prove2.me/submissions/ed0d9fa2-692d-41e5-a5e3-e7e609debae1

import Definitions.Def_RH1E5_Data009
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0072 : RS5.BandZeros RH1E5_0072.s0.t RH1E5_0072.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0072.s0 RH1E5_0072.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0072.s0 RH1E5_0072.rest = RH1E5_0072.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0072.s0 :: RH1E5_0072.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0073 : RS5.BandZeros RH1E5_0073.s0.t RH1E5_0073.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0073.s0 RH1E5_0073.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0073.s0 RH1E5_0073.rest = RH1E5_0073.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0073.s0 :: RH1E5_0073.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0074 : RS5.BandZeros RH1E5_0074.s0.t RH1E5_0074.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0074.s0 RH1E5_0074.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0074.s0 RH1E5_0074.rest = RH1E5_0074.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0074.s0 :: RH1E5_0074.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0075 : RS5.BandZeros RH1E5_0075.s0.t RH1E5_0075.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0075.s0 RH1E5_0075.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0075.s0 RH1E5_0075.rest = RH1E5_0075.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0075.s0 :: RH1E5_0075.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0076 : RS5.BandZeros RH1E5_0076.s0.t RH1E5_0076.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0076.s0 RH1E5_0076.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0076.s0 RH1E5_0076.rest = RH1E5_0076.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0076.s0 :: RH1E5_0076.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0077 : RS5.BandZeros RH1E5_0077.s0.t RH1E5_0077.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0077.s0 RH1E5_0077.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0077.s0 RH1E5_0077.rest = RH1E5_0077.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0077.s0 :: RH1E5_0077.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0078 : RS5.BandZeros RH1E5_0078.s0.t RH1E5_0078.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0078.s0 RH1E5_0078.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0078.s0 RH1E5_0078.rest = RH1E5_0078.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0078.s0 :: RH1E5_0078.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0079 : RS5.BandZeros RH1E5_0079.s0.t RH1E5_0079.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0079.s0 RH1E5_0079.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0079.s0 RH1E5_0079.rest = RH1E5_0079.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0079.s0 :: RH1E5_0079.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_009 : RS5.BandZeros RH1E5_0072.s0.t RH1E5_0079.sL.t 1016 := by
  have g72 := band_0072
  have g73 := RS5.BandZeros.glue (a := RH1E5_0072.s0.t) (b := RH1E5_0072.sL.t) (c := RH1E5_0073.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0072.s0, RH1E5_0071.sL, RH1E5_0072.sL]) (by norm_num [RS5.Sample.t, RH1E5_0072.sL, RH1E5_0073.sL]) g72 band_0073
  have g74 := RS5.BandZeros.glue (a := RH1E5_0072.s0.t) (b := RH1E5_0073.sL.t) (c := RH1E5_0074.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0072.s0, RH1E5_0071.sL, RH1E5_0073.sL]) (by norm_num [RS5.Sample.t, RH1E5_0073.sL, RH1E5_0074.sL]) g73 band_0074
  have g75 := RS5.BandZeros.glue (a := RH1E5_0072.s0.t) (b := RH1E5_0074.sL.t) (c := RH1E5_0075.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0072.s0, RH1E5_0071.sL, RH1E5_0074.sL]) (by norm_num [RS5.Sample.t, RH1E5_0074.sL, RH1E5_0075.sL]) g74 band_0075
  have g76 := RS5.BandZeros.glue (a := RH1E5_0072.s0.t) (b := RH1E5_0075.sL.t) (c := RH1E5_0076.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0072.s0, RH1E5_0071.sL, RH1E5_0075.sL]) (by norm_num [RS5.Sample.t, RH1E5_0075.sL, RH1E5_0076.sL]) g75 band_0076
  have g77 := RS5.BandZeros.glue (a := RH1E5_0072.s0.t) (b := RH1E5_0076.sL.t) (c := RH1E5_0077.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0072.s0, RH1E5_0071.sL, RH1E5_0076.sL]) (by norm_num [RS5.Sample.t, RH1E5_0076.sL, RH1E5_0077.sL]) g76 band_0077
  have g78 := RS5.BandZeros.glue (a := RH1E5_0072.s0.t) (b := RH1E5_0077.sL.t) (c := RH1E5_0078.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0072.s0, RH1E5_0071.sL, RH1E5_0077.sL]) (by norm_num [RS5.Sample.t, RH1E5_0077.sL, RH1E5_0078.sL]) g77 band_0078
  have g79 := RS5.BandZeros.glue (a := RH1E5_0072.s0.t) (b := RH1E5_0078.sL.t) (c := RH1E5_0079.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0072.s0, RH1E5_0071.sL, RH1E5_0078.sL]) (by norm_num [RS5.Sample.t, RH1E5_0078.sL, RH1E5_0079.sL]) g78 band_0079
  exact g79

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0072.s0.t RH1E5_0079.sL.t 1016 := by
  apply RH1E5.group_009 <;> assumption
