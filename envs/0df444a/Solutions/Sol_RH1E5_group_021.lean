-- Prove2me | solution 1 for RH1E5.group_021
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:37:56.438053+00:00
-- url     : https://prove2.me/submissions/5080c159-3fb5-40ed-b0ff-144795e68819

import Definitions.Def_RH1E5_Data021
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0168 : RS5.BandZeros RH1E5_0168.s0.t RH1E5_0168.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0168.s0 RH1E5_0168.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0168.s0 RH1E5_0168.rest = RH1E5_0168.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0168.s0 :: RH1E5_0168.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0169 : RS5.BandZeros RH1E5_0169.s0.t RH1E5_0169.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0169.s0 RH1E5_0169.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0169.s0 RH1E5_0169.rest = RH1E5_0169.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0169.s0 :: RH1E5_0169.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0170 : RS5.BandZeros RH1E5_0170.s0.t RH1E5_0170.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0170.s0 RH1E5_0170.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0170.s0 RH1E5_0170.rest = RH1E5_0170.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0170.s0 :: RH1E5_0170.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0171 : RS5.BandZeros RH1E5_0171.s0.t RH1E5_0171.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0171.s0 RH1E5_0171.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0171.s0 RH1E5_0171.rest = RH1E5_0171.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0171.s0 :: RH1E5_0171.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0172 : RS5.BandZeros RH1E5_0172.s0.t RH1E5_0172.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0172.s0 RH1E5_0172.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0172.s0 RH1E5_0172.rest = RH1E5_0172.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0172.s0 :: RH1E5_0172.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0173 : RS5.BandZeros RH1E5_0173.s0.t RH1E5_0173.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0173.s0 RH1E5_0173.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0173.s0 RH1E5_0173.rest = RH1E5_0173.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0173.s0 :: RH1E5_0173.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0174 : RS5.BandZeros RH1E5_0174.s0.t RH1E5_0174.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0174.s0 RH1E5_0174.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0174.s0 RH1E5_0174.rest = RH1E5_0174.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0174.s0 :: RH1E5_0174.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0175 : RS5.BandZeros RH1E5_0175.s0.t RH1E5_0175.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0175.s0 RH1E5_0175.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0175.s0 RH1E5_0175.rest = RH1E5_0175.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0175.s0 :: RH1E5_0175.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_021 : RS5.BandZeros RH1E5_0168.s0.t RH1E5_0175.sL.t 1016 := by
  have g168 := band_0168
  have g169 := RS5.BandZeros.glue (a := RH1E5_0168.s0.t) (b := RH1E5_0168.sL.t) (c := RH1E5_0169.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0168.s0, RH1E5_0167.sL, RH1E5_0168.sL]) (by norm_num [RS5.Sample.t, RH1E5_0168.sL, RH1E5_0169.sL]) g168 band_0169
  have g170 := RS5.BandZeros.glue (a := RH1E5_0168.s0.t) (b := RH1E5_0169.sL.t) (c := RH1E5_0170.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0168.s0, RH1E5_0167.sL, RH1E5_0169.sL]) (by norm_num [RS5.Sample.t, RH1E5_0169.sL, RH1E5_0170.sL]) g169 band_0170
  have g171 := RS5.BandZeros.glue (a := RH1E5_0168.s0.t) (b := RH1E5_0170.sL.t) (c := RH1E5_0171.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0168.s0, RH1E5_0167.sL, RH1E5_0170.sL]) (by norm_num [RS5.Sample.t, RH1E5_0170.sL, RH1E5_0171.sL]) g170 band_0171
  have g172 := RS5.BandZeros.glue (a := RH1E5_0168.s0.t) (b := RH1E5_0171.sL.t) (c := RH1E5_0172.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0168.s0, RH1E5_0167.sL, RH1E5_0171.sL]) (by norm_num [RS5.Sample.t, RH1E5_0171.sL, RH1E5_0172.sL]) g171 band_0172
  have g173 := RS5.BandZeros.glue (a := RH1E5_0168.s0.t) (b := RH1E5_0172.sL.t) (c := RH1E5_0173.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0168.s0, RH1E5_0167.sL, RH1E5_0172.sL]) (by norm_num [RS5.Sample.t, RH1E5_0172.sL, RH1E5_0173.sL]) g172 band_0173
  have g174 := RS5.BandZeros.glue (a := RH1E5_0168.s0.t) (b := RH1E5_0173.sL.t) (c := RH1E5_0174.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0168.s0, RH1E5_0167.sL, RH1E5_0173.sL]) (by norm_num [RS5.Sample.t, RH1E5_0173.sL, RH1E5_0174.sL]) g173 band_0174
  have g175 := RS5.BandZeros.glue (a := RH1E5_0168.s0.t) (b := RH1E5_0174.sL.t) (c := RH1E5_0175.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0168.s0, RH1E5_0167.sL, RH1E5_0174.sL]) (by norm_num [RS5.Sample.t, RH1E5_0174.sL, RH1E5_0175.sL]) g174 band_0175
  exact g175

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0168.s0.t RH1E5_0175.sL.t 1016 := by
  apply RH1E5.group_021 <;> assumption
