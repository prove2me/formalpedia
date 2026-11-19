-- Prove2me | solution 1 for RH1E5.group_028
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:51:39.412014+00:00
-- url     : https://prove2.me/submissions/9710cb77-6117-4669-9ed7-08a28ef286bc

import Definitions.Def_RH1E5_Data028
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0224 : RS5.BandZeros RH1E5_0224.s0.t RH1E5_0224.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0224.s0 RH1E5_0224.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0224.s0 RH1E5_0224.rest = RH1E5_0224.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0224.s0 :: RH1E5_0224.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0225 : RS5.BandZeros RH1E5_0225.s0.t RH1E5_0225.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0225.s0 RH1E5_0225.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0225.s0 RH1E5_0225.rest = RH1E5_0225.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0225.s0 :: RH1E5_0225.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0226 : RS5.BandZeros RH1E5_0226.s0.t RH1E5_0226.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0226.s0 RH1E5_0226.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0226.s0 RH1E5_0226.rest = RH1E5_0226.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0226.s0 :: RH1E5_0226.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0227 : RS5.BandZeros RH1E5_0227.s0.t RH1E5_0227.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0227.s0 RH1E5_0227.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0227.s0 RH1E5_0227.rest = RH1E5_0227.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0227.s0 :: RH1E5_0227.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0228 : RS5.BandZeros RH1E5_0228.s0.t RH1E5_0228.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0228.s0 RH1E5_0228.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0228.s0 RH1E5_0228.rest = RH1E5_0228.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0228.s0 :: RH1E5_0228.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0229 : RS5.BandZeros RH1E5_0229.s0.t RH1E5_0229.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0229.s0 RH1E5_0229.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0229.s0 RH1E5_0229.rest = RH1E5_0229.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0229.s0 :: RH1E5_0229.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0230 : RS5.BandZeros RH1E5_0230.s0.t RH1E5_0230.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0230.s0 RH1E5_0230.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0230.s0 RH1E5_0230.rest = RH1E5_0230.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0230.s0 :: RH1E5_0230.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0231 : RS5.BandZeros RH1E5_0231.s0.t RH1E5_0231.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0231.s0 RH1E5_0231.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0231.s0 RH1E5_0231.rest = RH1E5_0231.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0231.s0 :: RH1E5_0231.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_028 : RS5.BandZeros RH1E5_0224.s0.t RH1E5_0231.sL.t 1016 := by
  have g224 := band_0224
  have g225 := RS5.BandZeros.glue (a := RH1E5_0224.s0.t) (b := RH1E5_0224.sL.t) (c := RH1E5_0225.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0224.s0, RH1E5_0223.sL, RH1E5_0224.sL]) (by norm_num [RS5.Sample.t, RH1E5_0224.sL, RH1E5_0225.sL]) g224 band_0225
  have g226 := RS5.BandZeros.glue (a := RH1E5_0224.s0.t) (b := RH1E5_0225.sL.t) (c := RH1E5_0226.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0224.s0, RH1E5_0223.sL, RH1E5_0225.sL]) (by norm_num [RS5.Sample.t, RH1E5_0225.sL, RH1E5_0226.sL]) g225 band_0226
  have g227 := RS5.BandZeros.glue (a := RH1E5_0224.s0.t) (b := RH1E5_0226.sL.t) (c := RH1E5_0227.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0224.s0, RH1E5_0223.sL, RH1E5_0226.sL]) (by norm_num [RS5.Sample.t, RH1E5_0226.sL, RH1E5_0227.sL]) g226 band_0227
  have g228 := RS5.BandZeros.glue (a := RH1E5_0224.s0.t) (b := RH1E5_0227.sL.t) (c := RH1E5_0228.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0224.s0, RH1E5_0223.sL, RH1E5_0227.sL]) (by norm_num [RS5.Sample.t, RH1E5_0227.sL, RH1E5_0228.sL]) g227 band_0228
  have g229 := RS5.BandZeros.glue (a := RH1E5_0224.s0.t) (b := RH1E5_0228.sL.t) (c := RH1E5_0229.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0224.s0, RH1E5_0223.sL, RH1E5_0228.sL]) (by norm_num [RS5.Sample.t, RH1E5_0228.sL, RH1E5_0229.sL]) g228 band_0229
  have g230 := RS5.BandZeros.glue (a := RH1E5_0224.s0.t) (b := RH1E5_0229.sL.t) (c := RH1E5_0230.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0224.s0, RH1E5_0223.sL, RH1E5_0229.sL]) (by norm_num [RS5.Sample.t, RH1E5_0229.sL, RH1E5_0230.sL]) g229 band_0230
  have g231 := RS5.BandZeros.glue (a := RH1E5_0224.s0.t) (b := RH1E5_0230.sL.t) (c := RH1E5_0231.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0224.s0, RH1E5_0223.sL, RH1E5_0230.sL]) (by norm_num [RS5.Sample.t, RH1E5_0230.sL, RH1E5_0231.sL]) g230 band_0231
  exact g231

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0224.s0.t RH1E5_0231.sL.t 1016 := by
  apply RH1E5.group_028 <;> assumption
