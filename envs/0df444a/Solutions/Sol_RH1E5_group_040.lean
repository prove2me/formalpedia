-- Prove2me | solution 1 for RH1E5.group_040
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:24:05.731318+00:00
-- url     : https://prove2.me/submissions/2b96b17d-b641-4bb3-a7f8-a7a4c840a24b

import Definitions.Def_RH1E5_Data040
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0320 : RS5.BandZeros RH1E5_0320.s0.t RH1E5_0320.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0320.s0 RH1E5_0320.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0320.s0 RH1E5_0320.rest = RH1E5_0320.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0320.s0 :: RH1E5_0320.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0321 : RS5.BandZeros RH1E5_0321.s0.t RH1E5_0321.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0321.s0 RH1E5_0321.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0321.s0 RH1E5_0321.rest = RH1E5_0321.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0321.s0 :: RH1E5_0321.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0322 : RS5.BandZeros RH1E5_0322.s0.t RH1E5_0322.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0322.s0 RH1E5_0322.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0322.s0 RH1E5_0322.rest = RH1E5_0322.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0322.s0 :: RH1E5_0322.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0323 : RS5.BandZeros RH1E5_0323.s0.t RH1E5_0323.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0323.s0 RH1E5_0323.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0323.s0 RH1E5_0323.rest = RH1E5_0323.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0323.s0 :: RH1E5_0323.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0324 : RS5.BandZeros RH1E5_0324.s0.t RH1E5_0324.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0324.s0 RH1E5_0324.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0324.s0 RH1E5_0324.rest = RH1E5_0324.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0324.s0 :: RH1E5_0324.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0325 : RS5.BandZeros RH1E5_0325.s0.t RH1E5_0325.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0325.s0 RH1E5_0325.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0325.s0 RH1E5_0325.rest = RH1E5_0325.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0325.s0 :: RH1E5_0325.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0326 : RS5.BandZeros RH1E5_0326.s0.t RH1E5_0326.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0326.s0 RH1E5_0326.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0326.s0 RH1E5_0326.rest = RH1E5_0326.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0326.s0 :: RH1E5_0326.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0327 : RS5.BandZeros RH1E5_0327.s0.t RH1E5_0327.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0327.s0 RH1E5_0327.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0327.s0 RH1E5_0327.rest = RH1E5_0327.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0327.s0 :: RH1E5_0327.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_040 : RS5.BandZeros RH1E5_0320.s0.t RH1E5_0327.sL.t 1016 := by
  have g320 := band_0320
  have g321 := RS5.BandZeros.glue (a := RH1E5_0320.s0.t) (b := RH1E5_0320.sL.t) (c := RH1E5_0321.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0320.s0, RH1E5_0319.sL, RH1E5_0320.sL]) (by norm_num [RS5.Sample.t, RH1E5_0320.sL, RH1E5_0321.sL]) g320 band_0321
  have g322 := RS5.BandZeros.glue (a := RH1E5_0320.s0.t) (b := RH1E5_0321.sL.t) (c := RH1E5_0322.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0320.s0, RH1E5_0319.sL, RH1E5_0321.sL]) (by norm_num [RS5.Sample.t, RH1E5_0321.sL, RH1E5_0322.sL]) g321 band_0322
  have g323 := RS5.BandZeros.glue (a := RH1E5_0320.s0.t) (b := RH1E5_0322.sL.t) (c := RH1E5_0323.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0320.s0, RH1E5_0319.sL, RH1E5_0322.sL]) (by norm_num [RS5.Sample.t, RH1E5_0322.sL, RH1E5_0323.sL]) g322 band_0323
  have g324 := RS5.BandZeros.glue (a := RH1E5_0320.s0.t) (b := RH1E5_0323.sL.t) (c := RH1E5_0324.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0320.s0, RH1E5_0319.sL, RH1E5_0323.sL]) (by norm_num [RS5.Sample.t, RH1E5_0323.sL, RH1E5_0324.sL]) g323 band_0324
  have g325 := RS5.BandZeros.glue (a := RH1E5_0320.s0.t) (b := RH1E5_0324.sL.t) (c := RH1E5_0325.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0320.s0, RH1E5_0319.sL, RH1E5_0324.sL]) (by norm_num [RS5.Sample.t, RH1E5_0324.sL, RH1E5_0325.sL]) g324 band_0325
  have g326 := RS5.BandZeros.glue (a := RH1E5_0320.s0.t) (b := RH1E5_0325.sL.t) (c := RH1E5_0326.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0320.s0, RH1E5_0319.sL, RH1E5_0325.sL]) (by norm_num [RS5.Sample.t, RH1E5_0325.sL, RH1E5_0326.sL]) g325 band_0326
  have g327 := RS5.BandZeros.glue (a := RH1E5_0320.s0.t) (b := RH1E5_0326.sL.t) (c := RH1E5_0327.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0320.s0, RH1E5_0319.sL, RH1E5_0326.sL]) (by norm_num [RS5.Sample.t, RH1E5_0326.sL, RH1E5_0327.sL]) g326 band_0327
  exact g327

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0320.s0.t RH1E5_0327.sL.t 1016 := by
  apply RH1E5.group_040 <;> assumption
