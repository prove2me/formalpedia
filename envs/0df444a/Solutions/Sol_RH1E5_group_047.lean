-- Prove2me | solution 1 for RH1E5.group_047
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:39:20.29709+00:00
-- url     : https://prove2.me/submissions/6e433662-541d-4b8e-b891-7fa523b680a9

import Definitions.Def_RH1E5_Data047
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0376 : RS5.BandZeros RH1E5_0376.s0.t RH1E5_0376.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0376.s0 RH1E5_0376.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0376.s0 RH1E5_0376.rest = RH1E5_0376.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0376.s0 :: RH1E5_0376.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0377 : RS5.BandZeros RH1E5_0377.s0.t RH1E5_0377.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0377.s0 RH1E5_0377.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0377.s0 RH1E5_0377.rest = RH1E5_0377.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0377.s0 :: RH1E5_0377.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0378 : RS5.BandZeros RH1E5_0378.s0.t RH1E5_0378.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0378.s0 RH1E5_0378.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0378.s0 RH1E5_0378.rest = RH1E5_0378.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0378.s0 :: RH1E5_0378.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0379 : RS5.BandZeros RH1E5_0379.s0.t RH1E5_0379.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0379.s0 RH1E5_0379.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0379.s0 RH1E5_0379.rest = RH1E5_0379.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0379.s0 :: RH1E5_0379.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0380 : RS5.BandZeros RH1E5_0380.s0.t RH1E5_0380.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0380.s0 RH1E5_0380.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0380.s0 RH1E5_0380.rest = RH1E5_0380.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0380.s0 :: RH1E5_0380.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0381 : RS5.BandZeros RH1E5_0381.s0.t RH1E5_0381.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0381.s0 RH1E5_0381.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0381.s0 RH1E5_0381.rest = RH1E5_0381.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0381.s0 :: RH1E5_0381.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0382 : RS5.BandZeros RH1E5_0382.s0.t RH1E5_0382.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0382.s0 RH1E5_0382.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0382.s0 RH1E5_0382.rest = RH1E5_0382.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0382.s0 :: RH1E5_0382.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0383 : RS5.BandZeros RH1E5_0383.s0.t RH1E5_0383.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0383.s0 RH1E5_0383.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0383.s0 RH1E5_0383.rest = RH1E5_0383.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0383.s0 :: RH1E5_0383.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_047 : RS5.BandZeros RH1E5_0376.s0.t RH1E5_0383.sL.t 1016 := by
  have g376 := band_0376
  have g377 := RS5.BandZeros.glue (a := RH1E5_0376.s0.t) (b := RH1E5_0376.sL.t) (c := RH1E5_0377.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0376.s0, RH1E5_0375.sL, RH1E5_0376.sL]) (by norm_num [RS5.Sample.t, RH1E5_0376.sL, RH1E5_0377.sL]) g376 band_0377
  have g378 := RS5.BandZeros.glue (a := RH1E5_0376.s0.t) (b := RH1E5_0377.sL.t) (c := RH1E5_0378.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0376.s0, RH1E5_0375.sL, RH1E5_0377.sL]) (by norm_num [RS5.Sample.t, RH1E5_0377.sL, RH1E5_0378.sL]) g377 band_0378
  have g379 := RS5.BandZeros.glue (a := RH1E5_0376.s0.t) (b := RH1E5_0378.sL.t) (c := RH1E5_0379.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0376.s0, RH1E5_0375.sL, RH1E5_0378.sL]) (by norm_num [RS5.Sample.t, RH1E5_0378.sL, RH1E5_0379.sL]) g378 band_0379
  have g380 := RS5.BandZeros.glue (a := RH1E5_0376.s0.t) (b := RH1E5_0379.sL.t) (c := RH1E5_0380.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0376.s0, RH1E5_0375.sL, RH1E5_0379.sL]) (by norm_num [RS5.Sample.t, RH1E5_0379.sL, RH1E5_0380.sL]) g379 band_0380
  have g381 := RS5.BandZeros.glue (a := RH1E5_0376.s0.t) (b := RH1E5_0380.sL.t) (c := RH1E5_0381.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0376.s0, RH1E5_0375.sL, RH1E5_0380.sL]) (by norm_num [RS5.Sample.t, RH1E5_0380.sL, RH1E5_0381.sL]) g380 band_0381
  have g382 := RS5.BandZeros.glue (a := RH1E5_0376.s0.t) (b := RH1E5_0381.sL.t) (c := RH1E5_0382.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0376.s0, RH1E5_0375.sL, RH1E5_0381.sL]) (by norm_num [RS5.Sample.t, RH1E5_0381.sL, RH1E5_0382.sL]) g381 band_0382
  have g383 := RS5.BandZeros.glue (a := RH1E5_0376.s0.t) (b := RH1E5_0382.sL.t) (c := RH1E5_0383.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0376.s0, RH1E5_0375.sL, RH1E5_0382.sL]) (by norm_num [RS5.Sample.t, RH1E5_0382.sL, RH1E5_0383.sL]) g382 band_0383
  exact g383

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0376.s0.t RH1E5_0383.sL.t 1016 := by
  apply RH1E5.group_047 <;> assumption
