-- Prove2me | solution 1 for RH1E5.group_048
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:41:53.917114+00:00
-- url     : https://prove2.me/submissions/7dcd2475-b0e4-40f5-a900-20d3da1646a2

import Definitions.Def_RH1E5_Data048
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0384 : RS5.BandZeros RH1E5_0384.s0.t RH1E5_0384.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0384.s0 RH1E5_0384.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0384.s0 RH1E5_0384.rest = RH1E5_0384.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0384.s0 :: RH1E5_0384.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0385 : RS5.BandZeros RH1E5_0385.s0.t RH1E5_0385.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0385.s0 RH1E5_0385.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0385.s0 RH1E5_0385.rest = RH1E5_0385.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0385.s0 :: RH1E5_0385.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0386 : RS5.BandZeros RH1E5_0386.s0.t RH1E5_0386.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0386.s0 RH1E5_0386.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0386.s0 RH1E5_0386.rest = RH1E5_0386.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0386.s0 :: RH1E5_0386.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0387 : RS5.BandZeros RH1E5_0387.s0.t RH1E5_0387.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0387.s0 RH1E5_0387.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0387.s0 RH1E5_0387.rest = RH1E5_0387.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0387.s0 :: RH1E5_0387.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0388 : RS5.BandZeros RH1E5_0388.s0.t RH1E5_0388.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0388.s0 RH1E5_0388.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0388.s0 RH1E5_0388.rest = RH1E5_0388.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0388.s0 :: RH1E5_0388.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0389 : RS5.BandZeros RH1E5_0389.s0.t RH1E5_0389.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0389.s0 RH1E5_0389.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0389.s0 RH1E5_0389.rest = RH1E5_0389.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0389.s0 :: RH1E5_0389.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0390 : RS5.BandZeros RH1E5_0390.s0.t RH1E5_0390.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0390.s0 RH1E5_0390.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0390.s0 RH1E5_0390.rest = RH1E5_0390.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0390.s0 :: RH1E5_0390.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0391 : RS5.BandZeros RH1E5_0391.s0.t RH1E5_0391.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0391.s0 RH1E5_0391.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0391.s0 RH1E5_0391.rest = RH1E5_0391.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0391.s0 :: RH1E5_0391.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_048 : RS5.BandZeros RH1E5_0384.s0.t RH1E5_0391.sL.t 1016 := by
  have g384 := band_0384
  have g385 := RS5.BandZeros.glue (a := RH1E5_0384.s0.t) (b := RH1E5_0384.sL.t) (c := RH1E5_0385.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0384.s0, RH1E5_0383.sL, RH1E5_0384.sL]) (by norm_num [RS5.Sample.t, RH1E5_0384.sL, RH1E5_0385.sL]) g384 band_0385
  have g386 := RS5.BandZeros.glue (a := RH1E5_0384.s0.t) (b := RH1E5_0385.sL.t) (c := RH1E5_0386.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0384.s0, RH1E5_0383.sL, RH1E5_0385.sL]) (by norm_num [RS5.Sample.t, RH1E5_0385.sL, RH1E5_0386.sL]) g385 band_0386
  have g387 := RS5.BandZeros.glue (a := RH1E5_0384.s0.t) (b := RH1E5_0386.sL.t) (c := RH1E5_0387.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0384.s0, RH1E5_0383.sL, RH1E5_0386.sL]) (by norm_num [RS5.Sample.t, RH1E5_0386.sL, RH1E5_0387.sL]) g386 band_0387
  have g388 := RS5.BandZeros.glue (a := RH1E5_0384.s0.t) (b := RH1E5_0387.sL.t) (c := RH1E5_0388.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0384.s0, RH1E5_0383.sL, RH1E5_0387.sL]) (by norm_num [RS5.Sample.t, RH1E5_0387.sL, RH1E5_0388.sL]) g387 band_0388
  have g389 := RS5.BandZeros.glue (a := RH1E5_0384.s0.t) (b := RH1E5_0388.sL.t) (c := RH1E5_0389.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0384.s0, RH1E5_0383.sL, RH1E5_0388.sL]) (by norm_num [RS5.Sample.t, RH1E5_0388.sL, RH1E5_0389.sL]) g388 band_0389
  have g390 := RS5.BandZeros.glue (a := RH1E5_0384.s0.t) (b := RH1E5_0389.sL.t) (c := RH1E5_0390.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0384.s0, RH1E5_0383.sL, RH1E5_0389.sL]) (by norm_num [RS5.Sample.t, RH1E5_0389.sL, RH1E5_0390.sL]) g389 band_0390
  have g391 := RS5.BandZeros.glue (a := RH1E5_0384.s0.t) (b := RH1E5_0390.sL.t) (c := RH1E5_0391.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0384.s0, RH1E5_0383.sL, RH1E5_0390.sL]) (by norm_num [RS5.Sample.t, RH1E5_0390.sL, RH1E5_0391.sL]) g390 band_0391
  exact g391

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0384.s0.t RH1E5_0391.sL.t 1016 := by
  apply RH1E5.group_048 <;> assumption
