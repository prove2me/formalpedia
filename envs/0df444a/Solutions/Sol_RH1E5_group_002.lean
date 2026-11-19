-- Prove2me | solution 1 for RH1E5.group_002
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:48:58.970277+00:00
-- url     : https://prove2.me/submissions/2593f9d3-8237-4298-bc5f-31a570873ef5

import Definitions.Def_RH1E5_Data002
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0016 : RS5.BandZeros RH1E5_0016.s0.t RH1E5_0016.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0016.s0 RH1E5_0016.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0016.s0 RH1E5_0016.rest = RH1E5_0016.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0016.s0 :: RH1E5_0016.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0017 : RS5.BandZeros RH1E5_0017.s0.t RH1E5_0017.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0017.s0 RH1E5_0017.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0017.s0 RH1E5_0017.rest = RH1E5_0017.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0017.s0 :: RH1E5_0017.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0018 : RS5.BandZeros RH1E5_0018.s0.t RH1E5_0018.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0018.s0 RH1E5_0018.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0018.s0 RH1E5_0018.rest = RH1E5_0018.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0018.s0 :: RH1E5_0018.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0019 : RS5.BandZeros RH1E5_0019.s0.t RH1E5_0019.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0019.s0 RH1E5_0019.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0019.s0 RH1E5_0019.rest = RH1E5_0019.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0019.s0 :: RH1E5_0019.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0020 : RS5.BandZeros RH1E5_0020.s0.t RH1E5_0020.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0020.s0 RH1E5_0020.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0020.s0 RH1E5_0020.rest = RH1E5_0020.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0020.s0 :: RH1E5_0020.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0021 : RS5.BandZeros RH1E5_0021.s0.t RH1E5_0021.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0021.s0 RH1E5_0021.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0021.s0 RH1E5_0021.rest = RH1E5_0021.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0021.s0 :: RH1E5_0021.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0022 : RS5.BandZeros RH1E5_0022.s0.t RH1E5_0022.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0022.s0 RH1E5_0022.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0022.s0 RH1E5_0022.rest = RH1E5_0022.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0022.s0 :: RH1E5_0022.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0023 : RS5.BandZeros RH1E5_0023.s0.t RH1E5_0023.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0023.s0 RH1E5_0023.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0023.s0 RH1E5_0023.rest = RH1E5_0023.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0023.s0 :: RH1E5_0023.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_002 : RS5.BandZeros RH1E5_0016.s0.t RH1E5_0023.sL.t 1016 := by
  have g16 := band_0016
  have g17 := RS5.BandZeros.glue (a := RH1E5_0016.s0.t) (b := RH1E5_0016.sL.t) (c := RH1E5_0017.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0016.s0, RH1E5_0015.sL, RH1E5_0016.sL]) (by norm_num [RS5.Sample.t, RH1E5_0016.sL, RH1E5_0017.sL]) g16 band_0017
  have g18 := RS5.BandZeros.glue (a := RH1E5_0016.s0.t) (b := RH1E5_0017.sL.t) (c := RH1E5_0018.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0016.s0, RH1E5_0015.sL, RH1E5_0017.sL]) (by norm_num [RS5.Sample.t, RH1E5_0017.sL, RH1E5_0018.sL]) g17 band_0018
  have g19 := RS5.BandZeros.glue (a := RH1E5_0016.s0.t) (b := RH1E5_0018.sL.t) (c := RH1E5_0019.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0016.s0, RH1E5_0015.sL, RH1E5_0018.sL]) (by norm_num [RS5.Sample.t, RH1E5_0018.sL, RH1E5_0019.sL]) g18 band_0019
  have g20 := RS5.BandZeros.glue (a := RH1E5_0016.s0.t) (b := RH1E5_0019.sL.t) (c := RH1E5_0020.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0016.s0, RH1E5_0015.sL, RH1E5_0019.sL]) (by norm_num [RS5.Sample.t, RH1E5_0019.sL, RH1E5_0020.sL]) g19 band_0020
  have g21 := RS5.BandZeros.glue (a := RH1E5_0016.s0.t) (b := RH1E5_0020.sL.t) (c := RH1E5_0021.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0016.s0, RH1E5_0015.sL, RH1E5_0020.sL]) (by norm_num [RS5.Sample.t, RH1E5_0020.sL, RH1E5_0021.sL]) g20 band_0021
  have g22 := RS5.BandZeros.glue (a := RH1E5_0016.s0.t) (b := RH1E5_0021.sL.t) (c := RH1E5_0022.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0016.s0, RH1E5_0015.sL, RH1E5_0021.sL]) (by norm_num [RS5.Sample.t, RH1E5_0021.sL, RH1E5_0022.sL]) g21 band_0022
  have g23 := RS5.BandZeros.glue (a := RH1E5_0016.s0.t) (b := RH1E5_0022.sL.t) (c := RH1E5_0023.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0016.s0, RH1E5_0015.sL, RH1E5_0022.sL]) (by norm_num [RS5.Sample.t, RH1E5_0022.sL, RH1E5_0023.sL]) g22 band_0023
  exact g23

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0016.s0.t RH1E5_0023.sL.t 1016 := by
  apply RH1E5.group_002 <;> assumption
