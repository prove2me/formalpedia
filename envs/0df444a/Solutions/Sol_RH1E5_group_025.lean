-- Prove2me | solution 1 for RH1E5.group_025
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:45:23.294745+00:00
-- url     : https://prove2.me/submissions/32fb91e4-4353-4da8-b9e4-12e725c0eec9

import Definitions.Def_RH1E5_Data025
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0200 : RS5.BandZeros RH1E5_0200.s0.t RH1E5_0200.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0200.s0 RH1E5_0200.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0200.s0 RH1E5_0200.rest = RH1E5_0200.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0200.s0 :: RH1E5_0200.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0201 : RS5.BandZeros RH1E5_0201.s0.t RH1E5_0201.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0201.s0 RH1E5_0201.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0201.s0 RH1E5_0201.rest = RH1E5_0201.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0201.s0 :: RH1E5_0201.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0202 : RS5.BandZeros RH1E5_0202.s0.t RH1E5_0202.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0202.s0 RH1E5_0202.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0202.s0 RH1E5_0202.rest = RH1E5_0202.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0202.s0 :: RH1E5_0202.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0203 : RS5.BandZeros RH1E5_0203.s0.t RH1E5_0203.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0203.s0 RH1E5_0203.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0203.s0 RH1E5_0203.rest = RH1E5_0203.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0203.s0 :: RH1E5_0203.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0204 : RS5.BandZeros RH1E5_0204.s0.t RH1E5_0204.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0204.s0 RH1E5_0204.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0204.s0 RH1E5_0204.rest = RH1E5_0204.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0204.s0 :: RH1E5_0204.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0205 : RS5.BandZeros RH1E5_0205.s0.t RH1E5_0205.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0205.s0 RH1E5_0205.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0205.s0 RH1E5_0205.rest = RH1E5_0205.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0205.s0 :: RH1E5_0205.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0206 : RS5.BandZeros RH1E5_0206.s0.t RH1E5_0206.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0206.s0 RH1E5_0206.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0206.s0 RH1E5_0206.rest = RH1E5_0206.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0206.s0 :: RH1E5_0206.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0207 : RS5.BandZeros RH1E5_0207.s0.t RH1E5_0207.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0207.s0 RH1E5_0207.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0207.s0 RH1E5_0207.rest = RH1E5_0207.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0207.s0 :: RH1E5_0207.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_025 : RS5.BandZeros RH1E5_0200.s0.t RH1E5_0207.sL.t 1016 := by
  have g200 := band_0200
  have g201 := RS5.BandZeros.glue (a := RH1E5_0200.s0.t) (b := RH1E5_0200.sL.t) (c := RH1E5_0201.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0200.s0, RH1E5_0199.sL, RH1E5_0200.sL]) (by norm_num [RS5.Sample.t, RH1E5_0200.sL, RH1E5_0201.sL]) g200 band_0201
  have g202 := RS5.BandZeros.glue (a := RH1E5_0200.s0.t) (b := RH1E5_0201.sL.t) (c := RH1E5_0202.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0200.s0, RH1E5_0199.sL, RH1E5_0201.sL]) (by norm_num [RS5.Sample.t, RH1E5_0201.sL, RH1E5_0202.sL]) g201 band_0202
  have g203 := RS5.BandZeros.glue (a := RH1E5_0200.s0.t) (b := RH1E5_0202.sL.t) (c := RH1E5_0203.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0200.s0, RH1E5_0199.sL, RH1E5_0202.sL]) (by norm_num [RS5.Sample.t, RH1E5_0202.sL, RH1E5_0203.sL]) g202 band_0203
  have g204 := RS5.BandZeros.glue (a := RH1E5_0200.s0.t) (b := RH1E5_0203.sL.t) (c := RH1E5_0204.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0200.s0, RH1E5_0199.sL, RH1E5_0203.sL]) (by norm_num [RS5.Sample.t, RH1E5_0203.sL, RH1E5_0204.sL]) g203 band_0204
  have g205 := RS5.BandZeros.glue (a := RH1E5_0200.s0.t) (b := RH1E5_0204.sL.t) (c := RH1E5_0205.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0200.s0, RH1E5_0199.sL, RH1E5_0204.sL]) (by norm_num [RS5.Sample.t, RH1E5_0204.sL, RH1E5_0205.sL]) g204 band_0205
  have g206 := RS5.BandZeros.glue (a := RH1E5_0200.s0.t) (b := RH1E5_0205.sL.t) (c := RH1E5_0206.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0200.s0, RH1E5_0199.sL, RH1E5_0205.sL]) (by norm_num [RS5.Sample.t, RH1E5_0205.sL, RH1E5_0206.sL]) g205 band_0206
  have g207 := RS5.BandZeros.glue (a := RH1E5_0200.s0.t) (b := RH1E5_0206.sL.t) (c := RH1E5_0207.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0200.s0, RH1E5_0199.sL, RH1E5_0206.sL]) (by norm_num [RS5.Sample.t, RH1E5_0206.sL, RH1E5_0207.sL]) g206 band_0207
  exact g207

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0200.s0.t RH1E5_0207.sL.t 1016 := by
  apply RH1E5.group_025 <;> assumption
