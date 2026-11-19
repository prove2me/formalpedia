-- Prove2me | solution 1 for RH1E5.group_023
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:39:11.217687+00:00
-- url     : https://prove2.me/submissions/51b76fad-e7f4-4d68-87e1-415ec52ab68b

import Definitions.Def_RH1E5_Data023
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0184 : RS5.BandZeros RH1E5_0184.s0.t RH1E5_0184.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0184.s0 RH1E5_0184.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0184.s0 RH1E5_0184.rest = RH1E5_0184.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0184.s0 :: RH1E5_0184.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0185 : RS5.BandZeros RH1E5_0185.s0.t RH1E5_0185.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0185.s0 RH1E5_0185.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0185.s0 RH1E5_0185.rest = RH1E5_0185.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0185.s0 :: RH1E5_0185.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0186 : RS5.BandZeros RH1E5_0186.s0.t RH1E5_0186.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0186.s0 RH1E5_0186.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0186.s0 RH1E5_0186.rest = RH1E5_0186.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0186.s0 :: RH1E5_0186.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0187 : RS5.BandZeros RH1E5_0187.s0.t RH1E5_0187.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0187.s0 RH1E5_0187.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0187.s0 RH1E5_0187.rest = RH1E5_0187.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0187.s0 :: RH1E5_0187.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0188 : RS5.BandZeros RH1E5_0188.s0.t RH1E5_0188.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0188.s0 RH1E5_0188.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0188.s0 RH1E5_0188.rest = RH1E5_0188.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0188.s0 :: RH1E5_0188.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0189 : RS5.BandZeros RH1E5_0189.s0.t RH1E5_0189.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0189.s0 RH1E5_0189.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0189.s0 RH1E5_0189.rest = RH1E5_0189.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0189.s0 :: RH1E5_0189.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0190 : RS5.BandZeros RH1E5_0190.s0.t RH1E5_0190.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0190.s0 RH1E5_0190.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0190.s0 RH1E5_0190.rest = RH1E5_0190.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0190.s0 :: RH1E5_0190.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0191 : RS5.BandZeros RH1E5_0191.s0.t RH1E5_0191.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0191.s0 RH1E5_0191.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0191.s0 RH1E5_0191.rest = RH1E5_0191.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0191.s0 :: RH1E5_0191.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_023 : RS5.BandZeros RH1E5_0184.s0.t RH1E5_0191.sL.t 1016 := by
  have g184 := band_0184
  have g185 := RS5.BandZeros.glue (a := RH1E5_0184.s0.t) (b := RH1E5_0184.sL.t) (c := RH1E5_0185.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0184.s0, RH1E5_0183.sL, RH1E5_0184.sL]) (by norm_num [RS5.Sample.t, RH1E5_0184.sL, RH1E5_0185.sL]) g184 band_0185
  have g186 := RS5.BandZeros.glue (a := RH1E5_0184.s0.t) (b := RH1E5_0185.sL.t) (c := RH1E5_0186.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0184.s0, RH1E5_0183.sL, RH1E5_0185.sL]) (by norm_num [RS5.Sample.t, RH1E5_0185.sL, RH1E5_0186.sL]) g185 band_0186
  have g187 := RS5.BandZeros.glue (a := RH1E5_0184.s0.t) (b := RH1E5_0186.sL.t) (c := RH1E5_0187.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0184.s0, RH1E5_0183.sL, RH1E5_0186.sL]) (by norm_num [RS5.Sample.t, RH1E5_0186.sL, RH1E5_0187.sL]) g186 band_0187
  have g188 := RS5.BandZeros.glue (a := RH1E5_0184.s0.t) (b := RH1E5_0187.sL.t) (c := RH1E5_0188.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0184.s0, RH1E5_0183.sL, RH1E5_0187.sL]) (by norm_num [RS5.Sample.t, RH1E5_0187.sL, RH1E5_0188.sL]) g187 band_0188
  have g189 := RS5.BandZeros.glue (a := RH1E5_0184.s0.t) (b := RH1E5_0188.sL.t) (c := RH1E5_0189.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0184.s0, RH1E5_0183.sL, RH1E5_0188.sL]) (by norm_num [RS5.Sample.t, RH1E5_0188.sL, RH1E5_0189.sL]) g188 band_0189
  have g190 := RS5.BandZeros.glue (a := RH1E5_0184.s0.t) (b := RH1E5_0189.sL.t) (c := RH1E5_0190.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0184.s0, RH1E5_0183.sL, RH1E5_0189.sL]) (by norm_num [RS5.Sample.t, RH1E5_0189.sL, RH1E5_0190.sL]) g189 band_0190
  have g191 := RS5.BandZeros.glue (a := RH1E5_0184.s0.t) (b := RH1E5_0190.sL.t) (c := RH1E5_0191.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0184.s0, RH1E5_0183.sL, RH1E5_0190.sL]) (by norm_num [RS5.Sample.t, RH1E5_0190.sL, RH1E5_0191.sL]) g190 band_0191
  exact g191

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0184.s0.t RH1E5_0191.sL.t 1016 := by
  apply RH1E5.group_023 <;> assumption
