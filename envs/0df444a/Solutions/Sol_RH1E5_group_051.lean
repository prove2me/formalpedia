-- Prove2me | solution 1 for RH1E5.group_051
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:49:33.09117+00:00
-- url     : https://prove2.me/submissions/59a11bc4-6e8c-4b47-9e3e-99e09558bdce

import Definitions.Def_RH1E5_Data051
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0408 : RS5.BandZeros RH1E5_0408.s0.t RH1E5_0408.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0408.s0 RH1E5_0408.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0408.s0 RH1E5_0408.rest = RH1E5_0408.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0408.s0 :: RH1E5_0408.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0409 : RS5.BandZeros RH1E5_0409.s0.t RH1E5_0409.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0409.s0 RH1E5_0409.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0409.s0 RH1E5_0409.rest = RH1E5_0409.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0409.s0 :: RH1E5_0409.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0410 : RS5.BandZeros RH1E5_0410.s0.t RH1E5_0410.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0410.s0 RH1E5_0410.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0410.s0 RH1E5_0410.rest = RH1E5_0410.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0410.s0 :: RH1E5_0410.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0411 : RS5.BandZeros RH1E5_0411.s0.t RH1E5_0411.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0411.s0 RH1E5_0411.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0411.s0 RH1E5_0411.rest = RH1E5_0411.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0411.s0 :: RH1E5_0411.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0412 : RS5.BandZeros RH1E5_0412.s0.t RH1E5_0412.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0412.s0 RH1E5_0412.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0412.s0 RH1E5_0412.rest = RH1E5_0412.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0412.s0 :: RH1E5_0412.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0413 : RS5.BandZeros RH1E5_0413.s0.t RH1E5_0413.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0413.s0 RH1E5_0413.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0413.s0 RH1E5_0413.rest = RH1E5_0413.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0413.s0 :: RH1E5_0413.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0414 : RS5.BandZeros RH1E5_0414.s0.t RH1E5_0414.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0414.s0 RH1E5_0414.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0414.s0 RH1E5_0414.rest = RH1E5_0414.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0414.s0 :: RH1E5_0414.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0415 : RS5.BandZeros RH1E5_0415.s0.t RH1E5_0415.sL.t 76 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0415.s0 RH1E5_0415.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0415.s0 RH1E5_0415.rest = RH1E5_0415.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0415.s0 :: RH1E5_0415.rest) = 76 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_051 : RS5.BandZeros RH1E5_0408.s0.t RH1E5_0415.sL.t 965 := by
  have g408 := band_0408
  have g409 := RS5.BandZeros.glue (a := RH1E5_0408.s0.t) (b := RH1E5_0408.sL.t) (c := RH1E5_0409.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0408.s0, RH1E5_0407.sL, RH1E5_0408.sL]) (by norm_num [RS5.Sample.t, RH1E5_0408.sL, RH1E5_0409.sL]) g408 band_0409
  have g410 := RS5.BandZeros.glue (a := RH1E5_0408.s0.t) (b := RH1E5_0409.sL.t) (c := RH1E5_0410.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0408.s0, RH1E5_0407.sL, RH1E5_0409.sL]) (by norm_num [RS5.Sample.t, RH1E5_0409.sL, RH1E5_0410.sL]) g409 band_0410
  have g411 := RS5.BandZeros.glue (a := RH1E5_0408.s0.t) (b := RH1E5_0410.sL.t) (c := RH1E5_0411.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0408.s0, RH1E5_0407.sL, RH1E5_0410.sL]) (by norm_num [RS5.Sample.t, RH1E5_0410.sL, RH1E5_0411.sL]) g410 band_0411
  have g412 := RS5.BandZeros.glue (a := RH1E5_0408.s0.t) (b := RH1E5_0411.sL.t) (c := RH1E5_0412.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0408.s0, RH1E5_0407.sL, RH1E5_0411.sL]) (by norm_num [RS5.Sample.t, RH1E5_0411.sL, RH1E5_0412.sL]) g411 band_0412
  have g413 := RS5.BandZeros.glue (a := RH1E5_0408.s0.t) (b := RH1E5_0412.sL.t) (c := RH1E5_0413.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0408.s0, RH1E5_0407.sL, RH1E5_0412.sL]) (by norm_num [RS5.Sample.t, RH1E5_0412.sL, RH1E5_0413.sL]) g412 band_0413
  have g414 := RS5.BandZeros.glue (a := RH1E5_0408.s0.t) (b := RH1E5_0413.sL.t) (c := RH1E5_0414.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0408.s0, RH1E5_0407.sL, RH1E5_0413.sL]) (by norm_num [RS5.Sample.t, RH1E5_0413.sL, RH1E5_0414.sL]) g413 band_0414
  have g415 := RS5.BandZeros.glue (a := RH1E5_0408.s0.t) (b := RH1E5_0414.sL.t) (c := RH1E5_0415.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0408.s0, RH1E5_0407.sL, RH1E5_0414.sL]) (by norm_num [RS5.Sample.t, RH1E5_0414.sL, RH1E5_0415.sL]) g414 band_0415
  exact g415

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0408.s0.t RH1E5_0415.sL.t 965 := by
  apply RH1E5.group_051 <;> assumption
