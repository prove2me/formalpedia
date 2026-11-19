-- Prove2me | solution 1 for RH1E5.group_046
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T21:35:35.791331+00:00
-- url     : https://prove2.me/submissions/efb3bfc0-ad0c-4901-a7cd-52770800b7ee

import Definitions.Def_RH1E5_Data046
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0368 : RS5.BandZeros RH1E5_0368.s0.t RH1E5_0368.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0368.s0 RH1E5_0368.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0368.s0 RH1E5_0368.rest = RH1E5_0368.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0368.s0 :: RH1E5_0368.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0369 : RS5.BandZeros RH1E5_0369.s0.t RH1E5_0369.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0369.s0 RH1E5_0369.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0369.s0 RH1E5_0369.rest = RH1E5_0369.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0369.s0 :: RH1E5_0369.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0370 : RS5.BandZeros RH1E5_0370.s0.t RH1E5_0370.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0370.s0 RH1E5_0370.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0370.s0 RH1E5_0370.rest = RH1E5_0370.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0370.s0 :: RH1E5_0370.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0371 : RS5.BandZeros RH1E5_0371.s0.t RH1E5_0371.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0371.s0 RH1E5_0371.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0371.s0 RH1E5_0371.rest = RH1E5_0371.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0371.s0 :: RH1E5_0371.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0372 : RS5.BandZeros RH1E5_0372.s0.t RH1E5_0372.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0372.s0 RH1E5_0372.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0372.s0 RH1E5_0372.rest = RH1E5_0372.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0372.s0 :: RH1E5_0372.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0373 : RS5.BandZeros RH1E5_0373.s0.t RH1E5_0373.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0373.s0 RH1E5_0373.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0373.s0 RH1E5_0373.rest = RH1E5_0373.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0373.s0 :: RH1E5_0373.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0374 : RS5.BandZeros RH1E5_0374.s0.t RH1E5_0374.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0374.s0 RH1E5_0374.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0374.s0 RH1E5_0374.rest = RH1E5_0374.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0374.s0 :: RH1E5_0374.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0375 : RS5.BandZeros RH1E5_0375.s0.t RH1E5_0375.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0375.s0 RH1E5_0375.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0375.s0 RH1E5_0375.rest = RH1E5_0375.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0375.s0 :: RH1E5_0375.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_046 : RS5.BandZeros RH1E5_0368.s0.t RH1E5_0375.sL.t 1016 := by
  have g368 := band_0368
  have g369 := RS5.BandZeros.glue (a := RH1E5_0368.s0.t) (b := RH1E5_0368.sL.t) (c := RH1E5_0369.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0368.s0, RH1E5_0367.sL, RH1E5_0368.sL]) (by norm_num [RS5.Sample.t, RH1E5_0368.sL, RH1E5_0369.sL]) g368 band_0369
  have g370 := RS5.BandZeros.glue (a := RH1E5_0368.s0.t) (b := RH1E5_0369.sL.t) (c := RH1E5_0370.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0368.s0, RH1E5_0367.sL, RH1E5_0369.sL]) (by norm_num [RS5.Sample.t, RH1E5_0369.sL, RH1E5_0370.sL]) g369 band_0370
  have g371 := RS5.BandZeros.glue (a := RH1E5_0368.s0.t) (b := RH1E5_0370.sL.t) (c := RH1E5_0371.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0368.s0, RH1E5_0367.sL, RH1E5_0370.sL]) (by norm_num [RS5.Sample.t, RH1E5_0370.sL, RH1E5_0371.sL]) g370 band_0371
  have g372 := RS5.BandZeros.glue (a := RH1E5_0368.s0.t) (b := RH1E5_0371.sL.t) (c := RH1E5_0372.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0368.s0, RH1E5_0367.sL, RH1E5_0371.sL]) (by norm_num [RS5.Sample.t, RH1E5_0371.sL, RH1E5_0372.sL]) g371 band_0372
  have g373 := RS5.BandZeros.glue (a := RH1E5_0368.s0.t) (b := RH1E5_0372.sL.t) (c := RH1E5_0373.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0368.s0, RH1E5_0367.sL, RH1E5_0372.sL]) (by norm_num [RS5.Sample.t, RH1E5_0372.sL, RH1E5_0373.sL]) g372 band_0373
  have g374 := RS5.BandZeros.glue (a := RH1E5_0368.s0.t) (b := RH1E5_0373.sL.t) (c := RH1E5_0374.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0368.s0, RH1E5_0367.sL, RH1E5_0373.sL]) (by norm_num [RS5.Sample.t, RH1E5_0373.sL, RH1E5_0374.sL]) g373 band_0374
  have g375 := RS5.BandZeros.glue (a := RH1E5_0368.s0.t) (b := RH1E5_0374.sL.t) (c := RH1E5_0375.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0368.s0, RH1E5_0367.sL, RH1E5_0374.sL]) (by norm_num [RS5.Sample.t, RH1E5_0374.sL, RH1E5_0375.sL]) g374 band_0375
  exact g375

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0368.s0.t RH1E5_0375.sL.t 1016 := by
  apply RH1E5.group_046 <;> assumption
