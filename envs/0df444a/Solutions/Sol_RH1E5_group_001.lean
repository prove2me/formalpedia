-- Prove2me | solution 1 for RH1E5.group_001
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:47:31.350595+00:00
-- url     : https://prove2.me/submissions/7a0caf6d-7b6b-49b6-9168-132b1cf944f6

import Definitions.Def_RH1E5_Data001
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0008 : RS5.BandZeros RH1E5_0008.s0.t RH1E5_0008.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0008.s0 RH1E5_0008.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0008.s0 RH1E5_0008.rest = RH1E5_0008.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0008.s0 :: RH1E5_0008.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0009 : RS5.BandZeros RH1E5_0009.s0.t RH1E5_0009.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0009.s0 RH1E5_0009.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0009.s0 RH1E5_0009.rest = RH1E5_0009.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0009.s0 :: RH1E5_0009.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0010 : RS5.BandZeros RH1E5_0010.s0.t RH1E5_0010.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0010.s0 RH1E5_0010.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0010.s0 RH1E5_0010.rest = RH1E5_0010.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0010.s0 :: RH1E5_0010.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0011 : RS5.BandZeros RH1E5_0011.s0.t RH1E5_0011.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0011.s0 RH1E5_0011.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0011.s0 RH1E5_0011.rest = RH1E5_0011.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0011.s0 :: RH1E5_0011.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0012 : RS5.BandZeros RH1E5_0012.s0.t RH1E5_0012.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0012.s0 RH1E5_0012.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0012.s0 RH1E5_0012.rest = RH1E5_0012.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0012.s0 :: RH1E5_0012.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0013 : RS5.BandZeros RH1E5_0013.s0.t RH1E5_0013.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0013.s0 RH1E5_0013.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0013.s0 RH1E5_0013.rest = RH1E5_0013.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0013.s0 :: RH1E5_0013.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0014 : RS5.BandZeros RH1E5_0014.s0.t RH1E5_0014.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0014.s0 RH1E5_0014.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0014.s0 RH1E5_0014.rest = RH1E5_0014.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0014.s0 :: RH1E5_0014.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0015 : RS5.BandZeros RH1E5_0015.s0.t RH1E5_0015.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0015.s0 RH1E5_0015.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0015.s0 RH1E5_0015.rest = RH1E5_0015.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0015.s0 :: RH1E5_0015.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_001 : RS5.BandZeros RH1E5_0008.s0.t RH1E5_0015.sL.t 1016 := by
  have g8 := band_0008
  have g9 := RS5.BandZeros.glue (a := RH1E5_0008.s0.t) (b := RH1E5_0008.sL.t) (c := RH1E5_0009.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0008.s0, RH1E5_0007.sL, RH1E5_0008.sL]) (by norm_num [RS5.Sample.t, RH1E5_0008.sL, RH1E5_0009.sL]) g8 band_0009
  have g10 := RS5.BandZeros.glue (a := RH1E5_0008.s0.t) (b := RH1E5_0009.sL.t) (c := RH1E5_0010.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0008.s0, RH1E5_0007.sL, RH1E5_0009.sL]) (by norm_num [RS5.Sample.t, RH1E5_0009.sL, RH1E5_0010.sL]) g9 band_0010
  have g11 := RS5.BandZeros.glue (a := RH1E5_0008.s0.t) (b := RH1E5_0010.sL.t) (c := RH1E5_0011.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0008.s0, RH1E5_0007.sL, RH1E5_0010.sL]) (by norm_num [RS5.Sample.t, RH1E5_0010.sL, RH1E5_0011.sL]) g10 band_0011
  have g12 := RS5.BandZeros.glue (a := RH1E5_0008.s0.t) (b := RH1E5_0011.sL.t) (c := RH1E5_0012.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0008.s0, RH1E5_0007.sL, RH1E5_0011.sL]) (by norm_num [RS5.Sample.t, RH1E5_0011.sL, RH1E5_0012.sL]) g11 band_0012
  have g13 := RS5.BandZeros.glue (a := RH1E5_0008.s0.t) (b := RH1E5_0012.sL.t) (c := RH1E5_0013.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0008.s0, RH1E5_0007.sL, RH1E5_0012.sL]) (by norm_num [RS5.Sample.t, RH1E5_0012.sL, RH1E5_0013.sL]) g12 band_0013
  have g14 := RS5.BandZeros.glue (a := RH1E5_0008.s0.t) (b := RH1E5_0013.sL.t) (c := RH1E5_0014.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0008.s0, RH1E5_0007.sL, RH1E5_0013.sL]) (by norm_num [RS5.Sample.t, RH1E5_0013.sL, RH1E5_0014.sL]) g13 band_0014
  have g15 := RS5.BandZeros.glue (a := RH1E5_0008.s0.t) (b := RH1E5_0014.sL.t) (c := RH1E5_0015.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0008.s0, RH1E5_0007.sL, RH1E5_0014.sL]) (by norm_num [RS5.Sample.t, RH1E5_0014.sL, RH1E5_0015.sL]) g14 band_0015
  exact g15

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0008.s0.t RH1E5_0015.sL.t 1016 := by
  apply RH1E5.group_001 <;> assumption
