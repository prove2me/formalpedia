-- Prove2me | solution 1 for RH1E5.group_000
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:47:29.32701+00:00
-- url     : https://prove2.me/submissions/df446314-083e-4b23-ab67-8c6d2ce35e59

import Definitions.Def_RH1E5_Data000
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0000 : RS5.BandZeros RH1E5_0000.s0.t RH1E5_0000.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0000.s0 RH1E5_0000.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0000.s0 RH1E5_0000.rest = RH1E5_0000.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0000.s0 :: RH1E5_0000.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0001 : RS5.BandZeros RH1E5_0001.s0.t RH1E5_0001.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0001.s0 RH1E5_0001.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0001.s0 RH1E5_0001.rest = RH1E5_0001.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0001.s0 :: RH1E5_0001.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0002 : RS5.BandZeros RH1E5_0002.s0.t RH1E5_0002.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0002.s0 RH1E5_0002.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0002.s0 RH1E5_0002.rest = RH1E5_0002.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0002.s0 :: RH1E5_0002.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0003 : RS5.BandZeros RH1E5_0003.s0.t RH1E5_0003.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0003.s0 RH1E5_0003.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0003.s0 RH1E5_0003.rest = RH1E5_0003.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0003.s0 :: RH1E5_0003.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0004 : RS5.BandZeros RH1E5_0004.s0.t RH1E5_0004.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0004.s0 RH1E5_0004.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0004.s0 RH1E5_0004.rest = RH1E5_0004.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0004.s0 :: RH1E5_0004.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0005 : RS5.BandZeros RH1E5_0005.s0.t RH1E5_0005.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0005.s0 RH1E5_0005.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0005.s0 RH1E5_0005.rest = RH1E5_0005.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0005.s0 :: RH1E5_0005.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0006 : RS5.BandZeros RH1E5_0006.s0.t RH1E5_0006.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0006.s0 RH1E5_0006.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0006.s0 RH1E5_0006.rest = RH1E5_0006.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0006.s0 :: RH1E5_0006.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0007 : RS5.BandZeros RH1E5_0007.s0.t RH1E5_0007.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0007.s0 RH1E5_0007.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0007.s0 RH1E5_0007.rest = RH1E5_0007.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0007.s0 :: RH1E5_0007.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_000 : RS5.BandZeros RH1E5_0000.s0.t RH1E5_0007.sL.t 1016 := by
  have g0 := band_0000
  have g1 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0000.sL.t) (c := RH1E5_0001.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0000.sL]) (by norm_num [RS5.Sample.t, RH1E5_0000.sL, RH1E5_0001.sL]) g0 band_0001
  have g2 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0001.sL.t) (c := RH1E5_0002.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0001.sL]) (by norm_num [RS5.Sample.t, RH1E5_0001.sL, RH1E5_0002.sL]) g1 band_0002
  have g3 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0002.sL.t) (c := RH1E5_0003.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0002.sL]) (by norm_num [RS5.Sample.t, RH1E5_0002.sL, RH1E5_0003.sL]) g2 band_0003
  have g4 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0003.sL.t) (c := RH1E5_0004.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0003.sL]) (by norm_num [RS5.Sample.t, RH1E5_0003.sL, RH1E5_0004.sL]) g3 band_0004
  have g5 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0004.sL.t) (c := RH1E5_0005.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0004.sL]) (by norm_num [RS5.Sample.t, RH1E5_0004.sL, RH1E5_0005.sL]) g4 band_0005
  have g6 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0005.sL.t) (c := RH1E5_0006.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0005.sL]) (by norm_num [RS5.Sample.t, RH1E5_0005.sL, RH1E5_0006.sL]) g5 band_0006
  have g7 := RS5.BandZeros.glue (a := RH1E5_0000.s0.t) (b := RH1E5_0006.sL.t) (c := RH1E5_0007.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0000.s0, RH1E5_0006.sL]) (by norm_num [RS5.Sample.t, RH1E5_0006.sL, RH1E5_0007.sL]) g6 band_0007
  exact g7

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0000.s0.t RH1E5_0007.sL.t 1016 := by
  apply RH1E5.group_000 <;> assumption
