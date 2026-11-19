-- Prove2me | solution 1 for RH1E5.group_005
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:56:44.291922+00:00
-- url     : https://prove2.me/submissions/459005ab-9be1-475c-a15a-e268be76e975

import Definitions.Def_RH1E5_Data005
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0040 : RS5.BandZeros RH1E5_0040.s0.t RH1E5_0040.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0040.s0 RH1E5_0040.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0040.s0 RH1E5_0040.rest = RH1E5_0040.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0040.s0 :: RH1E5_0040.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0041 : RS5.BandZeros RH1E5_0041.s0.t RH1E5_0041.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0041.s0 RH1E5_0041.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0041.s0 RH1E5_0041.rest = RH1E5_0041.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0041.s0 :: RH1E5_0041.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0042 : RS5.BandZeros RH1E5_0042.s0.t RH1E5_0042.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0042.s0 RH1E5_0042.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0042.s0 RH1E5_0042.rest = RH1E5_0042.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0042.s0 :: RH1E5_0042.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0043 : RS5.BandZeros RH1E5_0043.s0.t RH1E5_0043.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0043.s0 RH1E5_0043.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0043.s0 RH1E5_0043.rest = RH1E5_0043.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0043.s0 :: RH1E5_0043.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0044 : RS5.BandZeros RH1E5_0044.s0.t RH1E5_0044.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0044.s0 RH1E5_0044.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0044.s0 RH1E5_0044.rest = RH1E5_0044.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0044.s0 :: RH1E5_0044.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0045 : RS5.BandZeros RH1E5_0045.s0.t RH1E5_0045.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0045.s0 RH1E5_0045.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0045.s0 RH1E5_0045.rest = RH1E5_0045.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0045.s0 :: RH1E5_0045.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0046 : RS5.BandZeros RH1E5_0046.s0.t RH1E5_0046.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0046.s0 RH1E5_0046.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0046.s0 RH1E5_0046.rest = RH1E5_0046.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0046.s0 :: RH1E5_0046.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0047 : RS5.BandZeros RH1E5_0047.s0.t RH1E5_0047.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0047.s0 RH1E5_0047.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0047.s0 RH1E5_0047.rest = RH1E5_0047.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0047.s0 :: RH1E5_0047.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_005 : RS5.BandZeros RH1E5_0040.s0.t RH1E5_0047.sL.t 1016 := by
  have g40 := band_0040
  have g41 := RS5.BandZeros.glue (a := RH1E5_0040.s0.t) (b := RH1E5_0040.sL.t) (c := RH1E5_0041.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0040.s0, RH1E5_0039.sL, RH1E5_0040.sL]) (by norm_num [RS5.Sample.t, RH1E5_0040.sL, RH1E5_0041.sL]) g40 band_0041
  have g42 := RS5.BandZeros.glue (a := RH1E5_0040.s0.t) (b := RH1E5_0041.sL.t) (c := RH1E5_0042.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0040.s0, RH1E5_0039.sL, RH1E5_0041.sL]) (by norm_num [RS5.Sample.t, RH1E5_0041.sL, RH1E5_0042.sL]) g41 band_0042
  have g43 := RS5.BandZeros.glue (a := RH1E5_0040.s0.t) (b := RH1E5_0042.sL.t) (c := RH1E5_0043.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0040.s0, RH1E5_0039.sL, RH1E5_0042.sL]) (by norm_num [RS5.Sample.t, RH1E5_0042.sL, RH1E5_0043.sL]) g42 band_0043
  have g44 := RS5.BandZeros.glue (a := RH1E5_0040.s0.t) (b := RH1E5_0043.sL.t) (c := RH1E5_0044.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0040.s0, RH1E5_0039.sL, RH1E5_0043.sL]) (by norm_num [RS5.Sample.t, RH1E5_0043.sL, RH1E5_0044.sL]) g43 band_0044
  have g45 := RS5.BandZeros.glue (a := RH1E5_0040.s0.t) (b := RH1E5_0044.sL.t) (c := RH1E5_0045.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0040.s0, RH1E5_0039.sL, RH1E5_0044.sL]) (by norm_num [RS5.Sample.t, RH1E5_0044.sL, RH1E5_0045.sL]) g44 band_0045
  have g46 := RS5.BandZeros.glue (a := RH1E5_0040.s0.t) (b := RH1E5_0045.sL.t) (c := RH1E5_0046.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0040.s0, RH1E5_0039.sL, RH1E5_0045.sL]) (by norm_num [RS5.Sample.t, RH1E5_0045.sL, RH1E5_0046.sL]) g45 band_0046
  have g47 := RS5.BandZeros.glue (a := RH1E5_0040.s0.t) (b := RH1E5_0046.sL.t) (c := RH1E5_0047.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0040.s0, RH1E5_0039.sL, RH1E5_0046.sL]) (by norm_num [RS5.Sample.t, RH1E5_0046.sL, RH1E5_0047.sL]) g46 band_0047
  exact g47

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0040.s0.t RH1E5_0047.sL.t 1016 := by
  apply RH1E5.group_005 <;> assumption
