-- Prove2me | solution 1 for RH1E5.group_007
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:00:37.035379+00:00
-- url     : https://prove2.me/submissions/34fa5919-f141-4232-9ea8-d84f8b8cc0b9

import Definitions.Def_RH1E5_Data007
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0056 : RS5.BandZeros RH1E5_0056.s0.t RH1E5_0056.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0056.s0 RH1E5_0056.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0056.s0 RH1E5_0056.rest = RH1E5_0056.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0056.s0 :: RH1E5_0056.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0057 : RS5.BandZeros RH1E5_0057.s0.t RH1E5_0057.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0057.s0 RH1E5_0057.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0057.s0 RH1E5_0057.rest = RH1E5_0057.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0057.s0 :: RH1E5_0057.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0058 : RS5.BandZeros RH1E5_0058.s0.t RH1E5_0058.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0058.s0 RH1E5_0058.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0058.s0 RH1E5_0058.rest = RH1E5_0058.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0058.s0 :: RH1E5_0058.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0059 : RS5.BandZeros RH1E5_0059.s0.t RH1E5_0059.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0059.s0 RH1E5_0059.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0059.s0 RH1E5_0059.rest = RH1E5_0059.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0059.s0 :: RH1E5_0059.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0060 : RS5.BandZeros RH1E5_0060.s0.t RH1E5_0060.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0060.s0 RH1E5_0060.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0060.s0 RH1E5_0060.rest = RH1E5_0060.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0060.s0 :: RH1E5_0060.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0061 : RS5.BandZeros RH1E5_0061.s0.t RH1E5_0061.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0061.s0 RH1E5_0061.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0061.s0 RH1E5_0061.rest = RH1E5_0061.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0061.s0 :: RH1E5_0061.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0062 : RS5.BandZeros RH1E5_0062.s0.t RH1E5_0062.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0062.s0 RH1E5_0062.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0062.s0 RH1E5_0062.rest = RH1E5_0062.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0062.s0 :: RH1E5_0062.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0063 : RS5.BandZeros RH1E5_0063.s0.t RH1E5_0063.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0063.s0 RH1E5_0063.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0063.s0 RH1E5_0063.rest = RH1E5_0063.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0063.s0 :: RH1E5_0063.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_007 : RS5.BandZeros RH1E5_0056.s0.t RH1E5_0063.sL.t 1016 := by
  have g56 := band_0056
  have g57 := RS5.BandZeros.glue (a := RH1E5_0056.s0.t) (b := RH1E5_0056.sL.t) (c := RH1E5_0057.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0056.s0, RH1E5_0055.sL, RH1E5_0056.sL]) (by norm_num [RS5.Sample.t, RH1E5_0056.sL, RH1E5_0057.sL]) g56 band_0057
  have g58 := RS5.BandZeros.glue (a := RH1E5_0056.s0.t) (b := RH1E5_0057.sL.t) (c := RH1E5_0058.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0056.s0, RH1E5_0055.sL, RH1E5_0057.sL]) (by norm_num [RS5.Sample.t, RH1E5_0057.sL, RH1E5_0058.sL]) g57 band_0058
  have g59 := RS5.BandZeros.glue (a := RH1E5_0056.s0.t) (b := RH1E5_0058.sL.t) (c := RH1E5_0059.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0056.s0, RH1E5_0055.sL, RH1E5_0058.sL]) (by norm_num [RS5.Sample.t, RH1E5_0058.sL, RH1E5_0059.sL]) g58 band_0059
  have g60 := RS5.BandZeros.glue (a := RH1E5_0056.s0.t) (b := RH1E5_0059.sL.t) (c := RH1E5_0060.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0056.s0, RH1E5_0055.sL, RH1E5_0059.sL]) (by norm_num [RS5.Sample.t, RH1E5_0059.sL, RH1E5_0060.sL]) g59 band_0060
  have g61 := RS5.BandZeros.glue (a := RH1E5_0056.s0.t) (b := RH1E5_0060.sL.t) (c := RH1E5_0061.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0056.s0, RH1E5_0055.sL, RH1E5_0060.sL]) (by norm_num [RS5.Sample.t, RH1E5_0060.sL, RH1E5_0061.sL]) g60 band_0061
  have g62 := RS5.BandZeros.glue (a := RH1E5_0056.s0.t) (b := RH1E5_0061.sL.t) (c := RH1E5_0062.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0056.s0, RH1E5_0055.sL, RH1E5_0061.sL]) (by norm_num [RS5.Sample.t, RH1E5_0061.sL, RH1E5_0062.sL]) g61 band_0062
  have g63 := RS5.BandZeros.glue (a := RH1E5_0056.s0.t) (b := RH1E5_0062.sL.t) (c := RH1E5_0063.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0056.s0, RH1E5_0055.sL, RH1E5_0062.sL]) (by norm_num [RS5.Sample.t, RH1E5_0062.sL, RH1E5_0063.sL]) g62 band_0063
  exact g63

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0056.s0.t RH1E5_0063.sL.t 1016 := by
  apply RH1E5.group_007 <;> assumption
