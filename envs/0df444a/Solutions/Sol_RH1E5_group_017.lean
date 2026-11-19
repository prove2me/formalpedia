-- Prove2me | solution 1 for RH1E5.group_017
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:24:11.883895+00:00
-- url     : https://prove2.me/submissions/70acf9b1-c1db-412a-9ccd-f76be4792799

import Definitions.Def_RH1E5_Data017
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0136 : RS5.BandZeros RH1E5_0136.s0.t RH1E5_0136.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0136.s0 RH1E5_0136.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0136.s0 RH1E5_0136.rest = RH1E5_0136.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0136.s0 :: RH1E5_0136.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0137 : RS5.BandZeros RH1E5_0137.s0.t RH1E5_0137.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0137.s0 RH1E5_0137.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0137.s0 RH1E5_0137.rest = RH1E5_0137.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0137.s0 :: RH1E5_0137.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0138 : RS5.BandZeros RH1E5_0138.s0.t RH1E5_0138.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0138.s0 RH1E5_0138.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0138.s0 RH1E5_0138.rest = RH1E5_0138.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0138.s0 :: RH1E5_0138.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0139 : RS5.BandZeros RH1E5_0139.s0.t RH1E5_0139.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0139.s0 RH1E5_0139.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0139.s0 RH1E5_0139.rest = RH1E5_0139.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0139.s0 :: RH1E5_0139.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0140 : RS5.BandZeros RH1E5_0140.s0.t RH1E5_0140.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0140.s0 RH1E5_0140.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0140.s0 RH1E5_0140.rest = RH1E5_0140.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0140.s0 :: RH1E5_0140.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0141 : RS5.BandZeros RH1E5_0141.s0.t RH1E5_0141.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0141.s0 RH1E5_0141.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0141.s0 RH1E5_0141.rest = RH1E5_0141.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0141.s0 :: RH1E5_0141.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0142 : RS5.BandZeros RH1E5_0142.s0.t RH1E5_0142.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0142.s0 RH1E5_0142.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0142.s0 RH1E5_0142.rest = RH1E5_0142.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0142.s0 :: RH1E5_0142.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0143 : RS5.BandZeros RH1E5_0143.s0.t RH1E5_0143.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0143.s0 RH1E5_0143.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0143.s0 RH1E5_0143.rest = RH1E5_0143.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0143.s0 :: RH1E5_0143.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_017 : RS5.BandZeros RH1E5_0136.s0.t RH1E5_0143.sL.t 1016 := by
  have g136 := band_0136
  have g137 := RS5.BandZeros.glue (a := RH1E5_0136.s0.t) (b := RH1E5_0136.sL.t) (c := RH1E5_0137.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0136.s0, RH1E5_0135.sL, RH1E5_0136.sL]) (by norm_num [RS5.Sample.t, RH1E5_0136.sL, RH1E5_0137.sL]) g136 band_0137
  have g138 := RS5.BandZeros.glue (a := RH1E5_0136.s0.t) (b := RH1E5_0137.sL.t) (c := RH1E5_0138.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0136.s0, RH1E5_0135.sL, RH1E5_0137.sL]) (by norm_num [RS5.Sample.t, RH1E5_0137.sL, RH1E5_0138.sL]) g137 band_0138
  have g139 := RS5.BandZeros.glue (a := RH1E5_0136.s0.t) (b := RH1E5_0138.sL.t) (c := RH1E5_0139.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0136.s0, RH1E5_0135.sL, RH1E5_0138.sL]) (by norm_num [RS5.Sample.t, RH1E5_0138.sL, RH1E5_0139.sL]) g138 band_0139
  have g140 := RS5.BandZeros.glue (a := RH1E5_0136.s0.t) (b := RH1E5_0139.sL.t) (c := RH1E5_0140.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0136.s0, RH1E5_0135.sL, RH1E5_0139.sL]) (by norm_num [RS5.Sample.t, RH1E5_0139.sL, RH1E5_0140.sL]) g139 band_0140
  have g141 := RS5.BandZeros.glue (a := RH1E5_0136.s0.t) (b := RH1E5_0140.sL.t) (c := RH1E5_0141.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0136.s0, RH1E5_0135.sL, RH1E5_0140.sL]) (by norm_num [RS5.Sample.t, RH1E5_0140.sL, RH1E5_0141.sL]) g140 band_0141
  have g142 := RS5.BandZeros.glue (a := RH1E5_0136.s0.t) (b := RH1E5_0141.sL.t) (c := RH1E5_0142.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0136.s0, RH1E5_0135.sL, RH1E5_0141.sL]) (by norm_num [RS5.Sample.t, RH1E5_0141.sL, RH1E5_0142.sL]) g141 band_0142
  have g143 := RS5.BandZeros.glue (a := RH1E5_0136.s0.t) (b := RH1E5_0142.sL.t) (c := RH1E5_0143.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0136.s0, RH1E5_0135.sL, RH1E5_0142.sL]) (by norm_num [RS5.Sample.t, RH1E5_0142.sL, RH1E5_0143.sL]) g142 band_0143
  exact g143

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0136.s0.t RH1E5_0143.sL.t 1016 := by
  apply RH1E5.group_017 <;> assumption
