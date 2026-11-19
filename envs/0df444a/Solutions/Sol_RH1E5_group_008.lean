-- Prove2me | solution 1 for RH1E5.group_008
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:04:11.171196+00:00
-- url     : https://prove2.me/submissions/7bed393c-e193-43b8-a477-0b61860933aa

import Definitions.Def_RH1E5_Data008
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0064 : RS5.BandZeros RH1E5_0064.s0.t RH1E5_0064.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0064.s0 RH1E5_0064.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0064.s0 RH1E5_0064.rest = RH1E5_0064.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0064.s0 :: RH1E5_0064.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0065 : RS5.BandZeros RH1E5_0065.s0.t RH1E5_0065.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0065.s0 RH1E5_0065.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0065.s0 RH1E5_0065.rest = RH1E5_0065.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0065.s0 :: RH1E5_0065.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0066 : RS5.BandZeros RH1E5_0066.s0.t RH1E5_0066.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0066.s0 RH1E5_0066.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0066.s0 RH1E5_0066.rest = RH1E5_0066.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0066.s0 :: RH1E5_0066.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0067 : RS5.BandZeros RH1E5_0067.s0.t RH1E5_0067.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0067.s0 RH1E5_0067.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0067.s0 RH1E5_0067.rest = RH1E5_0067.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0067.s0 :: RH1E5_0067.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0068 : RS5.BandZeros RH1E5_0068.s0.t RH1E5_0068.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0068.s0 RH1E5_0068.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0068.s0 RH1E5_0068.rest = RH1E5_0068.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0068.s0 :: RH1E5_0068.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0069 : RS5.BandZeros RH1E5_0069.s0.t RH1E5_0069.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0069.s0 RH1E5_0069.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0069.s0 RH1E5_0069.rest = RH1E5_0069.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0069.s0 :: RH1E5_0069.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0070 : RS5.BandZeros RH1E5_0070.s0.t RH1E5_0070.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0070.s0 RH1E5_0070.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0070.s0 RH1E5_0070.rest = RH1E5_0070.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0070.s0 :: RH1E5_0070.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0071 : RS5.BandZeros RH1E5_0071.s0.t RH1E5_0071.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0071.s0 RH1E5_0071.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0071.s0 RH1E5_0071.rest = RH1E5_0071.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0071.s0 :: RH1E5_0071.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_008 : RS5.BandZeros RH1E5_0064.s0.t RH1E5_0071.sL.t 1016 := by
  have g64 := band_0064
  have g65 := RS5.BandZeros.glue (a := RH1E5_0064.s0.t) (b := RH1E5_0064.sL.t) (c := RH1E5_0065.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0064.s0, RH1E5_0063.sL, RH1E5_0064.sL]) (by norm_num [RS5.Sample.t, RH1E5_0064.sL, RH1E5_0065.sL]) g64 band_0065
  have g66 := RS5.BandZeros.glue (a := RH1E5_0064.s0.t) (b := RH1E5_0065.sL.t) (c := RH1E5_0066.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0064.s0, RH1E5_0063.sL, RH1E5_0065.sL]) (by norm_num [RS5.Sample.t, RH1E5_0065.sL, RH1E5_0066.sL]) g65 band_0066
  have g67 := RS5.BandZeros.glue (a := RH1E5_0064.s0.t) (b := RH1E5_0066.sL.t) (c := RH1E5_0067.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0064.s0, RH1E5_0063.sL, RH1E5_0066.sL]) (by norm_num [RS5.Sample.t, RH1E5_0066.sL, RH1E5_0067.sL]) g66 band_0067
  have g68 := RS5.BandZeros.glue (a := RH1E5_0064.s0.t) (b := RH1E5_0067.sL.t) (c := RH1E5_0068.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0064.s0, RH1E5_0063.sL, RH1E5_0067.sL]) (by norm_num [RS5.Sample.t, RH1E5_0067.sL, RH1E5_0068.sL]) g67 band_0068
  have g69 := RS5.BandZeros.glue (a := RH1E5_0064.s0.t) (b := RH1E5_0068.sL.t) (c := RH1E5_0069.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0064.s0, RH1E5_0063.sL, RH1E5_0068.sL]) (by norm_num [RS5.Sample.t, RH1E5_0068.sL, RH1E5_0069.sL]) g68 band_0069
  have g70 := RS5.BandZeros.glue (a := RH1E5_0064.s0.t) (b := RH1E5_0069.sL.t) (c := RH1E5_0070.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0064.s0, RH1E5_0063.sL, RH1E5_0069.sL]) (by norm_num [RS5.Sample.t, RH1E5_0069.sL, RH1E5_0070.sL]) g69 band_0070
  have g71 := RS5.BandZeros.glue (a := RH1E5_0064.s0.t) (b := RH1E5_0070.sL.t) (c := RH1E5_0071.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0064.s0, RH1E5_0063.sL, RH1E5_0070.sL]) (by norm_num [RS5.Sample.t, RH1E5_0070.sL, RH1E5_0071.sL]) g70 band_0071
  exact g71

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0064.s0.t RH1E5_0071.sL.t 1016 := by
  apply RH1E5.group_008 <;> assumption
