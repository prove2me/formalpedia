-- Prove2me | solution 1 for RH1E5.group_022
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:36:38.186007+00:00
-- url     : https://prove2.me/submissions/4f2cfc27-5bf8-4fc9-8f0b-beed267b219a

import Definitions.Def_RH1E5_Data022
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0176 : RS5.BandZeros RH1E5_0176.s0.t RH1E5_0176.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0176.s0 RH1E5_0176.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0176.s0 RH1E5_0176.rest = RH1E5_0176.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0176.s0 :: RH1E5_0176.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0177 : RS5.BandZeros RH1E5_0177.s0.t RH1E5_0177.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0177.s0 RH1E5_0177.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0177.s0 RH1E5_0177.rest = RH1E5_0177.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0177.s0 :: RH1E5_0177.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0178 : RS5.BandZeros RH1E5_0178.s0.t RH1E5_0178.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0178.s0 RH1E5_0178.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0178.s0 RH1E5_0178.rest = RH1E5_0178.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0178.s0 :: RH1E5_0178.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0179 : RS5.BandZeros RH1E5_0179.s0.t RH1E5_0179.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0179.s0 RH1E5_0179.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0179.s0 RH1E5_0179.rest = RH1E5_0179.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0179.s0 :: RH1E5_0179.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0180 : RS5.BandZeros RH1E5_0180.s0.t RH1E5_0180.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0180.s0 RH1E5_0180.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0180.s0 RH1E5_0180.rest = RH1E5_0180.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0180.s0 :: RH1E5_0180.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0181 : RS5.BandZeros RH1E5_0181.s0.t RH1E5_0181.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0181.s0 RH1E5_0181.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0181.s0 RH1E5_0181.rest = RH1E5_0181.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0181.s0 :: RH1E5_0181.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0182 : RS5.BandZeros RH1E5_0182.s0.t RH1E5_0182.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0182.s0 RH1E5_0182.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0182.s0 RH1E5_0182.rest = RH1E5_0182.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0182.s0 :: RH1E5_0182.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0183 : RS5.BandZeros RH1E5_0183.s0.t RH1E5_0183.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0183.s0 RH1E5_0183.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0183.s0 RH1E5_0183.rest = RH1E5_0183.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0183.s0 :: RH1E5_0183.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_022 : RS5.BandZeros RH1E5_0176.s0.t RH1E5_0183.sL.t 1016 := by
  have g176 := band_0176
  have g177 := RS5.BandZeros.glue (a := RH1E5_0176.s0.t) (b := RH1E5_0176.sL.t) (c := RH1E5_0177.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0176.s0, RH1E5_0175.sL, RH1E5_0176.sL]) (by norm_num [RS5.Sample.t, RH1E5_0176.sL, RH1E5_0177.sL]) g176 band_0177
  have g178 := RS5.BandZeros.glue (a := RH1E5_0176.s0.t) (b := RH1E5_0177.sL.t) (c := RH1E5_0178.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0176.s0, RH1E5_0175.sL, RH1E5_0177.sL]) (by norm_num [RS5.Sample.t, RH1E5_0177.sL, RH1E5_0178.sL]) g177 band_0178
  have g179 := RS5.BandZeros.glue (a := RH1E5_0176.s0.t) (b := RH1E5_0178.sL.t) (c := RH1E5_0179.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0176.s0, RH1E5_0175.sL, RH1E5_0178.sL]) (by norm_num [RS5.Sample.t, RH1E5_0178.sL, RH1E5_0179.sL]) g178 band_0179
  have g180 := RS5.BandZeros.glue (a := RH1E5_0176.s0.t) (b := RH1E5_0179.sL.t) (c := RH1E5_0180.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0176.s0, RH1E5_0175.sL, RH1E5_0179.sL]) (by norm_num [RS5.Sample.t, RH1E5_0179.sL, RH1E5_0180.sL]) g179 band_0180
  have g181 := RS5.BandZeros.glue (a := RH1E5_0176.s0.t) (b := RH1E5_0180.sL.t) (c := RH1E5_0181.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0176.s0, RH1E5_0175.sL, RH1E5_0180.sL]) (by norm_num [RS5.Sample.t, RH1E5_0180.sL, RH1E5_0181.sL]) g180 band_0181
  have g182 := RS5.BandZeros.glue (a := RH1E5_0176.s0.t) (b := RH1E5_0181.sL.t) (c := RH1E5_0182.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0176.s0, RH1E5_0175.sL, RH1E5_0181.sL]) (by norm_num [RS5.Sample.t, RH1E5_0181.sL, RH1E5_0182.sL]) g181 band_0182
  have g183 := RS5.BandZeros.glue (a := RH1E5_0176.s0.t) (b := RH1E5_0182.sL.t) (c := RH1E5_0183.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0176.s0, RH1E5_0175.sL, RH1E5_0182.sL]) (by norm_num [RS5.Sample.t, RH1E5_0182.sL, RH1E5_0183.sL]) g182 band_0183
  exact g183

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0176.s0.t RH1E5_0183.sL.t 1016 := by
  apply RH1E5.group_022 <;> assumption
