-- Prove2me | solution 1 for RH1E5.group_019
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:30:22.003207+00:00
-- url     : https://prove2.me/submissions/f5229923-31b4-4b18-9b9c-c66543a31088

import Definitions.Def_RH1E5_Data019
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0152 : RS5.BandZeros RH1E5_0152.s0.t RH1E5_0152.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0152.s0 RH1E5_0152.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0152.s0 RH1E5_0152.rest = RH1E5_0152.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0152.s0 :: RH1E5_0152.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0153 : RS5.BandZeros RH1E5_0153.s0.t RH1E5_0153.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0153.s0 RH1E5_0153.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0153.s0 RH1E5_0153.rest = RH1E5_0153.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0153.s0 :: RH1E5_0153.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0154 : RS5.BandZeros RH1E5_0154.s0.t RH1E5_0154.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0154.s0 RH1E5_0154.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0154.s0 RH1E5_0154.rest = RH1E5_0154.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0154.s0 :: RH1E5_0154.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0155 : RS5.BandZeros RH1E5_0155.s0.t RH1E5_0155.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0155.s0 RH1E5_0155.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0155.s0 RH1E5_0155.rest = RH1E5_0155.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0155.s0 :: RH1E5_0155.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0156 : RS5.BandZeros RH1E5_0156.s0.t RH1E5_0156.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0156.s0 RH1E5_0156.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0156.s0 RH1E5_0156.rest = RH1E5_0156.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0156.s0 :: RH1E5_0156.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0157 : RS5.BandZeros RH1E5_0157.s0.t RH1E5_0157.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0157.s0 RH1E5_0157.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0157.s0 RH1E5_0157.rest = RH1E5_0157.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0157.s0 :: RH1E5_0157.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0158 : RS5.BandZeros RH1E5_0158.s0.t RH1E5_0158.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0158.s0 RH1E5_0158.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0158.s0 RH1E5_0158.rest = RH1E5_0158.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0158.s0 :: RH1E5_0158.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0159 : RS5.BandZeros RH1E5_0159.s0.t RH1E5_0159.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0159.s0 RH1E5_0159.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0159.s0 RH1E5_0159.rest = RH1E5_0159.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0159.s0 :: RH1E5_0159.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_019 : RS5.BandZeros RH1E5_0152.s0.t RH1E5_0159.sL.t 1016 := by
  have g152 := band_0152
  have g153 := RS5.BandZeros.glue (a := RH1E5_0152.s0.t) (b := RH1E5_0152.sL.t) (c := RH1E5_0153.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0152.s0, RH1E5_0151.sL, RH1E5_0152.sL]) (by norm_num [RS5.Sample.t, RH1E5_0152.sL, RH1E5_0153.sL]) g152 band_0153
  have g154 := RS5.BandZeros.glue (a := RH1E5_0152.s0.t) (b := RH1E5_0153.sL.t) (c := RH1E5_0154.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0152.s0, RH1E5_0151.sL, RH1E5_0153.sL]) (by norm_num [RS5.Sample.t, RH1E5_0153.sL, RH1E5_0154.sL]) g153 band_0154
  have g155 := RS5.BandZeros.glue (a := RH1E5_0152.s0.t) (b := RH1E5_0154.sL.t) (c := RH1E5_0155.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0152.s0, RH1E5_0151.sL, RH1E5_0154.sL]) (by norm_num [RS5.Sample.t, RH1E5_0154.sL, RH1E5_0155.sL]) g154 band_0155
  have g156 := RS5.BandZeros.glue (a := RH1E5_0152.s0.t) (b := RH1E5_0155.sL.t) (c := RH1E5_0156.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0152.s0, RH1E5_0151.sL, RH1E5_0155.sL]) (by norm_num [RS5.Sample.t, RH1E5_0155.sL, RH1E5_0156.sL]) g155 band_0156
  have g157 := RS5.BandZeros.glue (a := RH1E5_0152.s0.t) (b := RH1E5_0156.sL.t) (c := RH1E5_0157.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0152.s0, RH1E5_0151.sL, RH1E5_0156.sL]) (by norm_num [RS5.Sample.t, RH1E5_0156.sL, RH1E5_0157.sL]) g156 band_0157
  have g158 := RS5.BandZeros.glue (a := RH1E5_0152.s0.t) (b := RH1E5_0157.sL.t) (c := RH1E5_0158.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0152.s0, RH1E5_0151.sL, RH1E5_0157.sL]) (by norm_num [RS5.Sample.t, RH1E5_0157.sL, RH1E5_0158.sL]) g157 band_0158
  have g159 := RS5.BandZeros.glue (a := RH1E5_0152.s0.t) (b := RH1E5_0158.sL.t) (c := RH1E5_0159.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0152.s0, RH1E5_0151.sL, RH1E5_0158.sL]) (by norm_num [RS5.Sample.t, RH1E5_0158.sL, RH1E5_0159.sL]) g158 band_0159
  exact g159

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0152.s0.t RH1E5_0159.sL.t 1016 := by
  apply RH1E5.group_019 <;> assumption
