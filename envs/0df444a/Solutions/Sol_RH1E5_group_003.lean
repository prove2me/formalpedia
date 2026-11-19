-- Prove2me | solution 1 for RH1E5.group_003
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:51:48.745021+00:00
-- url     : https://prove2.me/submissions/3dc2a93c-c5b9-4ac6-8c9d-5fa20c21c398

import Definitions.Def_RH1E5_Data003
import Theorems.Thm_RS5_bandZeros_of_ok_prime
import Theorems.Thm_RS5_BandZeros_glue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0024 : RS5.BandZeros RH1E5_0024.s0.t RH1E5_0024.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0024.s0 RH1E5_0024.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0024.s0 RH1E5_0024.rest = RH1E5_0024.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0024.s0 :: RH1E5_0024.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0025 : RS5.BandZeros RH1E5_0025.s0.t RH1E5_0025.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0025.s0 RH1E5_0025.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0025.s0 RH1E5_0025.rest = RH1E5_0025.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0025.s0 :: RH1E5_0025.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0026 : RS5.BandZeros RH1E5_0026.s0.t RH1E5_0026.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0026.s0 RH1E5_0026.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0026.s0 RH1E5_0026.rest = RH1E5_0026.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0026.s0 :: RH1E5_0026.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0027 : RS5.BandZeros RH1E5_0027.s0.t RH1E5_0027.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0027.s0 RH1E5_0027.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0027.s0 RH1E5_0027.rest = RH1E5_0027.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0027.s0 :: RH1E5_0027.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0028 : RS5.BandZeros RH1E5_0028.s0.t RH1E5_0028.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0028.s0 RH1E5_0028.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0028.s0 RH1E5_0028.rest = RH1E5_0028.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0028.s0 :: RH1E5_0028.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0029 : RS5.BandZeros RH1E5_0029.s0.t RH1E5_0029.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0029.s0 RH1E5_0029.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0029.s0 RH1E5_0029.rest = RH1E5_0029.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0029.s0 :: RH1E5_0029.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0030 : RS5.BandZeros RH1E5_0030.s0.t RH1E5_0030.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0030.s0 RH1E5_0030.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0030.s0 RH1E5_0030.rest = RH1E5_0030.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0030.s0 :: RH1E5_0030.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0031 : RS5.BandZeros RH1E5_0031.s0.t RH1E5_0031.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0031.s0 RH1E5_0031.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0031.s0 RH1E5_0031.rest = RH1E5_0031.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0031.s0 :: RH1E5_0031.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_003 : RS5.BandZeros RH1E5_0024.s0.t RH1E5_0031.sL.t 1016 := by
  have g24 := band_0024
  have g25 := RS5.BandZeros.glue (a := RH1E5_0024.s0.t) (b := RH1E5_0024.sL.t) (c := RH1E5_0025.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0024.s0, RH1E5_0023.sL, RH1E5_0024.sL]) (by norm_num [RS5.Sample.t, RH1E5_0024.sL, RH1E5_0025.sL]) g24 band_0025
  have g26 := RS5.BandZeros.glue (a := RH1E5_0024.s0.t) (b := RH1E5_0025.sL.t) (c := RH1E5_0026.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0024.s0, RH1E5_0023.sL, RH1E5_0025.sL]) (by norm_num [RS5.Sample.t, RH1E5_0025.sL, RH1E5_0026.sL]) g25 band_0026
  have g27 := RS5.BandZeros.glue (a := RH1E5_0024.s0.t) (b := RH1E5_0026.sL.t) (c := RH1E5_0027.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0024.s0, RH1E5_0023.sL, RH1E5_0026.sL]) (by norm_num [RS5.Sample.t, RH1E5_0026.sL, RH1E5_0027.sL]) g26 band_0027
  have g28 := RS5.BandZeros.glue (a := RH1E5_0024.s0.t) (b := RH1E5_0027.sL.t) (c := RH1E5_0028.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0024.s0, RH1E5_0023.sL, RH1E5_0027.sL]) (by norm_num [RS5.Sample.t, RH1E5_0027.sL, RH1E5_0028.sL]) g27 band_0028
  have g29 := RS5.BandZeros.glue (a := RH1E5_0024.s0.t) (b := RH1E5_0028.sL.t) (c := RH1E5_0029.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0024.s0, RH1E5_0023.sL, RH1E5_0028.sL]) (by norm_num [RS5.Sample.t, RH1E5_0028.sL, RH1E5_0029.sL]) g28 band_0029
  have g30 := RS5.BandZeros.glue (a := RH1E5_0024.s0.t) (b := RH1E5_0029.sL.t) (c := RH1E5_0030.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0024.s0, RH1E5_0023.sL, RH1E5_0029.sL]) (by norm_num [RS5.Sample.t, RH1E5_0029.sL, RH1E5_0030.sL]) g29 band_0030
  have g31 := RS5.BandZeros.glue (a := RH1E5_0024.s0.t) (b := RH1E5_0030.sL.t) (c := RH1E5_0031.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0024.s0, RH1E5_0023.sL, RH1E5_0030.sL]) (by norm_num [RS5.Sample.t, RH1E5_0030.sL, RH1E5_0031.sL]) g30 band_0031
  exact g31

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0024.s0.t RH1E5_0031.sL.t 1016 := by
  apply RH1E5.group_003 <;> assumption
