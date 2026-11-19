-- Prove2me | solution 1 for RH1E5.group_027
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T20:50:22.575752+00:00
-- url     : https://prove2.me/submissions/f30c2248-0222-4c99-a93a-66d5f226e69d

import Definitions.Def_RH1E5_Data027
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E5

theorem band_0216 : RS5.BandZeros RH1E5_0216.s0.t RH1E5_0216.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0216.s0 RH1E5_0216.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0216.s0 RH1E5_0216.rest = RH1E5_0216.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0216.s0 :: RH1E5_0216.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0217 : RS5.BandZeros RH1E5_0217.s0.t RH1E5_0217.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0217.s0 RH1E5_0217.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0217.s0 RH1E5_0217.rest = RH1E5_0217.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0217.s0 :: RH1E5_0217.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0218 : RS5.BandZeros RH1E5_0218.s0.t RH1E5_0218.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0218.s0 RH1E5_0218.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0218.s0 RH1E5_0218.rest = RH1E5_0218.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0218.s0 :: RH1E5_0218.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0219 : RS5.BandZeros RH1E5_0219.s0.t RH1E5_0219.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0219.s0 RH1E5_0219.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0219.s0 RH1E5_0219.rest = RH1E5_0219.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0219.s0 :: RH1E5_0219.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0220 : RS5.BandZeros RH1E5_0220.s0.t RH1E5_0220.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0220.s0 RH1E5_0220.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0220.s0 RH1E5_0220.rest = RH1E5_0220.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0220.s0 :: RH1E5_0220.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0221 : RS5.BandZeros RH1E5_0221.s0.t RH1E5_0221.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0221.s0 RH1E5_0221.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0221.s0 RH1E5_0221.rest = RH1E5_0221.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0221.s0 :: RH1E5_0221.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0222 : RS5.BandZeros RH1E5_0222.s0.t RH1E5_0222.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0222.s0 RH1E5_0222.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0222.s0 RH1E5_0222.rest = RH1E5_0222.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0222.s0 :: RH1E5_0222.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem band_0223 : RS5.BandZeros RH1E5_0223.s0.t RH1E5_0223.sL.t 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E5_0223.s0 RH1E5_0223.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E5_0223.s0 RH1E5_0223.rest = RH1E5_0223.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E5_0223.s0 :: RH1E5_0223.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  exact h

theorem group_027 : RS5.BandZeros RH1E5_0216.s0.t RH1E5_0223.sL.t 1016 := by
  have g216 := band_0216
  have g217 := RS5.BandZeros.glue (a := RH1E5_0216.s0.t) (b := RH1E5_0216.sL.t) (c := RH1E5_0217.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0216.s0, RH1E5_0215.sL, RH1E5_0216.sL]) (by norm_num [RS5.Sample.t, RH1E5_0216.sL, RH1E5_0217.sL]) g216 band_0217
  have g218 := RS5.BandZeros.glue (a := RH1E5_0216.s0.t) (b := RH1E5_0217.sL.t) (c := RH1E5_0218.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0216.s0, RH1E5_0215.sL, RH1E5_0217.sL]) (by norm_num [RS5.Sample.t, RH1E5_0217.sL, RH1E5_0218.sL]) g217 band_0218
  have g219 := RS5.BandZeros.glue (a := RH1E5_0216.s0.t) (b := RH1E5_0218.sL.t) (c := RH1E5_0219.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0216.s0, RH1E5_0215.sL, RH1E5_0218.sL]) (by norm_num [RS5.Sample.t, RH1E5_0218.sL, RH1E5_0219.sL]) g218 band_0219
  have g220 := RS5.BandZeros.glue (a := RH1E5_0216.s0.t) (b := RH1E5_0219.sL.t) (c := RH1E5_0220.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0216.s0, RH1E5_0215.sL, RH1E5_0219.sL]) (by norm_num [RS5.Sample.t, RH1E5_0219.sL, RH1E5_0220.sL]) g219 band_0220
  have g221 := RS5.BandZeros.glue (a := RH1E5_0216.s0.t) (b := RH1E5_0220.sL.t) (c := RH1E5_0221.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0216.s0, RH1E5_0215.sL, RH1E5_0220.sL]) (by norm_num [RS5.Sample.t, RH1E5_0220.sL, RH1E5_0221.sL]) g220 band_0221
  have g222 := RS5.BandZeros.glue (a := RH1E5_0216.s0.t) (b := RH1E5_0221.sL.t) (c := RH1E5_0222.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0216.s0, RH1E5_0215.sL, RH1E5_0221.sL]) (by norm_num [RS5.Sample.t, RH1E5_0221.sL, RH1E5_0222.sL]) g221 band_0222
  have g223 := RS5.BandZeros.glue (a := RH1E5_0216.s0.t) (b := RH1E5_0222.sL.t) (c := RH1E5_0223.sL.t)
    (by norm_num [RS5.Sample.t, RH1E5_0216.s0, RH1E5_0215.sL, RH1E5_0222.sL]) (by norm_num [RS5.Sample.t, RH1E5_0222.sL, RH1E5_0223.sL]) g222 band_0223
  exact g223

end RH1E5
open RH1E5 in
theorem solution : RS5.BandZeros RH1E5_0216.s0.t RH1E5_0223.sL.t 1016 := by
  apply RH1E5.group_027 <;> assumption
