-- Prove2me | solution 1 for RH1E6S08.part_020_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:51:51.407389+00:00
-- url     : https://prove2.me/submissions/be695bcb-c758-4e41-92fc-250422d50501

import Definitions.Def_RH1E6S08_D020_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem band_0164 : RS5.BandZeros ((33527264711 : ℝ) / 65536) ((33531884902 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0164.s0 RH1E6S08_0164.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0164.s0 RH1E6S08_0164.rest = RH1E6S08_0164.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0164.s0 :: RH1E6S08_0164.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0164.s0.t = ((33527264711 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0164.s0]
  have e1 : RH1E6S08_0164.sL.t = ((33531884902 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0164.sL]
  rw [e0, e1] at h
  exact h

theorem band_0165 : RS5.BandZeros ((33531884902 : ℝ) / 65536) ((33536521821 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S08_0165.s0 RH1E6S08_0165.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S08_0165.s0 RH1E6S08_0165.rest = RH1E6S08_0165.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S08_0165.s0 :: RH1E6S08_0165.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S08_0165.s0.t = ((33531884902 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0165.s0]
  have e1 : RH1E6S08_0165.sL.t = ((33536521821 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S08_0165.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_2 : RS5.BandZeros ((33527264711 : ℝ) / 65536) ((33536521821 : ℝ) / 65536) 254 := by
  have g0 := band_0164
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0165
  exact g1

end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33527264711 : ℝ) / 65536) ((33536521821 : ℝ) / 65536) 254 := by
  apply RH1E6S08.part_020_2 <;> assumption
