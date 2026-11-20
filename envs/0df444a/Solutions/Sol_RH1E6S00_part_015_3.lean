-- Prove2me | solution 1 for RH1E6S00.part_015_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:18:58.106192+00:00
-- url     : https://prove2.me/submissions/cda0a174-1015-4c06-9e7d-fecbb65e589c

import Definitions.Def_RH1E6S00_D015_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0126 : RS5.BandZeros ((7231180724 : ℝ) / 65536) ((7236531291 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0126.s0 RH1E6S00_0126.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0126.s0 RH1E6S00_0126.rest = RH1E6S00_0126.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0126.s0 :: RH1E6S00_0126.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0126.s0.t = ((7231180724 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0126.s0]
  have e1 : RH1E6S00_0126.sL.t = ((7236531291 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0126.sL]
  rw [e0, e1] at h
  exact h

theorem band_0127 : RS5.BandZeros ((7236531291 : ℝ) / 65536) ((7241870921 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0127.s0 RH1E6S00_0127.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0127.s0 RH1E6S00_0127.rest = RH1E6S00_0127.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0127.s0 :: RH1E6S00_0127.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0127.s0.t = ((7236531291 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0127.s0]
  have e1 : RH1E6S00_0127.sL.t = ((7241870921 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0127.sL]
  rw [e0, e1] at h
  exact h

theorem part_015_3 : RS5.BandZeros ((7231180724 : ℝ) / 65536) ((7241870921 : ℝ) / 65536) 254 := by
  have g0 := band_0126
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0127
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7231180724 : ℝ) / 65536) ((7241870921 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_015_3 <;> assumption
