-- Prove2me | solution 1 for RH1E6S03.part_057_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T07:21:55.69816+00:00
-- url     : https://prove2.me/submissions/20a8c715-1873-4fb4-a113-b249ad1a6253

import Definitions.Def_RH1E6S03_D057_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem band_0456 : RS5.BandZeros ((18621710858 : ℝ) / 65536) ((18626589391 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0456.s0 RH1E6S03_0456.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0456.s0 RH1E6S03_0456.rest = RH1E6S03_0456.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0456.s0 :: RH1E6S03_0456.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0456.s0.t = ((18621710858 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0456.s0]
  have e1 : RH1E6S03_0456.sL.t = ((18626589391 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0456.sL]
  rw [e0, e1] at h
  exact h

theorem band_0457 : RS5.BandZeros ((18626589391 : ℝ) / 65536) ((18631458202 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S03_0457.s0 RH1E6S03_0457.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S03_0457.s0 RH1E6S03_0457.rest = RH1E6S03_0457.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S03_0457.s0 :: RH1E6S03_0457.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S03_0457.s0.t = ((18626589391 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0457.s0]
  have e1 : RH1E6S03_0457.sL.t = ((18631458202 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S03_0457.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_0 : RS5.BandZeros ((18621710858 : ℝ) / 65536) ((18631458202 : ℝ) / 65536) 254 := by
  have g0 := band_0456
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0457
  exact g1

end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((18621710858 : ℝ) / 65536) ((18631458202 : ℝ) / 65536) 254 := by
  apply RH1E6S03.part_057_0 <;> assumption
