-- Prove2me | solution 1 for RH1E6S01.part_018_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:58:32.500174+00:00
-- url     : https://prove2.me/submissions/9442d113-66bd-4f33-9f7f-2fd3f16d1a0c

import Definitions.Def_RH1E6S01_D018_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem band_0144 : RS5.BandZeros ((10574705093 : ℝ) / 65536) ((10579855451 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0144.s0 RH1E6S01_0144.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0144.s0 RH1E6S01_0144.rest = RH1E6S01_0144.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0144.s0 :: RH1E6S01_0144.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0144.s0.t = ((10574705093 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0144.s0]
  have e1 : RH1E6S01_0144.sL.t = ((10579855451 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0144.sL]
  rw [e0, e1] at h
  exact h

theorem band_0145 : RS5.BandZeros ((10579855451 : ℝ) / 65536) ((10584995424 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S01_0145.s0 RH1E6S01_0145.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S01_0145.s0 RH1E6S01_0145.rest = RH1E6S01_0145.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S01_0145.s0 :: RH1E6S01_0145.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S01_0145.s0.t = ((10579855451 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0145.s0]
  have e1 : RH1E6S01_0145.sL.t = ((10584995424 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S01_0145.sL]
  rw [e0, e1] at h
  exact h

theorem part_018_0 : RS5.BandZeros ((10574705093 : ℝ) / 65536) ((10584995424 : ℝ) / 65536) 254 := by
  have g0 := band_0144
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0145
  exact g1

end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((10574705093 : ℝ) / 65536) ((10584995424 : ℝ) / 65536) 254 := by
  apply RH1E6S01.part_018_0 <;> assumption
