-- Prove2me | solution 1 for RH1E6S02.part_066_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T04:28:11.432709+00:00
-- url     : https://prove2.me/submissions/4e6716d3-ff63-46e4-9635-ec40351da6c2

import Definitions.Def_RH1E6S02_D066_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem band_0528 : RS5.BandZeros ((15746279814 : ℝ) / 65536) ((15751265115 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0528.s0 RH1E6S02_0528.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0528.s0 RH1E6S02_0528.rest = RH1E6S02_0528.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0528.s0 :: RH1E6S02_0528.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0528.s0.t = ((15746279814 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0528.s0]
  have e1 : RH1E6S02_0528.sL.t = ((15751265115 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0528.sL]
  rw [e0, e1] at h
  exact h

theorem band_0529 : RS5.BandZeros ((15751265115 : ℝ) / 65536) ((15756194449 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S02_0529.s0 RH1E6S02_0529.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S02_0529.s0 RH1E6S02_0529.rest = RH1E6S02_0529.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S02_0529.s0 :: RH1E6S02_0529.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S02_0529.s0.t = ((15751265115 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0529.s0]
  have e1 : RH1E6S02_0529.sL.t = ((15756194449 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S02_0529.sL]
  rw [e0, e1] at h
  exact h

theorem part_066_0 : RS5.BandZeros ((15746279814 : ℝ) / 65536) ((15756194449 : ℝ) / 65536) 254 := by
  have g0 := band_0528
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0529
  exact g1

end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15746279814 : ℝ) / 65536) ((15756194449 : ℝ) / 65536) 254 := by
  apply RH1E6S02.part_066_0 <;> assumption
