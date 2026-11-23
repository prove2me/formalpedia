-- Prove2me | solution 1 for RH1E6S17.part_000_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:34:25.106256+00:00
-- url     : https://prove2.me/submissions/88ad4b44-9d99-4ea5-b0a7-c5cdf3e97f4a

import Definitions.Def_RH1E6S17_D000_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem band_0002 : RS5.BandZeros ((62267965376 : ℝ) / 65536) ((62272376072 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0002.s0 RH1E6S17_0002.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0002.s0 RH1E6S17_0002.rest = RH1E6S17_0002.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0002.s0 :: RH1E6S17_0002.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0002.s0.t = ((62267965376 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0002.s0]
  have e1 : RH1E6S17_0002.sL.t = ((62272376072 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0002.sL]
  rw [e0, e1] at h
  exact h

theorem band_0003 : RS5.BandZeros ((62272376072 : ℝ) / 65536) ((62276743584 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S17_0003.s0 RH1E6S17_0003.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S17_0003.s0 RH1E6S17_0003.rest = RH1E6S17_0003.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S17_0003.s0 :: RH1E6S17_0003.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S17_0003.s0.t = ((62272376072 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0003.s0]
  have e1 : RH1E6S17_0003.sL.t = ((62276743584 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S17_0003.sL]
  rw [e0, e1] at h
  exact h

theorem part_000_1 : RS5.BandZeros ((62267965376 : ℝ) / 65536) ((62276743584 : ℝ) / 65536) 254 := by
  have g0 := band_0002
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0003
  exact g1

end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((62267965376 : ℝ) / 65536) ((62276743584 : ℝ) / 65536) 254 := by
  apply RH1E6S17.part_000_1 <;> assumption
