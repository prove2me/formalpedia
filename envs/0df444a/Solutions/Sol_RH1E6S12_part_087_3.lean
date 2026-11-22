-- Prove2me | solution 1 for RH1E6S12.part_087_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:33:32.840221+00:00
-- url     : https://prove2.me/submissions/a35d5926-cc32-44e7-94c3-2bb607c7d988

import Definitions.Def_RH1E6S12_D087_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem band_0702 : RS5.BandZeros ((49025172457 : ℝ) / 65536) ((49029653621 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0702.s0 RH1E6S12_0702.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0702.s0 RH1E6S12_0702.rest = RH1E6S12_0702.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0702.s0 :: RH1E6S12_0702.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0702.s0.t = ((49025172457 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0702.s0]
  have e1 : RH1E6S12_0702.sL.t = ((49029653621 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0702.sL]
  rw [e0, e1] at h
  exact h

theorem band_0703 : RS5.BandZeros ((49029653621 : ℝ) / 65536) ((49034114489 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S12_0703.s0 RH1E6S12_0703.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S12_0703.s0 RH1E6S12_0703.rest = RH1E6S12_0703.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S12_0703.s0 :: RH1E6S12_0703.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S12_0703.s0.t = ((49029653621 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0703.s0]
  have e1 : RH1E6S12_0703.sL.t = ((49034114489 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S12_0703.sL]
  rw [e0, e1] at h
  exact h

theorem part_087_3 : RS5.BandZeros ((49025172457 : ℝ) / 65536) ((49034114489 : ℝ) / 65536) 254 := by
  have g0 := band_0702
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0703
  exact g1

end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((49025172457 : ℝ) / 65536) ((49034114489 : ℝ) / 65536) 254 := by
  apply RH1E6S12.part_087_3 <;> assumption
