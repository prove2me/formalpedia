-- Prove2me | solution 1 for RH1E6S05.part_020_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:53:34.764596+00:00
-- url     : https://prove2.me/submissions/86e2e605-8345-4ba6-9009-3abff48a4eb3

import Definitions.Def_RH1E6S05_D020_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0164 : RS5.BandZeros ((23721227027 : ℝ) / 65536) ((23725988459 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0164.s0 RH1E6S05_0164.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0164.s0 RH1E6S05_0164.rest = RH1E6S05_0164.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0164.s0 :: RH1E6S05_0164.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0164.s0.t = ((23721227027 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0164.s0]
  have e1 : RH1E6S05_0164.sL.t = ((23725988459 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0164.sL]
  rw [e0, e1] at h
  exact h

theorem band_0165 : RS5.BandZeros ((23725988459 : ℝ) / 65536) ((23730759195 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0165.s0 RH1E6S05_0165.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0165.s0 RH1E6S05_0165.rest = RH1E6S05_0165.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0165.s0 :: RH1E6S05_0165.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0165.s0.t = ((23725988459 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0165.s0]
  have e1 : RH1E6S05_0165.sL.t = ((23730759195 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0165.sL]
  rw [e0, e1] at h
  exact h

theorem part_020_2 : RS5.BandZeros ((23721227027 : ℝ) / 65536) ((23730759195 : ℝ) / 65536) 254 := by
  have g0 := band_0164
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0165
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23721227027 : ℝ) / 65536) ((23730759195 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_020_2 <;> assumption
