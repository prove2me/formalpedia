-- Prove2me | solution 1 for RH1E6S05.part_054_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T14:37:00.79118+00:00
-- url     : https://prove2.me/submissions/9851cd44-869f-4bb7-9f0f-c75728c540f4

import Definitions.Def_RH1E6S05_D054_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0436 : RS5.BandZeros ((25015728239 : ℝ) / 65536) ((25020485397 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0436.s0 RH1E6S05_0436.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0436.s0 RH1E6S05_0436.rest = RH1E6S05_0436.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0436.s0 :: RH1E6S05_0436.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0436.s0.t = ((25015728239 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0436.s0]
  have e1 : RH1E6S05_0436.sL.t = ((25020485397 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0436.sL]
  rw [e0, e1] at h
  exact h

theorem band_0437 : RS5.BandZeros ((25020485397 : ℝ) / 65536) ((25025233126 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0437.s0 RH1E6S05_0437.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0437.s0 RH1E6S05_0437.rest = RH1E6S05_0437.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0437.s0 :: RH1E6S05_0437.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0437.s0.t = ((25020485397 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0437.s0]
  have e1 : RH1E6S05_0437.sL.t = ((25025233126 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0437.sL]
  rw [e0, e1] at h
  exact h

theorem part_054_2 : RS5.BandZeros ((25015728239 : ℝ) / 65536) ((25025233126 : ℝ) / 65536) 254 := by
  have g0 := band_0436
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0437
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25015728239 : ℝ) / 65536) ((25025233126 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_054_2 <;> assumption
