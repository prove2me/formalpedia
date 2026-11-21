-- Prove2me | solution 1 for RH1E6S05.part_038_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T13:58:56.122253+00:00
-- url     : https://prove2.me/submissions/5b62d232-fef0-444b-9eff-b65480e9aa6e

import Definitions.Def_RH1E6S05_D038_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0308 : RS5.BandZeros ((24407325924 : ℝ) / 65536) ((24412103105 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0308.s0 RH1E6S05_0308.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0308.s0 RH1E6S05_0308.rest = RH1E6S05_0308.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0308.s0 :: RH1E6S05_0308.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0308.s0.t = ((24407325924 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0308.s0]
  have e1 : RH1E6S05_0308.sL.t = ((24412103105 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0308.sL]
  rw [e0, e1] at h
  exact h

theorem band_0309 : RS5.BandZeros ((24412103105 : ℝ) / 65536) ((24416852101 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0309.s0 RH1E6S05_0309.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0309.s0 RH1E6S05_0309.rest = RH1E6S05_0309.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0309.s0 :: RH1E6S05_0309.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0309.s0.t = ((24412103105 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0309.s0]
  have e1 : RH1E6S05_0309.sL.t = ((24416852101 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0309.sL]
  rw [e0, e1] at h
  exact h

theorem part_038_2 : RS5.BandZeros ((24407325924 : ℝ) / 65536) ((24416852101 : ℝ) / 65536) 254 := by
  have g0 := band_0308
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0309
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24407325924 : ℝ) / 65536) ((24416852101 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_038_2 <;> assumption
