-- Prove2me | solution 1 for RH1E6S05.part_008_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:25:49.665515+00:00
-- url     : https://prove2.me/submissions/fd32e996-e143-46f5-8021-c256da0b113a

import Definitions.Def_RH1E6S05_D008_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0066 : RS5.BandZeros ((23253248720 : ℝ) / 65536) ((23258018823 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0066.s0 RH1E6S05_0066.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0066.s0 RH1E6S05_0066.rest = RH1E6S05_0066.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0066.s0 :: RH1E6S05_0066.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0066.s0.t = ((23253248720 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0066.s0]
  have e1 : RH1E6S05_0066.sL.t = ((23258018823 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0066.sL]
  rw [e0, e1] at h
  exact h

theorem band_0067 : RS5.BandZeros ((23258018823 : ℝ) / 65536) ((23262807652 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0067.s0 RH1E6S05_0067.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0067.s0 RH1E6S05_0067.rest = RH1E6S05_0067.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0067.s0 :: RH1E6S05_0067.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0067.s0.t = ((23258018823 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0067.s0]
  have e1 : RH1E6S05_0067.sL.t = ((23262807652 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0067.sL]
  rw [e0, e1] at h
  exact h

theorem part_008_1 : RS5.BandZeros ((23253248720 : ℝ) / 65536) ((23262807652 : ℝ) / 65536) 254 := by
  have g0 := band_0066
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0067
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23253248720 : ℝ) / 65536) ((23262807652 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_008_1 <;> assumption
