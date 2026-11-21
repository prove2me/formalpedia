-- Prove2me | solution 1 for RH1E6S07.part_086_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T03:51:04.622305+00:00
-- url     : https://prove2.me/submissions/90548395-0126-49cf-a20f-191e0bedded8

import Definitions.Def_RH1E6S07_D086_0
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem band_0688 : RS5.BandZeros ((32694601806 : ℝ) / 65536) ((32699244983 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0688.s0 RH1E6S07_0688.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0688.s0 RH1E6S07_0688.rest = RH1E6S07_0688.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0688.s0 :: RH1E6S07_0688.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0688.s0.t = ((32694601806 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0688.s0]
  have e1 : RH1E6S07_0688.sL.t = ((32699244983 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0688.sL]
  rw [e0, e1] at h
  exact h

theorem band_0689 : RS5.BandZeros ((32699244983 : ℝ) / 65536) ((32703865155 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S07_0689.s0 RH1E6S07_0689.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S07_0689.s0 RH1E6S07_0689.rest = RH1E6S07_0689.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S07_0689.s0 :: RH1E6S07_0689.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S07_0689.s0.t = ((32699244983 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0689.s0]
  have e1 : RH1E6S07_0689.sL.t = ((32703865155 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S07_0689.sL]
  rw [e0, e1] at h
  exact h

theorem part_086_0 : RS5.BandZeros ((32694601806 : ℝ) / 65536) ((32703865155 : ℝ) / 65536) 254 := by
  have g0 := band_0688
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0689
  exact g1

end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32694601806 : ℝ) / 65536) ((32703865155 : ℝ) / 65536) 254 := by
  apply RH1E6S07.part_086_0 <;> assumption
