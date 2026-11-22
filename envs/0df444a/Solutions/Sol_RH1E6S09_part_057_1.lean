-- Prove2me | solution 1 for RH1E6S09.part_057_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:53:12.05475+00:00
-- url     : https://prove2.me/submissions/6cd93f60-a891-4a93-86dd-6cf40c062806

import Definitions.Def_RH1E6S09_D057_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0458 : RS5.BandZeros ((38144217670 : ℝ) / 65536) ((38148798275 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0458.s0 RH1E6S09_0458.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0458.s0 RH1E6S09_0458.rest = RH1E6S09_0458.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0458.s0 :: RH1E6S09_0458.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0458.s0.t = ((38144217670 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0458.s0]
  have e1 : RH1E6S09_0458.sL.t = ((38148798275 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0458.sL]
  rw [e0, e1] at h
  exact h

theorem band_0459 : RS5.BandZeros ((38148798275 : ℝ) / 65536) ((38153377176 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0459.s0 RH1E6S09_0459.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0459.s0 RH1E6S09_0459.rest = RH1E6S09_0459.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0459.s0 :: RH1E6S09_0459.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0459.s0.t = ((38148798275 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0459.s0]
  have e1 : RH1E6S09_0459.sL.t = ((38153377176 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0459.sL]
  rw [e0, e1] at h
  exact h

theorem part_057_1 : RS5.BandZeros ((38144217670 : ℝ) / 65536) ((38153377176 : ℝ) / 65536) 254 := by
  have g0 := band_0458
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0459
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38144217670 : ℝ) / 65536) ((38153377176 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_057_1 <;> assumption
