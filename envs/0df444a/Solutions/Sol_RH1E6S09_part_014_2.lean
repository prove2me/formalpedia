-- Prove2me | solution 1 for RH1E6S09.part_014_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:50:20.013121+00:00
-- url     : https://prove2.me/submissions/b65dfbb3-dd30-49c1-87ee-8009abeb76c2

import Definitions.Def_RH1E6S09_D014_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem band_0116 : RS5.BandZeros ((36577512303 : ℝ) / 65536) ((36582095318 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0116.s0 RH1E6S09_0116.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0116.s0 RH1E6S09_0116.rest = RH1E6S09_0116.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0116.s0 :: RH1E6S09_0116.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0116.s0.t = ((36577512303 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0116.s0]
  have e1 : RH1E6S09_0116.sL.t = ((36582095318 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0116.sL]
  rw [e0, e1] at h
  exact h

theorem band_0117 : RS5.BandZeros ((36582095318 : ℝ) / 65536) ((36586682462 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S09_0117.s0 RH1E6S09_0117.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S09_0117.s0 RH1E6S09_0117.rest = RH1E6S09_0117.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S09_0117.s0 :: RH1E6S09_0117.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S09_0117.s0.t = ((36582095318 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0117.s0]
  have e1 : RH1E6S09_0117.sL.t = ((36586682462 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S09_0117.sL]
  rw [e0, e1] at h
  exact h

theorem part_014_2 : RS5.BandZeros ((36577512303 : ℝ) / 65536) ((36586682462 : ℝ) / 65536) 254 := by
  have g0 := band_0116
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0117
  exact g1

end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36577512303 : ℝ) / 65536) ((36586682462 : ℝ) / 65536) 254 := by
  apply RH1E6S09.part_014_2 <;> assumption
