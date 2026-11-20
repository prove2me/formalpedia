-- Prove2me | solution 1 for RH1E6S00.part_035_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:56:39.605039+00:00
-- url     : https://prove2.me/submissions/6a28c9ff-d4ed-4db9-a2ff-b11d5f324ae4

import Definitions.Def_RH1E6S00_D035_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem band_0282 : RS5.BandZeros ((8061192722 : ℝ) / 65536) ((8066505314 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0282.s0 RH1E6S00_0282.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0282.s0 RH1E6S00_0282.rest = RH1E6S00_0282.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0282.s0 :: RH1E6S00_0282.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0282.s0.t = ((8061192722 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0282.s0]
  have e1 : RH1E6S00_0282.sL.t = ((8066505314 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0282.sL]
  rw [e0, e1] at h
  exact h

theorem band_0283 : RS5.BandZeros ((8066505314 : ℝ) / 65536) ((8071775889 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S00_0283.s0 RH1E6S00_0283.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S00_0283.s0 RH1E6S00_0283.rest = RH1E6S00_0283.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S00_0283.s0 :: RH1E6S00_0283.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S00_0283.s0.t = ((8066505314 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0283.s0]
  have e1 : RH1E6S00_0283.sL.t = ((8071775889 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S00_0283.sL]
  rw [e0, e1] at h
  exact h

theorem part_035_1 : RS5.BandZeros ((8061192722 : ℝ) / 65536) ((8071775889 : ℝ) / 65536) 254 := by
  have g0 := band_0282
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0283
  exact g1

end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8061192722 : ℝ) / 65536) ((8071775889 : ℝ) / 65536) 254 := by
  apply RH1E6S00.part_035_1 <;> assumption
