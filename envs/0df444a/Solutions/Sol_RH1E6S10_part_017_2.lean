-- Prove2me | solution 1 for RH1E6S10.part_017_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T18:45:20.156088+00:00
-- url     : https://prove2.me/submissions/c2e51dd3-80f0-4c00-b705-d8565f8571be

import Definitions.Def_RH1E6S10_D017_2
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem band_0140 : RS5.BandZeros ((39959646034 : ℝ) / 65536) ((39964218138 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0140.s0 RH1E6S10_0140.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0140.s0 RH1E6S10_0140.rest = RH1E6S10_0140.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0140.s0 :: RH1E6S10_0140.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0140.s0.t = ((39959646034 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0140.s0]
  have e1 : RH1E6S10_0140.sL.t = ((39964218138 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0140.sL]
  rw [e0, e1] at h
  exact h

theorem band_0141 : RS5.BandZeros ((39964218138 : ℝ) / 65536) ((39968763302 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S10_0141.s0 RH1E6S10_0141.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S10_0141.s0 RH1E6S10_0141.rest = RH1E6S10_0141.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S10_0141.s0 :: RH1E6S10_0141.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S10_0141.s0.t = ((39964218138 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0141.s0]
  have e1 : RH1E6S10_0141.sL.t = ((39968763302 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S10_0141.sL]
  rw [e0, e1] at h
  exact h

theorem part_017_2 : RS5.BandZeros ((39959646034 : ℝ) / 65536) ((39968763302 : ℝ) / 65536) 254 := by
  have g0 := band_0140
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0141
  exact g1

end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39959646034 : ℝ) / 65536) ((39968763302 : ℝ) / 65536) 254 := by
  apply RH1E6S10.part_017_2 <;> assumption
