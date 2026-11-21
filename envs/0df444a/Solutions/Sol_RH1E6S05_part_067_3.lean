-- Prove2me | solution 1 for RH1E6S05.part_067_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T15:57:53.414269+00:00
-- url     : https://prove2.me/submissions/5b5bccb7-a9d1-43bb-8eb0-e15e4e9008e1

import Definitions.Def_RH1E6S05_D067_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem band_0542 : RS5.BandZeros ((25518554181 : ℝ) / 65536) ((25523265443 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0542.s0 RH1E6S05_0542.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0542.s0 RH1E6S05_0542.rest = RH1E6S05_0542.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0542.s0 :: RH1E6S05_0542.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0542.s0.t = ((25518554181 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0542.s0]
  have e1 : RH1E6S05_0542.sL.t = ((25523265443 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0542.sL]
  rw [e0, e1] at h
  exact h

theorem band_0543 : RS5.BandZeros ((25523265443 : ℝ) / 65536) ((25528023271 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S05_0543.s0 RH1E6S05_0543.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S05_0543.s0 RH1E6S05_0543.rest = RH1E6S05_0543.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S05_0543.s0 :: RH1E6S05_0543.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S05_0543.s0.t = ((25523265443 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0543.s0]
  have e1 : RH1E6S05_0543.sL.t = ((25528023271 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S05_0543.sL]
  rw [e0, e1] at h
  exact h

theorem part_067_3 : RS5.BandZeros ((25518554181 : ℝ) / 65536) ((25528023271 : ℝ) / 65536) 254 := by
  have g0 := band_0542
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0543
  exact g1

end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25518554181 : ℝ) / 65536) ((25528023271 : ℝ) / 65536) 254 := by
  apply RH1E6S05.part_067_3 <;> assumption
