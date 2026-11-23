-- Prove2me | solution 1 for RH1E6S13.part_089_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:16:28.875411+00:00
-- url     : https://prove2.me/submissions/28a9e183-33b6-45fb-8c0c-d722f87dd9e1

import Definitions.Def_RH1E6S13_D089_1
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0714 : RS5.BandZeros ((52337464489 : ℝ) / 65536) ((52341914106 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0714.s0 RH1E6S13_0714.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0714.s0 RH1E6S13_0714.rest = RH1E6S13_0714.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0714.s0 :: RH1E6S13_0714.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0714.s0.t = ((52337464489 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0714.s0]
  have e1 : RH1E6S13_0714.sL.t = ((52341914106 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0714.sL]
  rw [e0, e1] at h
  exact h

theorem band_0715 : RS5.BandZeros ((52341914106 : ℝ) / 65536) ((52346363690 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0715.s0 RH1E6S13_0715.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0715.s0 RH1E6S13_0715.rest = RH1E6S13_0715.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0715.s0 :: RH1E6S13_0715.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0715.s0.t = ((52341914106 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0715.s0]
  have e1 : RH1E6S13_0715.sL.t = ((52346363690 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0715.sL]
  rw [e0, e1] at h
  exact h

theorem part_089_1 : RS5.BandZeros ((52337464489 : ℝ) / 65536) ((52346363690 : ℝ) / 65536) 254 := by
  have g0 := band_0714
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0715
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((52337464489 : ℝ) / 65536) ((52346363690 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_089_1 <;> assumption
