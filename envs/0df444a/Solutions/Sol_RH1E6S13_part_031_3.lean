-- Prove2me | solution 1 for RH1E6S13.part_031_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T22:11:32.370621+00:00
-- url     : https://prove2.me/submissions/bc469027-fd21-48eb-aea6-27ffb1ccbc71

import Definitions.Def_RH1E6S13_D031_3
import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem band_0254 : RS5.BandZeros ((50287179708 : ℝ) / 65536) ((50291626928 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0254.s0 RH1E6S13_0254.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0254.s0 RH1E6S13_0254.rest = RH1E6S13_0254.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0254.s0 :: RH1E6S13_0254.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0254.s0.t = ((50287179708 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0254.s0]
  have e1 : RH1E6S13_0254.sL.t = ((50291626928 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0254.sL]
  rw [e0, e1] at h
  exact h

theorem band_0255 : RS5.BandZeros ((50291626928 : ℝ) / 65536) ((50296109269 : ℝ) / 65536) 127 := by
  have h := RS5.bandZeros_of_ok_prime RH1E6S13_0255.s0 RH1E6S13_0255.rest (by decide +kernel)
  have hl : RS5.lastOf RH1E6S13_0255.s0 RH1E6S13_0255.rest = RH1E6S13_0255.sL := rfl
  have hc : RS5.chgBy RS5.Sample.pos (RH1E6S13_0255.s0 :: RH1E6S13_0255.rest) = 127 := by decide +kernel
  rw [hl, hc] at h
  have e0 : RH1E6S13_0255.s0.t = ((50291626928 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0255.s0]
  have e1 : RH1E6S13_0255.sL.t = ((50296109269 : ℝ) / 65536) := by norm_num [RS5.Sample.t, RH1E6S13_0255.sL]
  rw [e0, e1] at h
  exact h

theorem part_031_3 : RS5.BandZeros ((50287179708 : ℝ) / 65536) ((50296109269 : ℝ) / 65536) 254 := by
  have g0 := band_0254
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 band_0255
  exact g1

end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50287179708 : ℝ) / 65536) ((50296109269 : ℝ) / 65536) 254 := by
  apply RH1E6S13.part_031_3 <;> assumption
