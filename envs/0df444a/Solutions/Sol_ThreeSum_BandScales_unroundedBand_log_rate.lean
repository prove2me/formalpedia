-- Prove2me | solution 1 for ThreeSum.BandScales.unroundedBand_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:13.047955+00:00
-- url     : https://prove2.me/submissions/971b87ca-d400-49ad-8d1b-825a85205fed

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_bandRoot_pos
import Theorems.Thm_ThreeSum_BandScales_bandDivisor_pos
import Definitions.Def_WeightedCache3SUM_Alias_8f301717a948972c
import Theorems.Thm_ThreeSum_BandScales_bandDivisor_log_rate

set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.BandScales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (unroundedBand n) / Real.log n) atTop
      (𝓝 ((Parameters.E - 1 / 20) / 5)) := by
  have h := bandRoot_log_rate.sub bandDivisor_log_rate
  have heq : Parameters.E / 5 - 1 / 100 = (Parameters.E - 1 / 20) / 5 := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [] with n
  have hR : (0 : ℝ) < bandRoot n := by exact_mod_cast bandRoot_pos n
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  rw [unroundedBand, Real.log_div hR.ne' hD.ne', sub_div]
end ThreeSum.BandScales
