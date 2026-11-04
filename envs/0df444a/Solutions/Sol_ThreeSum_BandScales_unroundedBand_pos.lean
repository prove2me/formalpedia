-- Prove2me | solution 1 for ThreeSum.BandScales.unroundedBand_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:17:12.536058+00:00
-- url     : https://prove2.me/submissions/e268fed5-ebe6-4f65-ae43-0e2bf36aecd4

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_bandRoot_pos
import Theorems.Thm_ThreeSum_BandScales_bandDivisor_pos

set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.BandScales
theorem _root_.solution (n : ℕ) : 0 < unroundedBand n := by
  have hR : (0 : ℝ) < bandRoot n := by exact_mod_cast bandRoot_pos n
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  exact div_pos hR hD
end ThreeSum.BandScales
