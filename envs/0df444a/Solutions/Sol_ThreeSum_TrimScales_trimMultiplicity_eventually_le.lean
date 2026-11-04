-- Prove2me | solution 1 for ThreeSum.TrimScales.trimMultiplicity_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:44.910612+00:00
-- url     : https://prove2.me/submissions/2b5e6e5f-f42c-404e-8252-f185a556efb7

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_TrimScales_trimMultiplicity_log_rate
import Theorems.Thm_ThreeSum_Scales_eventually_le_rpow_of_log_ratio


set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (trimMultiplicity n : ℝ) ≤ (n : ℝ) ^ (Parameters.kappa / 5 + d) :=
  eventually_le_rpow_of_log_ratio trimMultiplicity_log_rate hd
end ThreeSum.TrimScales
