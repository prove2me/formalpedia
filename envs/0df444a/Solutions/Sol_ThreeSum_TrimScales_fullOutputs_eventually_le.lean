-- Prove2me | solution 1 for ThreeSum.TrimScales.fullOutputs_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:46.140439+00:00
-- url     : https://prove2.me/submissions/17442540-9733-4142-98ee-43f862468aba

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_WeightedCache3SUM_Alias_612fa2b177f14593
import Theorems.Thm_ThreeSum_Scales_eventually_le_rpow_of_log_ratio


set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (fullOutputs n : ℝ) ≤ (n : ℝ) ^ (2 * Parameters.E / 5 + d) :=
  eventually_le_rpow_of_log_ratio fullOutputs_log_rate hd
end ThreeSum.TrimScales
