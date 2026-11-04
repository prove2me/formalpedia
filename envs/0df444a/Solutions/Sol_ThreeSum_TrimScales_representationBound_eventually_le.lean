-- Prove2me | solution 1 for ThreeSum.TrimScales.representationBound_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:46.330292+00:00
-- url     : https://prove2.me/submissions/f449436d-3366-4b34-9569-1fc607800364

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_WeightedCache3SUM_Alias_dc2f19a97a662b74
import Theorems.Thm_ThreeSum_Scales_eventually_le_rpow_of_log_ratio


set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (representationBound n : ℝ) ≤ (n : ℝ) ^ (Parameters.kappa / 5 + d) :=
  eventually_le_rpow_of_log_ratio representationBound_log_rate hd
end ThreeSum.TrimScales
