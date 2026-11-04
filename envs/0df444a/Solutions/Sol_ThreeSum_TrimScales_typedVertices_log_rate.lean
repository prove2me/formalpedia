-- Prove2me | solution 1 for ThreeSum.TrimScales.typedVertices_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:43.540652+00:00
-- url     : https://prove2.me/submissions/6edef052-5699-416d-acd6-21b5b35cb0b7

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_WeightedCache3SUM_Alias_8c840be79f696836
import Theorems.Thm_ThreeSum_BinomialEntropy_vertex_table_rate


set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (typedVertices n : ℝ) / Real.log n) atTop
      (𝓝 ((Parameters.E + 1 / 2 + Parameters.kappa / 2) / 5)) := by
  exact replicatedHalf_log_rate BinomialEntropy.vertex_table_rate
end ThreeSum.TrimScales
