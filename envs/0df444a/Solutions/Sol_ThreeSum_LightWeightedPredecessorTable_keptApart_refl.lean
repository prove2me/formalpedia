-- Prove2me | solution 1 for ThreeSum.LightWeightedPredecessorTable.keptApart_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:24.145692+00:00
-- url     : https://prove2.me/submissions/3ae478d3-af6d-4042-a6be-dc8684ad9c9f

import Definitions.Def_Submission_Weighted_Predecessor
import Definitions.Def_Submission_Weighted_PredecessorTable

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedPredecessorTable
theorem _root_.solution (μ : ℕ → ℤ) (dst stride n : ℕ) : KeptApart μ μ dst stride n :=
  fun _ _ => rfl
end ThreeSum.LightWeightedPredecessorTable
