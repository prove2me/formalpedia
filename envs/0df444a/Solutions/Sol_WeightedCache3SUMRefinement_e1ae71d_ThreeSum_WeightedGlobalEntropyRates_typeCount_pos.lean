-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates.typeCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:25:49.337979+00:00
-- url     : https://prove2.me/submissions/0be53c21-b006-4966-abaf-5ec5384e7026

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution {N r1 r2 : ℕ} (h1 : r1+r2 ≤ N) (m : ℕ) :
    0 < typeCount N r1 r2 m := by
  unfold typeCount
  exact Nat.mul_pos (Nat.choose_pos (Nat.mul_le_mul_right m (by omega)))
    (Nat.choose_pos (Nat.mul_le_mul_right m (by omega)))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
