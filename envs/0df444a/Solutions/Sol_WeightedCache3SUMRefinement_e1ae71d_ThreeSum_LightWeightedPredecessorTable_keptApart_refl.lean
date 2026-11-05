-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable.keptApart_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:11:14.108332+00:00
-- url     : https://prove2.me/submissions/08324c75-8e09-4e8d-aa0e-f70137121008

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PredecessorTable

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
theorem _root_.solution (μ : ℕ → ℤ) (dst stride n : ℕ) : KeptApart μ μ dst stride n :=
  fun _ _ => rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
