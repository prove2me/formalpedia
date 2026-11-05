-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_abs_le_of_seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:45:30.364966+00:00
-- url     : https://prove2.me/submissions/07e0c7a8-2cae-4489-9ebb-faed06b46f10

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPhysicalPairWordBounds_weighted_abs_le

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalPairWordBounds
open Finset WeightedGlobalNativePairMoments WeightedGlobalNativeMomentBounds
open scoped BigOperators
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalPairWordBounds
theorem _root_.solution {N d boundary : ℕ} {lim : Light.Limits}
    (S : WeightedSourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ)
    (H : WeightedSourceCountExecutionFactory.Seed S lim d boundary μ leftWeight rightWeight) :
    |weighted S leftWeight rightWeight i|≤(scoreBound S : ℤ) :=
  weighted_abs_le S leftWeight rightWeight i H.left.hweightBound H.right.hweightBound
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPhysicalPairWordBounds
