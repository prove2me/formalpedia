-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPhysicalPairWordBounds.weighted_abs_le_of_seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:42:36.000193+00:00
-- url     : https://prove2.me/submissions/65c4daa1-3112-4f2b-810d-495a2c785730

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Definitions.Def_Submission_Weighted_Global_TernaryPhysicalPairWordBounds
import Theorems.Thm_ThreeSum_WeightedGlobalPhysicalPairWordBounds_weighted_abs_le

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPhysicalPairWordBounds
open Finset WeightedGlobalNativePairMoments WeightedGlobalNativeMomentBounds
open scoped BigOperators
namespace ThreeSum.WeightedGlobalPhysicalPairWordBounds
theorem _root_.solution {N d boundary : ℕ} {lim : Light.Limits}
    (S : WeightedSourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ)
    (H : WeightedSourceCountExecutionFactory.Seed S lim d boundary μ leftWeight rightWeight) :
    |weighted S leftWeight rightWeight i|≤(scoreBound S : ℤ) :=
  weighted_abs_le S leftWeight rightWeight i H.left.hweightBound H.right.hweightBound
end ThreeSum.WeightedGlobalPhysicalPairWordBounds
