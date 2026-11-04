-- Prove2me | solution 1 for ThreeSum.TernaryCoverPairStep.rank_increment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:46.910882+00:00
-- url     : https://prove2.me/submissions/830cbbd7-34b5-4232-8a8e-cf48c5f57405

import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
import Theorems.Thm_ThreeSum_TernaryCoverPairStep_verticalMap_injective
import Theorems.Thm_ThreeSum_TernaryCoverPairStep_verticalMap_range
import Theorems.Thm_ThreeSum_TernaryCoverPairStep_prefixMap_range

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverPairStep
open Finset TernaryCoverRankFibers
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
namespace ThreeSum.TernaryCoverPairStep
theorem _root_.solution [Module.Finite K X] (S : Submodule K (X × (K × K))) :
    Module.finrank K (prefixSpace S) + Module.finrank K (vertical S) = Module.finrank K S := by
  have h := LinearMap.finrank_range_add_finrank_ker (prefixMap S)
  have hv := LinearMap.finrank_range_of_inj (verticalMap_injective S)
  rw [verticalMap_range] at hv
  rw [prefixMap_range, hv] at h
  exact h
end ThreeSum.TernaryCoverPairStep
