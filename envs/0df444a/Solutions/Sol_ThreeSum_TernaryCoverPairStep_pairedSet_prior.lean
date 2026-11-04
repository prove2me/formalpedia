-- Prove2me | solution 1 for ThreeSum.TernaryCoverPairStep.pairedSet_prior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:57.159144+00:00
-- url     : https://prove2.me/submissions/7d6fffb5-a53a-45c3-9fae-575d772204d5

import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverPairStep
open Finset TernaryCoverRankFibers
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
variable {E Z ι : Type*} [Fintype E] [Fintype Z] [Fintype ι] [DecidableEq K]
namespace ThreeSum.TernaryCoverPairStep
theorem _root_.solution (left right : E → ι → K) (prior : Z → ι → X)
    (S : Submodule K (X × (K × K))) {ze : Z × E}
    (h : ze ∈ pairedSet left right prior S) : ze.1 ∈ priorSet prior S := by
  classical
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  intro i
  exact ⟨(prior ze.1 i, (left ze.2 i, right ze.2 i)), (mem_filter.mp h).2 i, rfl⟩
end ThreeSum.TernaryCoverPairStep
