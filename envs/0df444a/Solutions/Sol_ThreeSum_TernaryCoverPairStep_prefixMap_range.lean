-- Prove2me | solution 1 for ThreeSum.TernaryCoverPairStep.prefixMap_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:55.879554+00:00
-- url     : https://prove2.me/submissions/820b43ae-a0b7-4950-8bcc-8420967c29b9

import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverPairStep
open Finset TernaryCoverRankFibers
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
namespace ThreeSum.TernaryCoverPairStep
theorem _root_.solution (S : Submodule K (X × (K × K))) :
    LinearMap.range (prefixMap S) = prefixSpace S := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.val, s.property, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
end ThreeSum.TernaryCoverPairStep
