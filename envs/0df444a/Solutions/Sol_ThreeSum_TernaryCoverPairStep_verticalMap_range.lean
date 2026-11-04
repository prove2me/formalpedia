-- Prove2me | solution 1 for ThreeSum.TernaryCoverPairStep.verticalMap_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:54.470409+00:00
-- url     : https://prove2.me/submissions/bfb96720-e81a-434e-9ef9-07d521d3dbdf

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
    LinearMap.range (verticalMap S) = LinearMap.ker (prefixMap S) := by
  ext s
  constructor
  · rintro ⟨v, rfl⟩
    rfl
  · intro hs
    have hx : s.val.1 = 0 := hs
    let v : vertical S := ⟨s.val.2, by
      change (0, s.val.2) ∈ S
      have he : (0, s.val.2) = s.val := Prod.ext hx.symm rfl
      rw [he]
      exact s.property⟩
    refine ⟨v, ?_⟩
    apply Subtype.ext
    exact Prod.ext hx.symm rfl
end ThreeSum.TernaryCoverPairStep
