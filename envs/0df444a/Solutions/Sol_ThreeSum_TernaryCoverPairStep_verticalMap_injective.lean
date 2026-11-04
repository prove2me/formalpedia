-- Prove2me | solution 1 for ThreeSum.TernaryCoverPairStep.verticalMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:28.699551+00:00
-- url     : https://prove2.me/submissions/56aefa5d-b64c-4e71-b3c8-5bc7b82c66eb

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
    Function.Injective (verticalMap S) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun v : S => v.val.2) h
end ThreeSum.TernaryCoverPairStep
