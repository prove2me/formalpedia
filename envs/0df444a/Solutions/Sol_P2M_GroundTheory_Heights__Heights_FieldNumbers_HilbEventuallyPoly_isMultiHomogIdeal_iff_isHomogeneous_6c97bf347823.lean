-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbEventuallyPoly_isMultiHomogIdeal_iff_isHomogeneous_6c97bf347823
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:00.607516+00:00
-- url     : https://prove2.me/submissions/d5cd59cc-44e2-4892-a43e-44cb6f469574

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HilbEventuallyPolyQualified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
theorem _root_.solution (I : Ideal (MRing ι F)) :
    IsMultiHomogIdeal I ↔ I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := by
  constructor
  · intro h b f hf
    have key : (DirectSum.decompose (weightedHomogeneousSubmodule F (blockWeight ι)) f b :
        MRing ι F) = weightedHomogeneousComponent (blockWeight ι) b f :=
      weightedDecomposition.decompose'_apply F (blockWeight ι) f b
    rw [key]
    exact h f hf b
  · intro h f hf b
    exact weightedHomogeneousComponent_mem_of_mem F (blockWeight ι) h hf b
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly
