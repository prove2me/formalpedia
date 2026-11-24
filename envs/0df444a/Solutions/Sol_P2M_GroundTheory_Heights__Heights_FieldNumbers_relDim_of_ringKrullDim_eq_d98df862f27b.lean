-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_of_ringKrullDim_eq_d98df862f27b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:18.542664+00:00
-- url     : https://prove2.me/submissions/a4598554-3ec0-4705-9e1a-3358865e0d5f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivPrincipalDegree

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
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
omit [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (I : Ideal (MRing ι F)) (d : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = (d : WithBot ℕ∞)) :
    relDim I = (((d : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) := by
  unfold relDim
  rw [h]
  rfl
end GroundTheory.Heights₂.Heights.FieldNumbers
