-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoin_isAlgebraic_adjoin_range_iff_d7959a5f1b61
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:48.038749+00:00
-- url     : https://prove2.me/submissions/517665f2-60fd-4e1f-97c7-1446a0cdafd8

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TrdegAdjoin
open MvPolynomial Algebra Cardinal
attribute [local instance] MvPolynomial.algebraMvPolynomial
noncomputable section
variable {R L : Type} [Field R] [CommRing L] [IsDomain L] [Algebra R L]
omit [IsDomain L]
namespace GroundTheory.Heights₂.Heights.TrdegAdjoin
theorem _root_.solution (A : Subalgebra R L) {κ : Type} (x : κ → A) (a : A) :
    IsAlgebraic (adjoin R (Set.range (A.val ∘ x))) (a : L) ↔
      IsAlgebraic (adjoin R (Set.range x)) a := by
  have hmap : (adjoin R (Set.range x)).map A.val = adjoin R (Set.range (A.val ∘ x)) := by
    rw [AlgHom.map_adjoin, Set.range_comp]
  let e : adjoin R (Set.range x) ≃ₐ[R] adjoin R (Set.range (A.val ∘ x)) :=
    (Subalgebra.equivMapOfInjective _ A.val Subtype.val_injective).trans
      (Subalgebra.equivOfEq _ _ hmap)
  exact isAlgebraic_ringHom_iff_of_comp_eq e.toRingEquiv A.val Subtype.val_injective
    (RingHom.ext fun _ ↦ rfl)
end GroundTheory.Heights₂.Heights.TrdegAdjoin
