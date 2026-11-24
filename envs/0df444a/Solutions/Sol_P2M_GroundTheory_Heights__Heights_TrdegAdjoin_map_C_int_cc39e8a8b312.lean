-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_C_int_cc39e8a8b312
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:48.403815+00:00
-- url     : https://prove2.me/submissions/cd431d42-b843-4bbd-a80b-61ed05a79159

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
variable {σ : Type} [Fintype σ] {L : Type} [CommRing L] [IsDomain L] [Algebra ℚ L]
omit [Fintype σ] [IsDomain L]
namespace GroundTheory.Heights₂.Heights.TrdegAdjoin
theorem _root_.solution (φ : MvPolynomial σ ℤ →+* L) (m : ℤ) : φ (C m) = algebraMap ℚ L m := by
  have h1 : φ (C m) = (m : L) := eq_intCast (φ.comp C) m
  rw [h1, map_intCast]
end GroundTheory.Heights₂.Heights.TrdegAdjoin
