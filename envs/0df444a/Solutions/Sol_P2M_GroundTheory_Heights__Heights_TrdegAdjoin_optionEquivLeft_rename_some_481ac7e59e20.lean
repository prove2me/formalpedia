-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoin_optionEquivLeft_rename_some_481ac7e59e20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:51.121857+00:00
-- url     : https://prove2.me/submissions/71e5bef6-98dc-42c3-a4bf-d23a6ea52e14

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
variable {M : Type} [CommRing M] [IsDomain M] [Algebra ℚ M]
namespace GroundTheory.Heights₂.Heights.TrdegAdjoin
theorem _root_.solution {K κ : Type} [CommRing K] (a : MvPolynomial κ K) :
    optionEquivLeft K κ (rename some a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on with
  | C k => rw [rename_C, optionEquivLeft_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.C_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, rename_X, optionEquivLeft_X_some, Polynomial.C_mul]
end GroundTheory.Heights₂.Heights.TrdegAdjoin
