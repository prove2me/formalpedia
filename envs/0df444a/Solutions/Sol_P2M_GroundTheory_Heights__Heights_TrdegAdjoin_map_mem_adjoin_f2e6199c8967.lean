-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_mem_adjoin_f2e6199c8967
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:50.265116+00:00
-- url     : https://prove2.me/submissions/0d276ae6-cea6-41d5-987c-a5e0f8347519

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_C_int_cc39e8a8b312

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
theorem _root_.solution (φ : MvPolynomial σ ℤ →+* L) (g : MvPolynomial σ ℤ) :
    φ g ∈ adjoin ℚ (Set.range fun v ↦ φ (X v)) := by
  induction g using MvPolynomial.induction_on with
  | C a => rw [map_C_int]; exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p v hp => rw [map_mul]; exact mul_mem hp (subset_adjoin ⟨v, rfl⟩)
end GroundTheory.Heights₂.Heights.TrdegAdjoin
