-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_toFrac_prod_ne_zero_82f3e7b02aa9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:27.817828+00:00
-- url     : https://prove2.me/submissions/bca474ad-5485-4e8e-b654-550f2b65e0d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_toFrac_eq_zero_5eaebcef54dc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
theorem _root_.solution {P : Ideal (MRing ι)} [P.IsPrime] (j : ∀ k, ι k)
    (hj : ∀ k, (X ⟨k, j k⟩ : MRing ι) ∉ P) (a : K → ℕ) :
    toFrac P (∏ k, (X ⟨k, j k⟩ : MRing ι) ^ a k) ≠ 0 := by
  simp only [map_prod, map_pow]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ fun h => hj k (toFrac_eq_zero.mp h)
end GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
