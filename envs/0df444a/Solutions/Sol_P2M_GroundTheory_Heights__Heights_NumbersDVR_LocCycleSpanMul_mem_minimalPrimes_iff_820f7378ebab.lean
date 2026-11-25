-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_LocCycleSpanMul_mem_minimalPrimes_iff_820f7378ebab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:32:43.528413+00:00
-- url     : https://prove2.me/submissions/9b333c59-f3f7-4feb-9395-a68db6de32ea

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Yhd1_mem_minimalPrimes_iff__ab28280ba29f
import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemMinimalPrimesIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocCycleSpanMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace LocCycleSpanMul
theorem _root_.solution {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {z : A} (hz : z ≠ 0) (W : Ideal A) :
    W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ z ∈ W :=
  _root_.P2M_UpperTheory_Reformulated_B_Yhd1_mem_minimalPrimes_iff__ab28280ba29f hz W
end LocCycleSpanMul
end GroundTheory.Heights₂.Heights.NumbersDVR
