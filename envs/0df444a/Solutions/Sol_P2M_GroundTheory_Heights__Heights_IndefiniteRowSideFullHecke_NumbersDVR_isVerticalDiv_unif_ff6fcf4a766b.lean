-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isVerticalDiv_unif_ff6fcf4a766b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:52:34.680132+00:00
-- url     : https://prove2.me/submissions/2ed1ed24-7fc1-4830-acb0-7ad0eff2e5e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_GroundTheory_ArithmeticGeometry_IwasawaModules_SpanFinrankMaximalIdealLeTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_mem_of_mem_support_divCycle_766366323b69
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_mem_of_mem_support_divO_e1f14c7b20c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_isMultiHomog_C_cab39863dc5a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
universe u v w
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
theorem _root_.solution (ϖ : O) {P : Ideal (MRingOver O ι)} (hP : P.IsPrime) :
    IsVerticalDiv ϖ P 0 (C ϖ) 1 := by
  refine ⟨⟨0, 0, isMultiHomog_C ϖ, by simpa using isMultiHomog_C (ι := ι) (1 : O), by simp⟩,
    hP.one_notMem, fun W hW => ?_⟩
  rcases mem_of_mem_support_divO hW with h | h
  · exact (mem_of_mem_support_divCycle h).2
  · exact absurd (mem_of_mem_support_divCycle h).2 (mem_of_mem_support_divCycle h).1.one_notMem
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
