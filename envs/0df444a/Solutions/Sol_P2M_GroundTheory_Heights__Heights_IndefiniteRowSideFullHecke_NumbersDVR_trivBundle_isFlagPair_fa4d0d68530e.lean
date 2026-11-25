-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_trivBundle_isFlagPair_fa4d0d68530e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:12.737866+00:00
-- url     : https://prove2.me/submissions/e374741d-0f7b-441a-8eb8-368ae1d7d86b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_trivBundle_isFlagGrading_b44ce4708f58
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
universe u v w u₁ u₂
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {o}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
theorem _root_.solution (N : ℕ) :
    IsFlagPair (genPt O ι) ⊥ (trivBundle O (segreVec (genPt O ι)) N)
      (trivBundle O (segreVec (genPt O ι)) N) (Pi.basisFun _ (Fin N)) 0 0 1 1 1 1 := by
  refine ⟨trivBundle_isFlagGrading _ N, trivBundle_isFlagGrading _ N, fun l => ⟨?_, ?_, rfl⟩⟩
  · exact ⟨0, 0, by simpa using isMultiHomog_C (ι := ι) (1 : O),
      by simpa using isMultiHomog_C (ι := ι) (1 : O), by simp⟩
  · exact Ideal.isPrime_bot.one_notMem
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
