-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isMultiProjPrime_map_052c7feb9148
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:11.023813+00:00
-- url     : https://prove2.me/submissions/fcb9413e-c553-4559-9ee7-a98c515273a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isPrime_map_4e84efccef29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isMultiHomogIdeal_map_c8689bb35698
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isRelevant_map_iff_44c6feca16d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_map_e1ed5f7bf88c


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
variable (e : K ≃ K') (σ : (Σ k, ι k) ≃ (Σ k', ι' k')) (hσ : ∀ p, (σ p).1 = e p.1)
include hσ
namespace GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
theorem _root_.solution {V : Ideal (MRingOver F ι)} (h : IsMultiProjPrime V) :
    IsMultiProjPrime (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) := by
  obtain ⟨hp, hh, hr⟩ := h
  exact ⟨isPrime_map _ V, isMultiHomogIdeal_map e σ hσ hh,
    (isRelevant_map_iff e σ hσ V).2 hr⟩
end GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
