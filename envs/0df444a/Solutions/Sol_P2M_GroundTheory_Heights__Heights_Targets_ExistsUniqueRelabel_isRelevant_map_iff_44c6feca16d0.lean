-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isRelevant_map_iff_44c6feca16d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:30:02.761375+00:00
-- url     : https://prove2.me/submissions/2c06aba5-ca4a-476e-8250-b9e7571736a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_mem_map_iff_702b680ecd84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isRelevant_iff_053461e9f345
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ren_X_11215966aa96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isRelevant_iff_3762d4b164c8


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
theorem _root_.solution (W : Ideal (MRingOver F ι)) :
    IsRelevant (W.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) ↔ IsRelevant W := by
  have hX : ∀ q : Σ k', ι' k', (X q : MRingOver F ι') = ren σ (X (σ.symm q)) := fun q => by
    rw [ren_X, Equiv.apply_symm_apply]
  rw [isRelevant_iff, isRelevant_iff]
  constructor
  · intro h k
    obtain ⟨q, hq, hX'⟩ := h (e k)
    refine ⟨σ.symm q, e.injective ?_, ?_⟩
    · rw [← hσ, Equiv.apply_symm_apply, hq]
    · rwa [hX, mem_map_iff] at hX'
  · intro h k'
    obtain ⟨p, hp, hX'⟩ := h (e.symm k')
    refine ⟨σ p, by rw [hσ, hp, Equiv.apply_symm_apply], ?_⟩
    rwa [← ren_X, mem_map_iff]
end GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
