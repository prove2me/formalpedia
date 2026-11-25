-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isRelevant_iff_053461e9f345
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:33.077908+00:00
-- url     : https://prove2.me/submissions/bce63e78-9cf0-464e-bb47-47b71f179875

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel

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
namespace GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
theorem _root_.solution (W : Ideal (MRingOver F ι)) :
    IsRelevant W ↔ ∀ k, ∃ p : Σ k, ι k, p.1 = k ∧ (X p : MRingOver F ι) ∉ W := by
  refine ⟨fun h k => ?_, fun h k => ?_⟩
  · obtain ⟨i, hi⟩ := h k
    exact ⟨⟨k, i⟩, rfl, hi⟩
  · obtain ⟨⟨a, b⟩, rfl, hp⟩ := h k
    exact ⟨b, hp⟩
end GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
