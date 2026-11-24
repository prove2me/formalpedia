-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabDivCycle_proof_3cb2a32c78c1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:36.068584+00:00
-- url     : https://prove2.me/submissions/4cb48f02-e7a0-4b2e-bd12-46ef570ac577

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabDivCycle

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
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace VocabDivCycle
theorem _root_.solution : VocabDivCycle.Statement := by
  intro R _ _ K _ ι _ P s W
  classical
  have e : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℕ) = if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s then
      ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W else 0 := by
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
  rw [e, divCycle]
  by_cases h : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s
  · have h' : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W := h
    have hW : W.IsPrime := h'.1.1.1
    rw [if_pos h, dif_pos h', ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos hW]
    rfl
  · have h' : ¬ (W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W) := h
    rw [if_neg h, dif_neg h']
    rfl
end VocabDivCycle
end GroundTheory.Heights₂.Heights.NumbersDVR
