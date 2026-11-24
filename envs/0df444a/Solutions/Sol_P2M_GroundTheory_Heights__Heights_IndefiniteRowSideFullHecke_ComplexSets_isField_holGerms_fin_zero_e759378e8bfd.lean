-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isField_holGerms_fin_zero_e759378e8bfd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:44.263071+00:00
-- url     : https://prove2.me/submissions/0b5d4b3a-8fd0-4fee-8f11-e5aee2356fe1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution : IsField (holGerms (0 : Fin 0 → ℂ)) := by
  refine ⟨⟨0, 1, fun h => ?_⟩, mul_comm, fun {φ} hφ => ?_⟩
  · exact one_ne_zero (congrArg Subtype.val h).symm
  · obtain ⟨f, hf, hfφ⟩ := φ.2
    have hall : ∀ x : Fin 0 → ℂ, f x = f 0 := fun x => by rw [Subsingleton.elim x 0]
    have h0 : f 0 ≠ 0 := by
      intro h0
      apply hφ
      apply Subtype.ext
      rw [← hfφ]
      exact Germ.coe_eq.2 (Eventually.of_forall fun x => by rw [hall x, h0])
    refine ⟨⟨↑(fun x => (f x)⁻¹), fun x => (f x)⁻¹, hf.inv h0, rfl⟩, ?_⟩
    apply Subtype.ext
    change (φ : Germ (𝓝 (0 : Fin 0 → ℂ)) ℂ) * ↑(fun x => (f x)⁻¹) = 1
    rw [← hfφ]
    exact Germ.coe_eq.2 (Eventually.of_forall fun x => by
      show f x * (f x)⁻¹ = 1
      rw [hall x]
      exact mul_inv_cancel₀ h0)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
