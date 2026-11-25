-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperSheetedFibreEsymm_norm_esymm_map_le_3b7e6e724f88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:00.427232+00:00
-- url     : https://prove2.me/submissions/e7ecaae1-593c-4003-aeb2-828e5830e16a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperSheetedFibreEsymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperSheetedFibreEsymm

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
open Topology Filter Set Complex
open scoped Real
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
theorem _root_.solution {ι : Type*} (S : Finset ι) (f : ι → ℂ) (j : ℕ) {C : ℝ} (hC : ∀ x ∈ S, ‖f x‖ ≤ C) :
    ‖(S.val.map f).esymm j‖ ≤ (S.card.choose j : ℝ) * C ^ j := by
  rw [Finset.esymm_map_val]
  calc ‖∑ u ∈ S.powersetCard j, ∏ x ∈ u, f x‖ ≤ ∑ u ∈ S.powersetCard j, ‖∏ x ∈ u, f x‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ S.powersetCard j, C ^ j := by
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨hu1, hu2⟩ := Finset.mem_powersetCard.1 hu
        rw [norm_prod, ← hu2, ← Finset.prod_const]
        exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun x hx => hC x (hu1 hx)
    _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ProperSheetedFibreEsymm
