-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RemovableHyperplane_update_mem_ball_one_5f61701915c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:21.328808+00:00
-- url     : https://prove2.me/submissions/6fe976b5-1b65-43eb-8367-435b68e7edd7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRemovableHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRemovableHyperplane

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
open Metric Filter Topology Set
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace RemovableHyperplane
theorem _root_.solution {m : ℕ} {z : Fin m → ℂ}
    (hz : z ∈ ball (0 : Fin m → ℂ) 1) (i : Fin m) {x : ℂ} (hx : ‖x‖ < 1) :
    Function.update z i x ∈ ball (0 : Fin m → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos] at hz ⊢
  intro l
  rcases eq_or_ne l i with rfl | h
  · simpa using hx
  · rw [Function.update_of_ne h]
    exact hz l
end RemovableHyperplane
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
