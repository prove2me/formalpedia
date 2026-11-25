-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_exists_small_avoid_f177da726c82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:23.100076+00:00
-- url     : https://prove2.me/submissions/93b87a61-8b21-4ebc-bf0f-e476233f7b26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInvarianceOfDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInvarianceOfDomain

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
open Metric Set MeasureTheory
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
theorem _root_.solution {P : (Fin n → ℝ) → Fin n → ℝ} (hP : Differentiable ℝ P) (c a : Fin n → ℝ)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ v : Fin n → ℝ, ‖v‖ < δ ∧ ∀ y ∈ sphere c ρ, P y ≠ a + v := by
  have hnull : volume (P '' sphere c ρ) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hP.differentiableOn
      (Measure.addHaar_sphere_of_ne_zero volume c hρ.ne')
  by_contra! hall
  have hsub : ball a δ ⊆ P '' sphere c ρ := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hall (z - a) (by rwa [mem_ball, dist_eq_norm] at hz)
    exact ⟨y, hy, by rw [hyz]; abel⟩
  have hle := measure_mono (μ := volume) hsub
  rw [hnull] at hle
  exact (measure_ball_pos volume a hδ).ne' (nonpos_iff_eq_zero.mp hle)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
