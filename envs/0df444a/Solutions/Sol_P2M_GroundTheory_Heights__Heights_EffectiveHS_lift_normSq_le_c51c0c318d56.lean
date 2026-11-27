-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_normSq_le_c51c0c318d56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:00.267041+00:00
-- url     : https://prove2.me/submissions/65132b0c-5f9b-45c3-9843-3d424fdcbc9c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_normSq_le_of_589f075b1e6f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open MeasureTheory
namespace GroundTheory.Heights₂.Heights.EffectiveHS
theorem _root_.solution {X ι : Type*} [MeasurableSpace X] (μ : Measure X) [Fintype ι]
    (D T : ℕ) (β r : ℝ) (hβ : 0 ≤ β) (u Ft : ι → X → ℂ) (rα G : ι → ℝ) (N : ℝ)
    (hu : ∀ i x, ‖u i x‖ ≤ rα i) (hFt : ∀ i, Integrable (fun x => ‖Ft i x‖ ^ 2) μ)
    (hL : ∀ i, ∫ x, ‖Ft i x‖ ^ 2 ∂μ ≤ 140 * cD D * r ^ (2 * D) * G i ^ 2)
    (hN : N ^ 2 ≤ β ^ (T + D + 1) * ∫ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ∂μ) :
    N ^ 2 ≤ (β ^ (T + D + 1) * 140 * cD D * (Fintype.card ι) * r ^ (2 * D)) *
      ∑ i, rα i ^ 2 * G i ^ 2 := by
  have h := lift_normSq_le_of μ u Ft rα G (140 * cD D * r ^ (2 * D)) (β ^ (T + D + 1)) N
    (by positivity) hu hFt hL hN
  calc N ^ 2 ≤ _ := h
    _ = _ := by ring
end GroundTheory.Heights₂.Heights.EffectiveHS
