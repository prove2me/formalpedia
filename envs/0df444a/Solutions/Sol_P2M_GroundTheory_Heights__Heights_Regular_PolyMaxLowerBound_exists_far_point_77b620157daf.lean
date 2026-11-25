-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_far_point_77b620157daf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:24.825807+00:00
-- url     : https://prove2.me/submissions/76a64560-a27e-4c33-b3f5-cee9d5a65da9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PPolyMaxLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Set
open ReciprocityTheory.AnForm.A (polyMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace PolyMaxLowerBound
theorem _root_.solution {D : ℕ} (z : Fin D → ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ y ∈ closedBall z t, ∀ i, t / 2 ≤ ‖y i‖ := by
  classical
  refine ⟨fun i => if t / 2 ≤ ‖z i‖ then z i else z i + (t : ℂ), ?_, fun i => ?_⟩
  · rw [mem_closedBall, dist_pi_le_iff ht.le]
    intro i
    by_cases h : t / 2 ≤ ‖z i‖
    · simp only [if_pos h, dist_self]; exact ht.le
    · simp only [if_neg h, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, le_refl]
  · by_cases h : t / 2 ≤ ‖z i‖
    · simp only [if_pos h]; exact h
    · simp only [if_neg h]
      replace h := not_le.mp h
      have h1 : ‖((t : ℝ) : ℂ)‖ ≤ ‖z i + (t : ℂ)‖ + ‖z i‖ := by
        calc ‖((t : ℝ) : ℂ)‖ = ‖(z i + (t : ℂ)) - z i‖ := by ring_nf
          _ ≤ ‖z i + (t : ℂ)‖ + ‖z i‖ := norm_sub_le _ _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h1
      linarith
end PolyMaxLowerBound
end GroundTheory.Heights₂.Heights.Regular
