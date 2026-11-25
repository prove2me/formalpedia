-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KShort_convex_cube_06aa38fb496f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:20.272725+00:00
-- url     : https://prove2.me/submissions/2b242b5d-5f0c-4edc-ad23-7397fa3aea31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors

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
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort
namespace GroundTheory.Heights₂.Heights.KShort
theorem _root_.solution (n : ℕ) (c : ℝ) : Convex ℝ (cube n c) := by
  intro x hx y hy a b ha hb hab i
  have hxi := hx i
  have hyi := hy i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
    _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < c := by
      rcases ha.lt_or_eq with ha' | ha'
      · calc a * |x i| + b * |y i| < a * c + b * c := by
              have : b * |y i| ≤ b * c := mul_le_mul_of_nonneg_left hyi.le hb
              have : a * |x i| < a * c := mul_lt_mul_of_pos_left hxi ha'
              linarith
          _ = c := by rw [← add_mul, hab, one_mul]
      · subst ha'
        simp only [zero_add] at hab
        subst hab
        simpa using hyi
end GroundTheory.Heights₂.Heights.KShort
