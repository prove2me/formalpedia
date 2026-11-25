-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_abs_quad_le_949e60e6298d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:20.995497+00:00
-- url     : https://prove2.me/submissions/7174634d-c9f2-447c-8653-104880c26b68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCBounds_abs_mul_le_dot_107bf1204f91

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ entrySum A * (x ⬝ᵥ x) := by
  have h : x ⬝ᵥ (A *ᵥ x) = ∑ j, ∑ k, x j * A j k * x k := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h, entrySum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul]
  calc |x j| * |A j k| * |x k| = |A j k| * (|x j| * |x k|) := by ring
    _ ≤ |A j k| * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_left (abs_mul_le_dot x j k) (abs_nonneg _)
end GroundTheory.Heights₂.Heights.MCBounds
