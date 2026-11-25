-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LatticePointCount_log_error_le_303c1986598d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:04.906905+00:00
-- url     : https://prove2.me/submissions/93db228f-38ab-4ea2-a582-718cc596d92a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_HilbDegreeBoundAltOfStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
namespace LatticePointCount
theorem _root_.solution {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    (r : ℝ) * Real.log (2 * (1 + r * C)) ≤
      (1 + Real.log (2 * (1 + C)) / Real.log 2) * (((r : ℝ) + 1) * Real.log ((r : ℝ) + 1)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrC : 0 ≤ (r : ℝ) * C := mul_nonneg (Nat.cast_nonneg r) hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : Real.log 2 ≤ Real.log ((r : ℝ) + 1) := Real.log_le_log two_pos (by linarith)
  have hc : 0 ≤ Real.log (2 * (1 + C)) := Real.log_nonneg (by linarith)
  have hX0 : 0 ≤ Real.log (2 * (1 + r * C)) := Real.log_nonneg (by linarith)
  have hX : Real.log (2 * (1 + r * C)) ≤ Real.log (2 * (1 + C)) + Real.log ((r : ℝ) + 1) := by
    rw [← Real.log_mul (by linarith : (0 : ℝ) < 2 * (1 + C)).ne' (by positivity)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hcL : Real.log (2 * (1 + C)) ≤
      Real.log (2 * (1 + C)) / Real.log 2 * Real.log ((r : ℝ) + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hL hc
  have hK : Real.log (2 * (1 + r * C)) ≤
      (1 + Real.log (2 * (1 + C)) / Real.log 2) * Real.log ((r : ℝ) + 1) := by
    have e : (1 + Real.log (2 * (1 + C)) / Real.log 2) * Real.log ((r : ℝ) + 1) =
        Real.log ((r : ℝ) + 1) + Real.log (2 * (1 + C)) / Real.log 2 * Real.log ((r : ℝ) + 1) := by
      ring
    rw [e]
    linarith
  calc (r : ℝ) * Real.log (2 * (1 + r * C)) ≤ ((r : ℝ) + 1) * Real.log (2 * (1 + r * C)) :=
        mul_le_mul_of_nonneg_right (by linarith) hX0
    _ ≤ ((r : ℝ) + 1) * ((1 + Real.log (2 * (1 + C)) / Real.log 2) * Real.log ((r : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hK (by linarith)
    _ = (1 + Real.log (2 * (1 + C)) / Real.log 2) * (((r : ℝ) + 1) * Real.log ((r : ℝ) + 1)) := by
        ring
end LatticePointCount
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
