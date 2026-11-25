-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_pt_in
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:40:22.986498+00:00
-- url     : https://prove2.me/submissions/c3626adf-b735-45c7-be33-31ded9fb00db

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (u E η D a I : ℝ) (hu : 0 ≤ u) (hE : 0 ≤ E) (h8 : 8 ≤ η) (hD : 2 * η ≤ D)
    (ha : 0 ≤ a) (hI : 2 * a * (E / η) ≤ I) :
    (Real.sqrt a + u * Real.sqrt (2 / η)) ^ 2 * (E / η) ≤
      (u ^ 2 * (E / η) - u ^ 2 * (E / D)) + I := by
  have hη : 0 < η := by linarith
  have hb : 0 ≤ 2 / η := by positivity
  have ham : 2 * Real.sqrt a * (u * Real.sqrt (2 / η)) ≤ a + u ^ 2 * (2 / η) := by
    have := two_mul_le_add_sq (Real.sqrt a) (u * Real.sqrt (2 / η))
    rwa [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb] at this
  have h1 : (Real.sqrt a + u * Real.sqrt (2 / η)) ^ 2 ≤ 2 * a + 2 * (u ^ 2 * (2 / η)) := by
    have e : (Real.sqrt a + u * Real.sqrt (2 / η)) ^ 2 = Real.sqrt a ^ 2 +
        2 * Real.sqrt a * (u * Real.sqrt (2 / η)) + u ^ 2 * Real.sqrt (2 / η) ^ 2 := by ring
    rw [e, Real.sq_sqrt ha, Real.sq_sqrt hb]
    linarith
  have hk := ap_key η D h8 hD
  calc (Real.sqrt a + u * Real.sqrt (2 / η)) ^ 2 * (E / η)
      ≤ (2 * a + 2 * (u ^ 2 * (2 / η))) * (E / η) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 2 * a * (E / η) + u ^ 2 * E * (4 / η ^ 2) := by field_simp; ring
    _ ≤ I + u ^ 2 * E * (1 / η - 1 / D) :=
        add_le_add hI (mul_le_mul_of_nonneg_left hk (by positivity))
    _ = (u ^ 2 * (E / η) - u ^ 2 * (E / D)) + I := by ring
end ReciprocityTheory.L2DbarEstimates.I
