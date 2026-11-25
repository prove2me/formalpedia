-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.sqrt_add_sq_le_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:35.846718+00:00
-- url     : https://prove2.me/submissions/a07c659b-4c0b-4606-9d22-b55254a78cdd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian

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
theorem _root_.solution (x y : ℝ≥0∞) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hx : x ≤ ENNReal.ofReal X) (hy : y ≤ ENNReal.ofReal Y) :
    (x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ≤
      ENNReal.ofReal ((101 / 100) * X + 101 * Y) := by
  have h1 : x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt X) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hX (by norm_num)]
    exact ENNReal.rpow_le_rpow hx (by norm_num)
  have h2 : y ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt Y) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hY (by norm_num)]
    exact ENNReal.rpow_le_rpow hy (by norm_num)
  have h3 : x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt X + Real.sqrt Y) := by
    rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
    exact add_le_add h1 h2
  calc (x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
      ≤ ENNReal.ofReal (Real.sqrt X + Real.sqrt Y) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h3 (by norm_num)
    _ = ENNReal.ofReal ((Real.sqrt X + Real.sqrt Y) ^ (2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ ≤ ENNReal.ofReal ((101 / 100) * X + 101 * Y) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Real.rpow_two]
        nlinarith [sq_nonneg (Real.sqrt X / 10 - 10 * Real.sqrt Y), Real.sq_sqrt hX, Real.sq_sqrt hY]
end ReciprocityTheory.L2DbarEstimates.I
