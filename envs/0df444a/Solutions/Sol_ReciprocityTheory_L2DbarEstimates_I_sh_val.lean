-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.sh_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:32.392077+00:00
-- url     : https://prove2.me/submissions/0a9ae91f-aad2-4f19-850e-bcf5b4398524

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n j : ℕ) (S r a b : ℝ) (hS : 0 < S) (hr : 0 < r) :
    Real.exp (-b - ((n : ℝ) + j) * a) * (S * Real.exp (-a) / r ^ 2) ^ (-(n : ℝ)) =
      r ^ (2 * n) * Real.exp (-b - (j : ℝ) * a) * S ^ (-(n : ℝ)) := by
  have hX : 0 < Real.exp (-a) / r ^ 2 := by positivity
  rw [mul_div_assoc, Real.mul_rpow hS.le hX.le, Real.rpow_neg hX.le, Real.rpow_natCast,
    div_pow, ← Real.exp_nat_mul, pow_mul]
  have hE : Real.exp (-b - ((n : ℝ) + j) * a) =
      Real.exp (-b - (j : ℝ) * a) * Real.exp (↑n * -a) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hE]
  have h1 : 0 < Real.exp (↑n * -a) := Real.exp_pos _
  have h2 : 0 < (r ^ 2) ^ n := by positivity
  field_simp
end ReciprocityTheory.L2DbarEstimates.I
