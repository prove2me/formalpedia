-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fourBasic_norm_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:35.810347+00:00
-- url     : https://prove2.me/submissions/67eb38d0-d91c-418c-bbf2-e44f05469513

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {f : ℕ} (ν : Fin f → ℤ) (x b : Fin f → ℝ) :
    ‖Complex.exp (-2 * Real.pi * Complex.I *
        ∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I))‖ =
      Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) := by
  have hsplit : (∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)) =
      ((∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) + ((∑ k, (ν k : ℝ) * b k : ℝ) : ℂ) * Complex.I := by
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have harg : -2 * Real.pi * Complex.I *
        (∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)) =
      ((2 * Real.pi * ∑ k, (ν k : ℝ) * b k : ℝ) : ℂ) +
        ((-2 * Real.pi * ∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) * Complex.I := by
    rw [hsplit]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * ∑ k, (ν k : ℂ) * (b k : ℂ)) * Complex.I_sq
  rw [harg, Complex.norm_exp]
  congr 1
  simp
end ReciprocityTheory.L2DbarEstimates.Y
