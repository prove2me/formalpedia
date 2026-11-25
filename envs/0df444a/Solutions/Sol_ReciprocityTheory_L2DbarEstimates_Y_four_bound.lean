-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.four_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:39:24.645891+00:00
-- url     : https://prove2.me/submissions/2c482aa1-374f-47c4-84b8-8247ec8b92e6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourBasic
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fourBasic_cube_vol
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fourBasic_norm_exp

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
theorem _root_.solution (f : ℕ) : FOURBoundStatement f := by
  intro h b ν C hC
  have hint_r : ‖fourCoeff h b ν‖ ≤ C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) := by
    unfold fourCoeff
    have : IsFiniteMeasure
        (volume.restrict (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1))) :=
      ⟨by rw [Measure.restrict_apply_univ, fourBasic_cube_vol]; exact ENNReal.one_lt_top⟩
    have hle := norm_integral_le_of_norm_le_const
      (μ := volume.restrict (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1)))
      (f := fun x : Fin f → ℝ => h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) *
        Complex.exp (-2 * Real.pi * Complex.I *
          ∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)))
      (C := C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k))
      (ae_of_all _ fun x => by
        rw [norm_mul, fourBasic_norm_exp]
        exact mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le)
    simpa [Measure.real, Measure.restrict_apply_univ, fourBasic_cube_vol] using hle
  have h1 : Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) *
      Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k) = 1 := by
    rw [← Real.exp_add]
    rw [show 2 * Real.pi * ∑ k, (ν k : ℝ) * b k + -2 * Real.pi * ∑ k, (ν k : ℝ) * b k = 0 by ring]
    exact Real.exp_zero
  calc ‖fourCoeff h b ν‖ * Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k)
      ≤ C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) *
          Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k) :=
        mul_le_mul_of_nonneg_right hint_r (Real.exp_pos _).le
    _ = C := by rw [mul_assoc, h1, mul_one]
end ReciprocityTheory.L2DbarEstimates.Y
