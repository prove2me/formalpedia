-- Prove2me | solution 1 for avram_chat07a_tendsto_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:06:28.602718+00:00
-- url     : https://prove2.me/submissions/c041b07d-bf55-4076-92c1-e7dc55628e4f

import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_right_slope
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integral
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_integrable_signed_negative_jump_tail_DCT
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_original_residual_poly_error_normalized
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_endpoint_poly_levy_integrable
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_signed_payoff_BV_Levy_L1_error_transfer
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_poly_residual_primitive_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_original_C1_source_drift_expectation_right_slope
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
theorem solution
    {α : Type*} {l : Filter α} (F : α → ℝ) (b : ℝ)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ (g : α → ℝ) (c : ℝ),
        Tendsto g l (nhds c) ∧
        |c - b| ≤ ε ∧
        (∀ᶠ a in l, |F a - g a| ≤ ε)) :
    Tendsto F l (nhds b) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g, c, hg, hc, hfg⟩ := happrox (ε / 3) (by linarith)
  have hgc : ∀ᶠ a in l, dist (g a) c < ε / 3 :=
    Metric.tendsto_nhds.mp hg (ε / 3) (by linarith)
  filter_upwards [hfg, hgc] with a hfa hga
  rw [Real.dist_eq] at hga ⊢
  calc
    |F a - b| = |(F a - g a) + (g a - c) + (c - b)| := by ring
    _ ≤ |(F a - g a) + (g a - c)| + |c - b| := abs_add_le _ _
    _ ≤ (|F a - g a| + |g a - c|) + |c - b| := by
      have ht := abs_add_le (F a - g a) (g a - c)
      linarith
    _ < ε := by linarith
