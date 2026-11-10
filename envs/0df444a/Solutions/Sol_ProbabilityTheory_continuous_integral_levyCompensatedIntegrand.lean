-- Prove2me | solution 1 for ProbabilityTheory.continuous_integral_levyCompensatedIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:31:53.779627+00:00
-- url     : https://prove2.me/submissions/c601b78c-a090-437b-af6c-dc71790e8853

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26_norm_compensated_minimal
import Theorems.Thm_ProbabilityTheory_measurable_levyCompensatedIntegrand
import Theorems.Thm_ProbabilityTheory_continuous_levyCompensatedIntegrand_fst
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_integrable_min_one_sq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    Continuous (fun ξ => ∫ x, levyCompensatedIntegrand ξ x ∂ν) := by
  rw [continuous_iff_continuousAt]
  intro ξ₀
  refine continuousAt_of_dominated
    (bound := fun x => (2 + 3 * (|ξ₀| + 1) ^ 2) * min 1 (x ^ 2))
    (Eventually.of_forall fun ξ =>
      (measurable_levyCompensatedIntegrand ξ).aestronglyMeasurable)
    ?_ (hν.integrable_min_one_sq.const_mul _)
    (Eventually.of_forall fun x =>
      (continuous_levyCompensatedIntegrand_fst x).continuousAt)
  have hev : ∀ᶠ ξ in 𝓝 ξ₀, |ξ| < |ξ₀| + 1 :=
    continuous_abs.continuousAt.eventually_lt continuousAt_const (by linarith)
  filter_upwards [hev] with ξ hξ
  filter_upwards with x
  have hξ2 : ξ ^ 2 ≤ (|ξ₀| + 1) ^ 2 := by
    nlinarith [sq_abs ξ, hξ.le, abs_nonneg ξ, abs_nonneg ξ₀]
  have hmin : (0 : ℝ) ≤ min 1 (x ^ 2) :=
    le_min zero_le_one (sq_nonneg x)
  calc
    ‖levyCompensatedIntegrand ξ x‖
        ≤ (2 + 3 * ξ ^ 2) * min 1 (x ^ 2) :=
          leanlevy_chat26_norm_compensated_minimal ξ x
    _ ≤ (2 + 3 * (|ξ₀| + 1) ^ 2) * min 1 (x ^ 2) := by
      nlinarith [hξ2, hmin]
