-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat32_remainder_integrableOn_ball
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:56:35.654202+00:00
-- url     : https://prove2.me/submissions/66c62f86-6b90-45a5-b873-664e589cd906

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_clamp_continuous
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_clamp_eq_of_abs_lt
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_clamp_norm_le
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ξ : ℝ) (m : Measure ℝ) [IsFiniteMeasure m] :
    IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < r} m := by
  have hmeas : MeasurableSet {x : ℝ | |x| < r} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  have hclamp_int : IntegrableOn
      (fun x : ℝ =>
        (fun y : ℝ =>
          exp ((↑y : ℂ) * ↑ξ * I) - 1 - (↑y : ℂ) * ↑ξ * I + ((↑y : ℂ) * ↑ξ) ^ 2 / 2)
          (max (-r) (min x r)))
      {x : ℝ | |x| < r} m :=
    (Integrable.mono' (integrable_const (2 + |ξ| + ξ ^ 2 / 2))
      (ProbabilityTheory.leanlevy_chat32_remainder_clamp_continuous r ξ).aestronglyMeasurable
      (Filter.Eventually.of_forall
        (ProbabilityTheory.leanlevy_chat32_remainder_clamp_norm_le hr0 hr1 ξ))).integrableOn
  refine hclamp_int.congr_fun (fun x hx => ?_) hmeas
  show (fun y : ℝ =>
      exp ((↑y : ℂ) * ↑ξ * I) - 1 - (↑y : ℂ) * ↑ξ * I + ((↑y : ℂ) * ↑ξ) ^ 2 / 2)
      (max (-r) (min x r)) = _
  rw [ProbabilityTheory.leanlevy_chat32_clamp_eq_of_abs_lt hx]
