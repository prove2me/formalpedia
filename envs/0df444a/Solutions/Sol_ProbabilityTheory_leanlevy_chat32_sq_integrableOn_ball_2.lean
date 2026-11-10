-- Prove2me | solution 2 for ProbabilityTheory.leanlevy_chat32_sq_integrableOn_ball
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:52:54.081125+00:00
-- url     : https://prove2.me/submissions/41de4b8e-8344-4ab5-8d33-e02f5d31bc92

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (r : ℝ) (m : Measure ℝ) [IsFiniteMeasure m] :
    IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < r} m := by
  have hmeas : MeasurableSet {x : ℝ | |x| < r} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  have hg_int : IntegrableOn (fun x : ℝ => min (x ^ 2) (r ^ 2)) {x : ℝ | |x| < r} m := by
    refine (Integrable.mono' (integrable_const (r ^ 2))
      ((continuous_pow 2).min continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))).integrableOn
    rw [Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · have : (0 : ℝ) ≤ min (x ^ 2) (r ^ 2) := le_min (sq_nonneg x) (sq_nonneg r)
      linarith [sq_nonneg r]
    · exact min_le_right _ _
  refine hg_int.congr_fun (fun x hx => ?_) hmeas
  have hx' : |x| < r := hx
  have : x ^ 2 ≤ r ^ 2 := by rw [← sq_abs x]; gcongr
  exact min_eq_left this
