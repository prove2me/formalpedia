-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat32_sq_integrableOn_ball_levy
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-09T23:51:49.944579+00:00
-- url     : https://prove2.me/submissions/fdf421e0-c4dc-4b6e-af32-eb1815f04a1e

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) (r : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < r} ν := by
  have hmeas : Measurable (fun x : ℝ => min 1 (x ^ 2)) := measurable_const.min (by fun_prop)
  have hint : Integrable (fun x : ℝ => min 1 (x ^ 2)) ν := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => le_min zero_le_one (sq_nonneg x))]
    exact hν.2
  have h1 : IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < 1} ν := by
    refine (hint.integrableOn).congr_fun ?_ (measurableSet_lt (by fun_prop) measurable_const)
    intro x hx
    have hx' : |x| < 1 := hx
    have : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
    exact min_eq_right this
  have h2 : IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < r ∧ 1 ≤ |x|} ν := by
    have hfin : ν {x : ℝ | 1 ≤ |x|} < ⊤ := hν.measure_setOf_abs_ge_lt_top one_pos
    have hma : MeasurableSet {x : ℝ | |x| < r} := measurableSet_lt (by fun_prop) measurable_const
    have hmb : MeasurableSet {x : ℝ | 1 ≤ |x|} := measurableSet_le measurable_const (by fun_prop)
    have hm : MeasurableSet {x : ℝ | |x| < r ∧ 1 ≤ |x|} := hma.inter hmb
    refine Measure.integrableOn_of_bounded (M := r ^ 2) ?_ (by fun_prop) ?_
    · exact (measure_mono (fun x hx => hx.2)).trans_lt hfin |>.ne
    · refine (ae_restrict_iff' hm).2 (Filter.Eventually.of_forall ?_)
      intro x hx
      rw [Real.norm_eq_abs, abs_pow, sq_abs]
      calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
        _ ≤ r ^ 2 := (pow_lt_pow_left₀ hx.1 (abs_nonneg x) two_ne_zero).le
  refine (h1.union h2).mono_set ?_
  intro x hx
  by_cases h : |x| < 1
  · exact Or.inl h
  · exact Or.inr ⟨hx, not_lt.1 h⟩
