-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat32_remainder_integrableOn_ball_levy
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-09T23:53:22.792645+00:00
-- url     : https://prove2.me/submissions/ba8fd716-9e39-4380-934d-90d889e6c594

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_norm_le_cube
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

private theorem sqBall_aux {ν : Measure ℝ} (hν : IsLevyMeasure ν) (r : ℝ) :
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

theorem solution {r : ℝ} (hr1 : r ≤ 1) (ξ : ℝ) {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < r} ν := by
  have hm : MeasurableSet {x : ℝ | |x| < r} := measurableSet_lt (by fun_prop) measurable_const
  have hsq := sqBall_aux hν r
  refine Integrable.mono' (hsq.const_mul (4 * ξ ^ 2)) (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' hm).2 (Filter.Eventually.of_forall ?_)
  intro x hx
  set u : ℝ := x * ξ with hu
  have hexp : ‖exp ((↑x : ℂ) * ↑ξ * I)‖ = 1 := by
    have : (↑x : ℂ) * ↑ξ * I = ((x * ξ : ℝ) : ℂ) * I := by push_cast; ring
    rw [this]; exact Complex.norm_exp_ofReal_mul_I _
  have hcast : (↑x : ℂ) * ↑ξ = ((u : ℝ) : ℂ) := by simp [hu]
  have hxξ2 : (4 * ξ ^ 2) * x ^ 2 = 4 * u ^ 2 := by simp [hu]; ring
  show ‖_‖ ≤ (4 * ξ ^ 2) * x ^ 2
  rw [hxξ2]
  by_cases hs : |u| ≤ 1
  · have := leanlevy_chat31_smallBall_remainder_norm_le_cube (ξ := ξ) (x := x) hs
    have hc : (2 / 9 : ℝ) * |ξ| ^ 3 * |x| ^ 3 = 2 / 9 * |u| ^ 3 := by
      rw [hu, abs_mul]; ring
    rw [hc] at this
    have : |u| ^ 3 ≤ u ^ 2 := by
      have : |u| ^ 3 = |u| * u ^ 2 := by rw [pow_succ, sq_abs]; ring
      rw [this]; nlinarith [sq_nonneg u, abs_nonneg u]
    nlinarith [sq_nonneg u, abs_nonneg u, ‹‖_‖ ≤ _›]
  · rw [not_le] at hs
    have h1 : 1 < u ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
    have hn : ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖
        ≤ 1 + 1 + |u| + u ^ 2 / 2 := by
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)) ?_
      · rw [hexp]; norm_num
      · rw [hcast, norm_mul, Complex.norm_real, Complex.norm_I]; simp
      · rw [hcast, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]; simp [sq_abs]
    nlinarith [sq_abs u, abs_nonneg u]
