-- Prove2me | solution 1 for ServiceParts.Shortfall.adjustment_coefficient_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:20:15.678365+00:00
-- url     : https://prove2.me/submissions/6faf3e58-8be8-4bc7-92a7-8162cfce0c56

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_ShortfallModel

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace D3cfd26dAux

/-- Pointwise strict convexity bound: for `0 < a < b`, `t = a / b`, and `y ≠ 0`,
`exp (-a*y) < (1 - t) + t * exp (-b*y)`. -/
lemma exp_strict (a b y : ℝ) (ha : 0 < a) (hab : a < b) (hy : y ≠ 0) :
    Real.exp (-a * y) < (1 - a / b) + (a / b) * Real.exp (-b * y) := by
  have hb : 0 < b := lt_trans ha hab
  have ht0 : 0 < a / b := div_pos ha hb
  have ht1 : a / b < 1 := (div_lt_one hb).2 hab
  have hne : (0 : ℝ) ≠ -b * y := by
    intro h
    have : -b * y = 0 := h.symm
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact hy h'
  have := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-b * y)) hne
    (sub_pos.2 ht1) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at this
  have heq : a / b * (-b * y) = -a * y := by field_simp
  rw [heq] at this
  exact this

lemma exp_le (a b y : ℝ) (ha : 0 < a) (hab : a < b) :
    Real.exp (-a * y) ≤ (1 - a / b) + (a / b) * Real.exp (-b * y) := by
  by_cases hy : y = 0
  · subst hy; simp
  · exact (exp_strict a b y ha hab hy).le

lemma ae_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (ea : ∫ ω, Real.exp (-a * Y ω) ∂P = 1) (eb : ∫ ω, Real.exp (-b * Y ω) ∂P = 1) :
    ∀ᵐ ω ∂P, Y ω = 0 := by
  have ia : Integrable (fun ω => Real.exp (-a * Y ω)) P :=
    Integrable.of_integral_ne_zero (by rw [ea]; norm_num)
  have ib : Integrable (fun ω => Real.exp (-b * Y ω)) P :=
    Integrable.of_integral_ne_zero (by rw [eb]; norm_num)
  set g : Ω → ℝ := fun ω =>
    (1 - a / b) + (a / b) * Real.exp (-b * Y ω) - Real.exp (-a * Y ω) with hg
  have gnn : 0 ≤ g := fun ω => by
    simp only [hg, Pi.zero_apply]
    linarith [exp_le a b (Y ω) ha hab]
  have gi : Integrable g P :=
    ((integrable_const (1 - a / b)).add (ib.const_mul (a / b))).sub ia
  have gint : ∫ ω, g ω ∂P = 0 := by
    simp only [hg]
    have i1 : Integrable (fun ω => (1 - a / b) + (a / b) * Real.exp (-b * Y ω)) P :=
      (integrable_const (1 - a / b)).add (ib.const_mul (a / b))
    rw [integral_sub i1 ia, integral_add (integrable_const _) (ib.const_mul _),
      integral_const_mul, eb, ea, integral_const]
    simp
  have hz := (integral_eq_zero_iff_of_nonneg gnn gi).1 gint
  filter_upwards [hz] with ω hω
  by_contra hy
  have := exp_strict a b (Y ω) ha hab hy
  simp only [hg, Pi.zero_apply] at hω
  linarith

end D3cfd26dAux

open MeasureTheory ProbabilityTheory ServiceParts.Shortfall in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) (α₁ α₂ : ℝ) (h₁ : 0 < α₁) (h₂ : 0 < α₂)
    (e₁ : ∫ ω, Real.exp (-α₁ * (M.capacity - M.demand 1 ω)) ∂P = 1)
    (e₂ : ∫ ω, Real.exp (-α₂ * (M.capacity - M.demand 1 ω)) ∂P = 1) :
    α₁ = α₂ := by
  have key : ∀ a b : ℝ, 0 < a → a < b →
      ∫ ω, Real.exp (-a * (M.capacity - M.demand 1 ω)) ∂P = 1 →
      ∫ ω, Real.exp (-b * (M.capacity - M.demand 1 ω)) ∂P = 1 → False := by
    intro a b ha hab ea eb
    have hz := D3cfd26dAux.ae_zero (P := P) (fun ω => M.capacity - M.demand 1 ω) a b ha hab ea eb
    have hD : (fun ω => M.demand 1 ω) =ᵐ[P] fun _ => M.capacity := by
      filter_upwards [hz] with ω hω
      linarith
    have hint : ∫ ω, M.demand 1 ω ∂P = M.capacity := by
      rw [integral_congr_ae hD]
      simp
    have := M.mean_lt_capacity
    linarith
  rcases lt_trichotomy α₁ α₂ with h | h | h
  · exact (key α₁ α₂ h₁ h e₁ e₂).elim
  · exact h
  · exact (key α₂ α₁ h₂ h e₂ e₁).elim
