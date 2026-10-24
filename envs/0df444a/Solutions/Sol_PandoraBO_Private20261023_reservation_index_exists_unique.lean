-- Prove2me | solution 1 for PandoraBO.Private20261023.reservation_index_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @QianJaneXie
-- created : 2026-10-23T23:46:17.953853+00:00
-- url     : https://prove2.me/submissions/a51ff001-816e-40a6-8736-66b29cc96c80

import Definitions.Def_PandoraBO_Model
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
# Basic analytic properties of the expected-improvement function

These lemmas use only the model definitions, with no import of the mission's
unproved theorem declarations. They are the analytic starting point for proving
that a positive inspection cost has a unique reservation index.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace PandoraBO

/-- The payoff used to define expected improvement is integrable. -/
theorem improvement_payoff_integrable {n : ℕ} (M : Instance n)
    (i : Box n) (z : ℝ) :
    Integrable (fun y : ℝ => max (y - z) 0) (M.law i) := by
  letI : IsProbabilityMeasure (M.law i) := M.law_probability i
  exact ((M.reward_integrable i).sub (integrable_const z)).pos_part

/-- Expected improvement is nonnegative, including at unattainable thresholds. -/
theorem expectedImprovement_nonneg {n : ℕ} (M : Instance n)
    (i : Box n) (z : ℝ) :
    0 ≤ expectedImprovement M i z := by
  exact integral_nonneg (fun y => le_max_right (y - z) 0)

/-- Raising the comparison value can only decrease expected improvement. -/
theorem expectedImprovement_antitone {n : ℕ} (M : Instance n)
    (i : Box n) : Antitone (expectedImprovement M i) := by
  intro z w hzw
  exact integral_mono (improvement_payoff_integrable M i w)
    (improvement_payoff_integrable M i z)
    (fun y => max_le_max (sub_le_sub_left hzw y) le_rfl)

/-- The positive-part payoff changes by at most the change in threshold. -/
theorem improvement_payoff_abs_sub_le (y z w : ℝ) :
    |max (y - z) 0 - max (y - w) 0| ≤ |z - w| := by
  simpa only [sub_sub_sub_cancel_left, abs_sub_comm]
    using abs_max_sub_max_le_abs (y - z) (y - w) 0

/-- Expected improvement changes by at most the change in threshold. -/
theorem expectedImprovement_abs_sub_le {n : ℕ} (M : Instance n)
    (i : Box n) (z w : ℝ) :
    |expectedImprovement M i z - expectedImprovement M i w| ≤ |z - w| := by
  letI : IsProbabilityMeasure (M.law i) := M.law_probability i
  unfold expectedImprovement
  rw [← integral_sub (improvement_payoff_integrable M i z)
    (improvement_payoff_integrable M i w)]
  have hbound : ∀ᵐ y ∂M.law i,
      ‖max (y - z) 0 - max (y - w) 0‖ ≤ |z - w| :=
    ae_of_all _ (fun y => by
      simpa only [Real.norm_eq_abs] using improvement_payoff_abs_sub_le y z w)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one]
    using norm_integral_le_of_norm_le_const hbound

/-- The expected-improvement function is globally 1-Lipschitz. -/
theorem expectedImprovement_lipschitz {n : ℕ} (M : Instance n)
    (i : Box n) : LipschitzWith 1 (expectedImprovement M i) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul]
    using expectedImprovement_abs_sub_le M i z w

/-- In particular, expected improvement is continuous in the threshold. -/
theorem expectedImprovement_continuous {n : ℕ} (M : Instance n)
    (i : Box n) : Continuous (expectedImprovement M i) :=
  (expectedImprovement_lipschitz M i).continuous

/-- The elementary lower bound that makes expected improvement unbounded as
the threshold tends to negative infinity. -/
theorem mean_sub_le_expectedImprovement {n : ℕ} (M : Instance n)
    (i : Box n) (z : ℝ) :
    (∫ y : ℝ, y ∂M.law i) - z ≤ expectedImprovement M i z := by
  letI : IsProbabilityMeasure (M.law i) := M.law_probability i
  have h := integral_mono ((M.reward_integrable i).sub (integrable_const z))
    (improvement_payoff_integrable M i z)
    (fun y => le_max_left (y - z) 0)
  change (∫ y : ℝ, y - z ∂M.law i) ≤ expectedImprovement M i z at h
  rw [integral_sub (M.reward_integrable i) (integrable_const z)] at h
  simpa only [integral_const, probReal_univ, one_smul] using h

end PandoraBO

/-!
# Existence and uniqueness of a positive-cost reservation index

The proof uses dominated convergence at positive thresholds, a linear lower
bound at negative thresholds, and strict decrease whenever expected improvement
is positive. No mission theorem with an unproved body is imported.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter

namespace PandoraBO

/-- At two distinct thresholds, equal positive-part payoffs must both vanish. -/
theorem improvement_payoff_eq_zero_of_eq_of_lt (y : ℝ) {z w : ℝ}
    (hzw : z < w) (heq : max (y - z) 0 = max (y - w) 0) :
    max (y - z) 0 = 0 := by
  by_cases hyw : y ≤ w
  · simpa only [max_eq_right (sub_nonpos.mpr hyw)] using heq
  · have hwy : w < y := lt_of_not_ge hyw
    have hw : 0 ≤ y - w := (sub_pos.mpr hwy).le
    have hz : 0 ≤ y - z := (sub_pos.mpr (lt_trans hzw hwy)).le
    rw [max_eq_left hz, max_eq_left hw] at heq
    exact False.elim ((ne_of_lt (sub_lt_sub_left hzw y)) heq.symm)

/-- Equality at distinct ordered thresholds can only occur at level zero. -/
theorem expectedImprovement_eq_zero_of_eq_of_lt {n : ℕ} (M : Instance n)
    (i : Box n) {z w : ℝ} (hzw : z < w)
    (heq : expectedImprovement M i z = expectedImprovement M i w) :
    expectedImprovement M i z = 0 := by
  have hle : (fun y : ℝ => max (y - w) 0) ≤ᵐ[M.law i]
      (fun y : ℝ => max (y - z) 0) :=
    ae_of_all _ (fun y => max_le_max (sub_le_sub_left hzw.le y) le_rfl)
  have heqae : (fun y : ℝ => max (y - w) 0) =ᵐ[M.law i]
      (fun y : ℝ => max (y - z) 0) :=
    (integral_eq_iff_of_ae_le (improvement_payoff_integrable M i w)
      (improvement_payoff_integrable M i z) hle).mp heq.symm
  apply integral_eq_zero_of_ae
  filter_upwards [heqae] with y hy
  exact improvement_payoff_eq_zero_of_eq_of_lt y hzw hy.symm

/-- Expected improvement strictly decreases when its value at the lower
threshold is positive. -/
theorem expectedImprovement_lt_of_lt_of_pos {n : ℕ} (M : Instance n)
    (i : Box n) {z w : ℝ} (hzw : z < w)
    (hz : 0 < expectedImprovement M i z) :
    expectedImprovement M i w < expectedImprovement M i z := by
  apply lt_of_le_of_ne (expectedImprovement_antitone M i hzw.le)
  intro heq
  exact (ne_of_gt hz)
    (expectedImprovement_eq_zero_of_eq_of_lt M i hzw heq.symm)

/-- Natural-number thresholds suffice to make expected improvement tend to
zero; domination is by the integrable positive part of the reward. -/
theorem expectedImprovement_nat_tendsto_zero {n : ℕ} (M : Instance n)
    (i : Box n) :
    Tendsto (fun k : ℕ => expectedImprovement M i (k : ℝ)) atTop (nhds 0) := by
  have hpoint : ∀ y : ℝ,
      Tendsto (fun k : ℕ => max (y - (k : ℝ)) 0) atTop (nhds 0) := by
    intro y
    obtain ⟨k, hk⟩ := exists_nat_gt y
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with l hl
    have hy : y ≤ (l : ℝ) := le_trans hk.le (Nat.cast_le.mpr hl)
    simp only [max_eq_right (sub_nonpos.mpr hy)]
  have hdom := tendsto_integral_of_dominated_convergence
    (μ := M.law i) (F := fun k : ℕ => fun y : ℝ => max (y - (k : ℝ)) 0)
    (f := fun _ : ℝ => (0 : ℝ)) (fun y : ℝ => max y 0)
    (fun k => (improvement_payoff_integrable M i (k : ℝ)).aestronglyMeasurable)
    (by simpa only [sub_zero] using improvement_payoff_integrable M i 0)
    (fun k => ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right (y - (k : ℝ)) 0)]
      exact max_le_max (sub_le_self y (Nat.cast_nonneg k)) le_rfl))
    (ae_of_all _ hpoint)
  simpa only [expectedImprovement, integral_zero] using hdom

/-- Every strictly positive cost is attained at a unique finite threshold. -/
theorem reservationRoot_exists_unique_positive_cost {n : ℕ} (M : Instance n)
    (i : Box n) (c : ℝ) (hc : 0 < c) :
    ∃! z : ℝ, reservationRoot M i c z := by
  have hsmall : ∀ᶠ k : ℕ in atTop, expectedImprovement M i (k : ℝ) < c :=
    (expectedImprovement_nat_tendsto_zero M i).eventually (isOpen_Iio.mem_nhds hc)
  obtain ⟨k, hk⟩ := hsmall.exists
  have hlarge : c ≤ expectedImprovement M i ((∫ y : ℝ, y ∂M.law i) - c) := by
    simpa only [sub_sub_cancel] using
      mean_sub_le_expectedImprovement M i ((∫ y : ℝ, y ∂M.law i) - c)
  obtain ⟨z, hz⟩ := mem_range_of_exists_le_of_exists_ge
    (expectedImprovement_continuous M i) ⟨(k : ℝ), hk.le⟩
    ⟨(∫ y : ℝ, y ∂M.law i) - c, hlarge⟩
  refine ⟨z, hz, ?_⟩
  intro w hw
  change expectedImprovement M i w = c at hw
  rcases lt_trichotomy w z with hwz | heq | hzw
  · exact False.elim ((ne_of_gt hc) (hw.symm.trans
      (expectedImprovement_eq_zero_of_eq_of_lt M i hwz (hw.trans hz.symm))))
  · exact heq
  · exact False.elim ((ne_of_gt hc) (hz.symm.trans
      (expectedImprovement_eq_zero_of_eq_of_lt M i hzw (hz.trans hw.symm))))

end PandoraBO

/-- The original reservation-index milestone, without any additional assumption. -/
theorem solution {n : ℕ} (M : PandoraBO.Instance n)
    (multiplier : ℝ) (hpos : 0 < multiplier) (i : PandoraBO.Box n) :
    ∃! z : ℝ, PandoraBO.reservationRoot M i (multiplier * M.cost i) z := by
  exact PandoraBO.reservationRoot_exists_unique_positive_cost M i (multiplier * M.cost i)
    (mul_pos hpos (M.cost_positive i))
