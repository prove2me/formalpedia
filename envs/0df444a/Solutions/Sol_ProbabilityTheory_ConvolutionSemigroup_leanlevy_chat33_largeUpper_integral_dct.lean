-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeUpper_integral_dct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:20:00.734492+00:00
-- url     : https://prove2.me/submissions/a807c483-488a-4e31-9267-f6579240d3ae

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Dominated convergence for the original bounded continuous upper ramps,
using only the pinned definitions and Mathlib integral convergence. -/
theorem solution (ρ : ℝ) (hρ : 0 < ρ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (M : ℝ)
    (hg_bnd : ∀ x, |g x| ≤ M)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∃ f : ℕ → BoundedContinuousFunction ℝ ℝ,
      (∀ n x, f n x = min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * g x) ∧
      Tendsto (fun n => ∫ x, f n x ∂ν) atTop
        (𝓝 (∫ x in largeSet ρ, g x ∂ν)) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg (g 0)) (hg_bnd 0)
  have hramp : ∀ n : ℕ, ∀ x : ℝ,
      0 ≤ min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) ∧
      min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) ≤ 1 := by
    intro n x
    exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hterm_bnd : ∀ n : ℕ, ∀ x : ℝ,
      |min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * g x| ≤ M := by
    intro n x
    rw [abs_mul, abs_of_nonneg (hramp n x).1]
    calc
      min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * |g x|
          ≤ 1 * |g x| :=
        mul_le_mul_of_nonneg_right (hramp n x).2 (abs_nonneg _)
      _ ≤ 1 * M := mul_le_mul_of_nonneg_left (hg_bnd x) zero_le_one
      _ = M := one_mul _
  let φ : ℕ → BoundedContinuousFunction ℝ ℝ := fun n =>
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * g x,
        (Continuous.min continuous_const
          (Continuous.max continuous_const
            (((continuous_abs.sub continuous_const).mul continuous_const).add continuous_const))).mul hg_cont⟩
      (2 * M)
      (fun x y => by
        rw [Real.dist_eq]
        simp only [ContinuousMap.coe_mk]
        have hx := hterm_bnd n x
        have hy := hterm_bnd n y
        rw [abs_le] at hx hy
        refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;> linarith)
  have hφ : ∀ n x, φ n x =
      min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * g x := by
    intro n x
    rfl
  have hzero : ∀ m : ℕ, 1 ≤ m → ∀ x : ℝ, |x| < ρ / 2 →
      min 1 (max 0 ((|x| - ρ) * ((m + 1 : ℝ) / ρ) + 1)) = 0 := by
    intro m hm x hx
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hdiff : 0 ≤ ρ - |x| := by linarith
    have hm2 : (2 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hmul : (ρ - |x|) * 2 ≤ (ρ - |x|) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hm2 hdiff
    have hδ : ρ ≤ (ρ - |x|) * 2 := by linarith
    have hnum : (|x| - ρ) * ((m : ℝ) + 1) ≤ -ρ := by
      nlinarith [hmul, hδ]
    have hdiv : (|x| - ρ) * (((m : ℝ) + 1) / ρ) ≤ -1 := by
      calc
        (|x| - ρ) * (((m : ℝ) + 1) / ρ) =
            ((|x| - ρ) * ((m : ℝ) + 1)) / ρ := by ring
        _ ≤ -1 := (div_le_iff₀ hρ).2 (by nlinarith [hnum])
    have hnonpos : (|x| - ρ) * ((m + 1 : ℝ) / ρ) + 1 ≤ 0 := by
      convert add_le_add_right hdiv 1 using 1 <;> push_cast <;> ring
    rw [max_eq_left hnonpos]
    norm_num
  have hφ_support : ∀ n x, |x| < ρ / 2 → φ (n + 1) x = 0 := by
    intro n x hx
    rw [hφ (n + 1) x, hzero (n + 1) (by omega) x hx, zero_mul]
  have hφ_limit : ∀ x, Tendsto (fun n => φ n x) atTop
      (𝓝 (Set.indicator (largeSet ρ) g x)) := by
    intro x
    by_cases hx : ρ ≤ |x|
    · rw [Set.indicator_of_mem (show x ∈ largeSet ρ from hx)]
      refine tendsto_atTop_of_eventually_const (i₀ := 0) (fun n _ => ?_)
      rw [hφ n x]
      have hcoef : 0 ≤ (n + 1 : ℝ) / ρ := by positivity
      have habove : (1 : ℝ) ≤ (|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hx) hcoef]
      rw [min_eq_left (le_trans habove (le_max_right _ _)), one_mul]
    · have hxlt : |x| < ρ := lt_of_not_ge hx
      rw [Set.indicator_of_notMem (show x ∉ largeSet ρ from not_le.mpr hxlt)]
      have hpos : 0 < ρ - |x| := by linarith
      obtain ⟨N, hN⟩ := exists_nat_gt (ρ / (ρ - |x|))
      rw [div_lt_iff₀ hpos] at hN
      refine tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => ?_)
      rw [hφ n x]
      have hn_le : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hnum : ρ ≤ (ρ - |x|) * (n + 1 : ℝ) := by
        calc
          ρ ≤ (N : ℝ) * (ρ - |x|) := le_of_lt hN
          _ ≤ (n : ℝ) * (ρ - |x|) := mul_le_mul_of_nonneg_right hn_le hpos.le
          _ ≤ (n + 1 : ℝ) * (ρ - |x|) :=
            mul_le_mul_of_nonneg_right (by linarith) hpos.le
          _ = (ρ - |x|) * (n + 1 : ℝ) := by ring
      have hscaled : (|x| - ρ) * ((n + 1 : ℝ) / ρ) ≤ -1 := by
        calc
          _ = ((|x| - ρ) * (n + 1 : ℝ)) / ρ := by ring
          _ ≤ -1 := (div_le_iff₀ hρ).2 (by nlinarith [hnum])
      have hnonpos : (|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1 ≤ 0 := by linarith
      rw [max_eq_left hnonpos]
      norm_num
  have hrhalf : 0 < ρ / 2 := by positivity
  have hmeas : MeasurableSet (largeSet (ρ / 2)) :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  haveI : IsFiniteMeasure (ν.restrict (largeSet (ρ / 2))) :=
    isFiniteMeasure_restrict.mpr (hν.measure_setOf_abs_ge_lt_top hrhalf).ne
  have hbound : Integrable (Set.indicator (largeSet (ρ / 2)) (fun _ => M)) ν :=
    (integrable_indicator_iff hmeas).mpr (integrable_const M)
  have hshift : Tendsto (fun n => ∫ x, φ (n + 1) x ∂ν) atTop
      (𝓝 (∫ x, Set.indicator (largeSet ρ) g x ∂ν)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := Set.indicator (largeSet (ρ / 2)) (fun _ => M))
      (fun n => (φ (n + 1)).continuous.aestronglyMeasurable)
      hbound
      (fun n => Filter.Eventually.of_forall (fun x => ?_))
      (Filter.Eventually.of_forall (fun x =>
        (tendsto_add_atTop_iff_nat 1).mpr (hφ_limit x)))
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ largeSet (ρ / 2)
    · rw [Set.indicator_of_mem hx, hφ (n + 1) x]
      exact hterm_bnd (n + 1) x
    · rw [Set.indicator_of_notMem hx]
      have hxsmall : |x| < ρ / 2 := by
        change ¬ ρ / 2 ≤ |x| at hx
        exact lt_of_not_ge hx
      rw [hφ_support n x hxsmall, abs_zero]
  have h_dct :=
    (tendsto_add_atTop_iff_nat (f := fun n => ∫ x, φ n x ∂ν) 1).mp hshift
  have hmeasρ : MeasurableSet (largeSet ρ) :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  rw [integral_indicator hmeasρ] at h_dct
  exact ⟨φ, hφ, h_dct⟩
