-- Prove2me | solution 1 for ProbabilityTheory.tendsto_setIntegral_annulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:51:38.847875+00:00
-- url     : https://prove2.me/submissions/c12faccd-f466-4fe7-b12d-7dd4bcd163aa

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Theorems.Thm_ProbabilityTheory_norm_levyCompensatedIntegrand_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}
theorem solution (hν : IsLevyMeasure ν) (ξ : ℝ) :
    Tendsto (fun n : ℕ => ∫ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|},
        (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν) atTop
      (𝓝 (∫ x in Set.Ioo (-1:ℝ) 1,
        (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν)) := by
  have hA_meas : ∀ n : ℕ,
      MeasurableSet (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|}) :=
    fun n => measurableSet_Ioo.inter (measurableSet_le measurable_const continuous_abs.measurable)
  have hgmeas : Measurable fun x : ℝ =>
      Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I := by
    have h1 : Measurable fun x : ℝ => (↑x * ↑ξ * Complex.I : ℂ) :=
      ((Complex.measurable_ofReal.mul measurable_const).mul measurable_const)
    exact ((Complex.measurable_exp.comp h1).sub measurable_const).sub h1
  have hg_eq : ∀ x ∈ Set.Ioo (-1:ℝ) 1,
      Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I = levyCompensatedIntegrand ξ x := by
    intro x hx
    have hlt : |x| < 1 := abs_lt.mpr hx
    simp [levyCompensatedIntegrand, hlt]
  have hbound_int : Integrable (fun x : ℝ => (2 + 3 * ξ ^ 2) * min 1 (x ^ 2)) ν := by
    refine ⟨((measurable_const.min (measurable_id'.pow_const 2)).const_mul _).aestronglyMeasurable,
      ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hC : (0:ℝ) ≤ 2 + 3 * ξ ^ 2 := by positivity
    have henorm : ∀ x : ℝ, ‖(2 + 3 * ξ ^ 2) * min 1 (x ^ 2)‖ₑ
        = ENNReal.ofReal (2 + 3 * ξ ^ 2) * ENNReal.ofReal (min 1 (x ^ 2)) := fun x => by
      rw [Real.enorm_eq_ofReal (mul_nonneg hC (le_min zero_le_one (sq_nonneg x))),
        ENNReal.ofReal_mul hC]
    simp_rw [henorm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν.2
  have hlim : ∀ x : ℝ, Tendsto (fun n : ℕ =>
      (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
        (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x) atTop
      (𝓝 ((Set.Ioo (-1:ℝ) 1).indicator
        (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x)) := by
    intro x
    by_cases hxo : x ∈ Set.Ioo (-1:ℝ) 1
    · rw [Set.indicator_of_mem hxo]
      by_cases hx0 : x = 0
      · have hz : (fun n : ℕ => (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
            (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x)
            = fun _ => Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I := by
          funext n; rw [hx0]; simp [Set.indicator_apply]
        rw [hz]; exact tendsto_const_nhds
      · have habs : (0:ℝ) < |x| := abs_pos.mpr hx0
        obtain ⟨N, hN⟩ := exists_nat_gt (|x|⁻¹)
        have hev : ∀ᶠ (n : ℕ) in atTop, (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
            (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x
            = Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I := by
          rw [Filter.eventually_atTop]
          refine ⟨N, fun n hn => ?_⟩
          have hxinv : |x|⁻¹ < (n:ℝ) + 1 := by
            have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
            linarith [hN]
          have h1 : (1:ℝ) < |x| * ((n:ℝ) + 1) := by
            have h2 := mul_lt_mul_of_pos_left hxinv habs
            rwa [mul_inv_cancel₀ (ne_of_gt habs)] at h2
          have hmem : x ∈ Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|} := by
            refine ⟨hxo, ?_⟩
            show ((n:ℝ) + 1)⁻¹ ≤ |x|
            rw [inv_eq_one_div, div_le_iff₀ (Nat.cast_add_one_pos n)]; linarith [h1]
          exact Set.indicator_of_mem hmem _
        exact (tendsto_congr' hev).mpr tendsto_const_nhds
    · rw [Set.indicator_of_notMem hxo]
      have hz : (fun n : ℕ => (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
          (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x)
          = fun _ => 0 := by
        funext n; exact Set.indicator_of_notMem (fun hmem => hxo hmem.1) _
      rw [hz]; exact tendsto_const_nhds
  have hdct := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun n x => (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
      (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x)
    (f := (Set.Ioo (-1:ℝ) 1).indicator
      fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I)
    (bound := fun x => (2 + 3 * ξ ^ 2) * min 1 (x ^ 2))
    (fun n => (hgmeas.indicator (hA_meas n)).aestronglyMeasurable) hbound_int
    (fun n => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall hlim)
  · rw [integral_indicator measurableSet_Ioo] at hdct
    have hrw : (fun n : ℕ => ∫ x,
          (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
            (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x ∂ν)
        = fun n : ℕ => ∫ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|},
            (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν := by
      funext n; rw [integral_indicator (hA_meas n)]
    rw [hrw] at hdct
    exact hdct
  · -- pointwise bound
    by_cases hxa : x ∈ Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}
    · rw [Set.indicator_of_mem hxa, hg_eq x hxa.1]
      exact norm_levyCompensatedIntegrand_le ξ x
    · rw [Set.indicator_of_notMem hxa, norm_zero]
      exact mul_nonneg (by positivity) (le_min zero_le_one (sq_nonneg x))
