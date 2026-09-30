-- Prove2me | solution 1 for UnderstandingML.hard_svm_generalization_rademacher
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T16:36:27.652103+00:00
-- url     : https://prove2.me/submissions/4ae67a1a-236a-4d38-afaa-f5354b2c358e

import Theorems.Thm_UnderstandingML_linear_l2_generalization
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML.HardSVMAux

/-- The ramp loss `min 1 (max 0 (1 - ȳ a))`, where `ȳ` is `y` clamped to `[-1, 1]`. -/
noncomputable def ramp (a y : ℝ) : ℝ := min 1 (max 0 (1 - max (-1) (min 1 y) * a))

lemma abs_clamp_le (y : ℝ) : |max (-1) (min 1 y)| ≤ 1 := by
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma ramp_lipschitz (y : ℝ) : LipschitzWith 1 (fun a : ℝ ↦ ramp a y) := by
  refine LipschitzWith.of_dist_le_mul (fun a b ↦ ?_)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, ramp]
  set t := max (-1) (min 1 y)
  calc |min 1 (max 0 (1 - t * a)) - min 1 (max 0 (1 - t * b))|
      ≤ |max 0 (1 - t * a) - max 0 (1 - t * b)| := by
        have := abs_min_sub_min_le_max (1 : ℝ) (max 0 (1 - t * a)) 1 (max 0 (1 - t * b))
        simpa using this
    _ ≤ |(1 - t * a) - (1 - t * b)| := by
        have := abs_max_sub_max_le_max (0 : ℝ) (1 - t * a) 0 (1 - t * b)
        simpa using this
    _ = |t| * |a - b| := by
        rw [show (1 - t * a) - (1 - t * b) = t * (b - a) by ring, abs_mul, abs_sub_comm]
    _ ≤ 1 * |a - b| := mul_le_mul_of_nonneg_right (abs_clamp_le y) (abs_nonneg _)
    _ = |a - b| := one_mul _

lemma ramp_nonneg (a y : ℝ) : 0 ≤ ramp a y :=
  le_min zero_le_one (le_max_left _ _)

lemma ramp_le_one (a y : ℝ) : ramp a y ≤ 1 := min_le_left _ _

lemma ramp_continuous : Continuous (Function.uncurry ramp) := by
  unfold ramp Function.uncurry
  fun_prop

lemma iidLaw_exists_null {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (m : ℕ) (T : Set Z) (hT : MeasurableSet T) (h0 : D T = 0) :
    iidLaw D m {S | ∃ i, S i ∈ T} = 0 := by
  have : {S : Fin m → Z | ∃ i, S i ∈ T} = ⋃ i, (fun S : Fin m → Z ↦ S i) ⁻¹' T := by
    ext S; simp
  rw [this]
  refine measure_iUnion_null (fun i ↦ ?_)
  have hp := measurePreserving_eval (fun _ : Fin m ↦ D) i
  unfold iidLaw
  rw [show (fun S : Fin m → Z ↦ S i) = Function.eval i from rfl,
    hp.measure_preimage hT.nullMeasurableSet]
  exact h0

end UnderstandingML.HardSVMAux

open UnderstandingML.HardSVMAux in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (D : Measure (E × ℝ)) [IsProbabilityMeasure D] (hy : D {p | p.2 ≠ 1 ∧ p.2 ≠ -1} = 0)
    (wstar : E) (hsep : D {p | p.2 * ⟪wstar, p.1⟫_ℝ < 1} = 0) (R : ℝ) (hR : D {p | R < ‖p.1‖} = 0)
    (A : UnderstandingML.Learner (E × ℝ) E)
    (hA : ∀ (m : ℕ) (S : Fin m → E × ℝ), (∃ w : E, ∀ i, 1 ≤ (S i).2 * ⟪w, (S i).1⟫_ℝ) →
      (∀ i, 1 ≤ (S i).2 * ⟪A m S, (S i).1⟫_ℝ) ∧
      ∀ w' : E, (∀ i, 1 ≤ (S i).2 * ⟪w', (S i).1⟫_ℝ) → ‖A m S‖ ≤ ‖w'‖)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    UnderstandingML.iidLaw D m {S | 2 * R * ‖wstar‖ / Real.sqrt m +
      (1 + R * ‖wstar‖) * Real.sqrt (2 * Real.log (2 / δ) / m) <
        (D {p | p.2 * ⟪A m S, p.1⟫_ℝ ≤ 0}).toReal} ≤ ENNReal.ofReal δ := by
  classical
  have hR0 : 0 ≤ R := by
    by_contra hneg
    replace hneg : R < 0 := lt_of_not_ge hneg
    have : {p : E × ℝ | R < ‖p.1‖} = Set.univ :=
      Set.eq_univ_of_forall (fun p ↦ lt_of_lt_of_le hneg (norm_nonneg _))
    rw [this, measure_univ] at hR
    exact one_ne_zero hR
  have key := UnderstandingML.linear_l2_generalization D R hR ‖wstar‖ (norm_nonneg _) ramp
    ramp_continuous.measurable 1 ramp_lipschitz 1
    (fun a y _ ↦ by rw [abs_of_nonneg (ramp_nonneg a y)]; exact ramp_le_one a y) m hm δ hδ hδ1
  set T1 : Set (E × ℝ) := {p | p.2 ≠ 1 ∧ p.2 ≠ -1} with hT1
  set T2 : Set (E × ℝ) := {p | p.2 * ⟪wstar, p.1⟫_ℝ < 1} with hT2
  have hT1m : MeasurableSet T1 :=
    (measurable_snd (measurableSet_singleton (1 : ℝ)).compl).inter
      (measurable_snd (measurableSet_singleton (-1 : ℝ)).compl)
  have hT2m : MeasurableSet T2 :=
    measurableSet_lt (measurable_snd.mul (measurable_const.inner measurable_fst)) measurable_const
  set N : Set (Fin m → E × ℝ) := {S | ∃ i, S i ∈ T1 ∪ T2} with hN
  have hN0 : UnderstandingML.iidLaw D m N = 0 :=
    iidLaw_exists_null D m _ (hT1m.union hT2m) (measure_union_null hy hsep)
  have hy_ae : ∀ᵐ p ∂D, p ∉ T1 := by
    rw [ae_iff]; simpa using hy
  have hsq : 0 ≤ Real.sqrt (2 * Real.log (2 / δ) / m) := Real.sqrt_nonneg _
  refine le_trans (measure_mono (t := {S | ∃ w : E, ‖w‖ ≤ ‖wstar‖ ∧
      UnderstandingML.empRisk (fun w p ↦ ramp ⟪w, p.1⟫_ℝ p.2) S w +
        2 * ((1 : NNReal) : ℝ) * ‖wstar‖ * R / Real.sqrt m +
        1 * Real.sqrt (2 * Real.log (2 / δ) / m) <
          UnderstandingML.risk (fun w p ↦ ramp ⟪w, p.1⟫_ℝ p.2) D w} ∪ N)
    (fun S hS ↦ ?_)) ?_
  · by_cases hSN : S ∈ N
    · exact Or.inr hSN
    left
    have hgood : ∀ i, S i ∉ T1 ∪ T2 := fun i h ↦ hSN ⟨i, h⟩
    have hfeas : ∀ i, 1 ≤ (S i).2 * ⟪wstar, (S i).1⟫_ℝ := by
      intro i
      by_contra h
      exact hgood i (Or.inr (lt_of_not_ge h))
    have hlab : ∀ i, (S i).2 = 1 ∨ (S i).2 = -1 := by
      intro i
      by_contra h
      rw [not_or] at h
      exact hgood i (Or.inl h)
    obtain ⟨h1, h2⟩ := hA m S ⟨wstar, hfeas⟩
    set w := A m S with hw
    refine ⟨w, h2 wstar hfeas, ?_⟩
    have hemp : UnderstandingML.empRisk (fun w p ↦ ramp ⟪w, p.1⟫_ℝ p.2) S w = 0 := by
      unfold UnderstandingML.empRisk
      rw [div_eq_zero_iff]; left
      refine Finset.sum_eq_zero (fun i _ ↦ ?_)
      have hc : max (-1) (min 1 (S i).2) = (S i).2 := by
        rcases hlab i with h | h <;> rw [h] <;> norm_num
      simp only [ramp, hc]
      have : 1 - (S i).2 * ⟪w, (S i).1⟫_ℝ ≤ 0 := by linarith [h1 i]
      rw [max_eq_left this, min_eq_right zero_le_one]
    have hrisk : (D {p | p.2 * ⟪w, p.1⟫_ℝ ≤ 0}).toReal ≤
        UnderstandingML.risk (fun w p ↦ ramp ⟪w, p.1⟫_ℝ p.2) D w := by
      have hTm : MeasurableSet {p : E × ℝ | p.2 * ⟪w, p.1⟫_ℝ ≤ 0} :=
        measurableSet_le (measurable_snd.mul (measurable_const.inner measurable_fst))
          measurable_const
      have hint : Integrable (fun p : E × ℝ ↦ ramp ⟪w, p.1⟫_ℝ p.2) D := by
        refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall (fun p ↦ ?_))
        · exact (ramp_continuous.measurable.comp
            ((measurable_const.inner measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_of_nonneg (ramp_nonneg _ _)]; exact ramp_le_one _ _
      rw [← measureReal_def, ← integral_indicator_one hTm]
      unfold UnderstandingML.risk
      refine integral_mono_ae ((integrable_const (1 : ℝ)).indicator hTm) hint ?_
      filter_upwards [hy_ae] with p hp
      by_cases hpT : p ∈ {p : E × ℝ | p.2 * ⟪w, p.1⟫_ℝ ≤ 0}
      · rw [Set.indicator_of_mem hpT, Pi.one_apply]
        have hlab' : p.2 = 1 ∨ p.2 = -1 := by
          by_contra h
          rw [not_or] at h
          exact hp h
        have hc : max (-1) (min 1 p.2) = p.2 := by
          rcases hlab' with h | h <;> rw [h] <;> norm_num
        have hpT' : p.2 * ⟪w, p.1⟫_ℝ ≤ 0 := hpT
        simp only [ramp, hc]
        have : 1 ≤ max 0 (1 - p.2 * ⟪w, p.1⟫_ℝ) := le_max_of_le_right (by linarith)
        rw [min_eq_left this]
      · rw [Set.indicator_of_notMem hpT]; exact ramp_nonneg _ _
    rw [hemp, NNReal.coe_one]
    have hS' : 2 * R * ‖wstar‖ / Real.sqrt m +
        (1 + R * ‖wstar‖) * Real.sqrt (2 * Real.log (2 / δ) / m) <
        (D {p | p.2 * ⟪w, p.1⟫_ℝ ≤ 0}).toReal := hS
    have hRw : 0 ≤ R * ‖wstar‖ * Real.sqrt (2 * Real.log (2 / δ) / m) :=
      mul_nonneg (mul_nonneg hR0 (norm_nonneg _)) hsq
    have heq : 2 * 1 * ‖wstar‖ * R / Real.sqrt m = 2 * R * ‖wstar‖ / Real.sqrt m := by ring
    rw [heq]
    nlinarith
  · refine (measure_union_le _ _).trans ?_
    rw [hN0, add_zero]
    exact key
