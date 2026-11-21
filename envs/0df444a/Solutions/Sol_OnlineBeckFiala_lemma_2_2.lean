-- Prove2me | solution 1 for OnlineBeckFiala.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:11:11.950178+00:00
-- url     : https://prove2.me/submissions/0273261c-eb1c-4059-8444-e7167fb5846f

import Mathlib
import Definitions.Def_OnlineBeckFiala_walkLaw

section
open MeasureTheory

namespace OnlineBeckFiala

namespace Dev.L22

variable {n : ℕ}

theorem cube_meas (L : ℝ) : MeasurableSet (cube (n := n) L) := by
  have : cube (n := n) L = ⋂ i, (fun x : Fin n → ℝ => x i) ⁻¹' Set.Ioo (-L) L := by
    ext x; simp [cube]
  rw [this]
  exact MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Ioo

theorem nonneg (L : ℝ) (μ : (Fin n → ℝ) → ℝ) (hμpos : ∀ x ∈ cube L, 0 < μ x)
    (hμzero : ∀ x ∉ cube L, μ x = 0) (x : Fin n → ℝ) : 0 ≤ μ x := by
  by_cases h : x ∈ cube L
  · exact (hμpos x h).le
  · rw [hμzero x h]

/-- detailed balance quantity -/
noncomputable def g (μ : (Fin n → ℝ) → ℝ) (v x : Fin n → ℝ) : ℝ :=
  1 / 3 * min (μ x) (μ (x + v))

theorem mul_pPlus (L : ℝ) (μ : (Fin n → ℝ) → ℝ) (hμpos : ∀ x ∈ cube L, 0 < μ x)
    (hμzero : ∀ x ∉ cube L, μ x = 0) (v x : Fin n → ℝ) :
    μ x * pPlus μ v x = g μ v x := by
  unfold pPlus g
  by_cases h : x ∈ cube L
  · have hp := hμpos x h
    rw [mul_left_comm, mul_min_of_nonneg _ _ hp.le]
    congr 2
    · ring
    · field_simp
  · rw [hμzero x h]
    have := nonneg L μ hμpos hμzero (x + v)
    simp [min_eq_left this]

theorem mul_pMinus (L : ℝ) (μ : (Fin n → ℝ) → ℝ) (hμpos : ∀ x ∈ cube L, 0 < μ x)
    (hμzero : ∀ x ∉ cube L, μ x = 0) (v x : Fin n → ℝ) :
    μ x * pMinus μ v x = 1 / 3 * min (μ x) (μ (x - v)) := by
  unfold pMinus
  by_cases h : x ∈ cube L
  · have hp := hμpos x h
    rw [mul_left_comm, mul_min_of_nonneg _ _ hp.le]
    congr 2
    · ring
    · field_simp
  · rw [hμzero x h]
    have := nonneg L μ hμpos hμzero (x - v)
    simp [min_eq_left this]

theorem pointwise (L : ℝ) (μ : (Fin n → ℝ) → ℝ) (hμpos : ∀ x ∈ cube L, 0 < μ x)
    (hμzero : ∀ x ∉ cube L, μ x = 0) (v x : Fin n → ℝ) (s : Set (Fin n → ℝ))
    (hs : MeasurableSet s) :
    ENNReal.ofReal (μ x) * stepMeasure μ L v x s =
      ENNReal.ofReal (g μ v x) * s.indicator 1 (x + v) +
      ENNReal.ofReal (1 / 3 * min (μ x) (μ (x - v))) * s.indicator 1 (x - v) +
      ENNReal.ofReal (μ x - g μ v x - 1 / 3 * min (μ x) (μ (x - v))) * s.indicator 1 x := by
  have h1 := mul_pPlus L μ hμpos hμzero v x
  have h2 := mul_pMinus L μ hμpos hμzero v x
  have hn := nonneg L μ hμpos hμzero x
  unfold stepMeasure
  by_cases h : x ∈ cube L
  · have hp := hμpos x h
    rw [if_pos h]
    have hp1 : 0 ≤ pPlus μ v x := by
      unfold pPlus
      have := nonneg L μ hμpos hμzero (x + v)
      positivity
    have hp2 : 0 ≤ pMinus μ v x := by
      unfold pMinus
      have := nonneg L μ hμpos hμzero (x - v)
      positivity
    have h3 : μ x - g μ v x - 1 / 3 * min (μ x) (μ (x - v)) = μ x * pZero μ v x := by
      unfold pZero; rw [← h1, ← h2]; ring
    have hp0 : 0 ≤ pZero μ v x := by
      unfold pZero pPlus pMinus
      have a1 : min 1 (μ (x + v) / μ x) ≤ 1 := min_le_left _ _
      have a2 : min 1 (μ (x - v) / μ x) ≤ 1 := min_le_left _ _
      linarith
    rw [h3]
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
    rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hn,
      ← ENNReal.ofReal_mul hn, ← ENNReal.ofReal_mul hn, h1, h2]
  · rw [if_neg h, hμzero x h]
    have := nonneg L μ hμpos hμzero (x + v)
    have := nonneg L μ hμpos hμzero (x - v)
    simp [g, min_eq_left, *]

theorem step_meas (L : ℝ) (μ : (Fin n → ℝ) → ℝ) (hμm : Measurable μ) (v : Fin n → ℝ) :
    Measurable (stepMeasure μ L v) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  unfold stepMeasure
  have hind : Measurable fun x : Fin n → ℝ => s.indicator (1 : (Fin n → ℝ) → ENNReal) x :=
    measurable_one.indicator hs
  have hind1 : Measurable fun x : Fin n → ℝ => s.indicator (1 : (Fin n → ℝ) → ENNReal) (x + v) :=
    hind.comp (measurable_add_const v)
  have hind2 : Measurable fun x : Fin n → ℝ => s.indicator (1 : (Fin n → ℝ) → ENNReal) (x - v) :=
    hind.comp (measurable_sub_const v)
  have m1 : Measurable fun x => μ (x + v) := hμm.comp (measurable_add_const v)
  have m2 : Measurable fun x => μ (x - v) := hμm.comp (measurable_sub_const v)
  have hpP : Measurable fun x => pPlus μ v x := by
    unfold pPlus; fun_prop
  have hpM : Measurable fun x => pMinus μ v x := by
    unfold pMinus; fun_prop
  have hpZ : Measurable fun x => pZero μ v x := by
    unfold pZero; fun_prop
  simp only [apply_ite (fun m : Measure (Fin n → ℝ) => m s)]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
  refine Measurable.ite (p := fun x => x ∈ cube L) (cube_meas L) ?_ hind
  exact ((hpP.ennreal_ofReal.mul hind1).add (hpM.ennreal_ofReal.mul hind2)).add
    (hpZ.ennreal_ofReal.mul hind)

theorem invariant (L : ℝ) (μ : (Fin n → ℝ) → ℝ) (hμm : Measurable μ)
    (hμpos : ∀ x ∈ cube L, 0 < μ x) (hμzero : ∀ x ∉ cube L, μ x = 0) (v : Fin n → ℝ) :
    (densityLaw μ).bind (stepMeasure μ L v) = densityLaw μ := by
  ext s hs
  have hnn := nonneg L μ hμpos hμzero
  rw [Measure.bind_apply hs (step_meas L μ hμm v).aemeasurable]
  unfold densityLaw
  have hmeas : Measurable fun a => stepMeasure μ L v a s :=
    (Measure.measurable_coe hs).comp (step_meas L μ hμm v)
  rw [lintegral_withDensity_eq_lintegral_mul volume hμm.ennreal_ofReal hmeas,
    withDensity_apply _ hs, ← lintegral_indicator hs]
  simp only [Pi.mul_apply, Function.comp]
  simp_rw [pointwise L μ hμpos hμzero v _ s hs]
  have m1 : Measurable fun x => μ (x + v) := hμm.comp (measurable_add_const v)
  have m2 : Measurable fun x => μ (x - v) := hμm.comp (measurable_sub_const v)
  have hind : Measurable fun x : Fin n → ℝ => s.indicator (1 : (Fin n → ℝ) → ENNReal) x :=
    measurable_one.indicator hs
  have hg : Measurable fun x => g μ v x := by unfold g; fun_prop
  have hg2 : Measurable fun x => 1 / 3 * min (μ x) (μ (x - v)) := by fun_prop
  rw [lintegral_add_left, lintegral_add_left]
  · -- shifts
    have e1 : ∫⁻ x, ENNReal.ofReal (g μ v x) * s.indicator 1 (x + v) =
        ∫⁻ z, ENNReal.ofReal (1 / 3 * min (μ z) (μ (z - v))) * s.indicator 1 z := by
      rw [← lintegral_add_right_eq_self
        (fun z => ENNReal.ofReal (1 / 3 * min (μ z) (μ (z - v))) * s.indicator 1 z) v]
      refine lintegral_congr fun x => ?_
      simp only [g, add_sub_cancel_right, min_comm]
    have e2 : ∫⁻ x, ENNReal.ofReal (1 / 3 * min (μ x) (μ (x - v))) * s.indicator 1 (x - v) =
        ∫⁻ z, ENNReal.ofReal (g μ v z) * s.indicator 1 z := by
      rw [← lintegral_sub_right_eq_self
        (fun z => ENNReal.ofReal (g μ v z) * s.indicator 1 z) v]
      refine lintegral_congr fun x => ?_
      simp only [g, sub_add_cancel, min_comm]
    rw [e1, e2, ← lintegral_add_left, ← lintegral_add_left]
    · refine lintegral_congr fun z => ?_
      have a1 : 0 ≤ g μ v z := by
        unfold g; have := hnn z; have := hnn (z + v); positivity
      have a2 : 0 ≤ 1 / 3 * min (μ z) (μ (z - v)) := by
        have := hnn z; have := hnn (z - v); positivity
      have a3 : g μ v z ≤ 1 / 3 * μ z := by
        unfold g; have := min_le_left (μ z) (μ (z + v)); linarith
      have a4 : 1 / 3 * min (μ z) (μ (z - v)) ≤ 1 / 3 * μ z := by
        have := min_le_left (μ z) (μ (z - v)); linarith
      have a5 : 0 ≤ μ z - g μ v z - 1 / 3 * min (μ z) (μ (z - v)) := by
        have := hnn z; linarith
      rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add a2 a1, ← ENNReal.ofReal_add (by positivity) a5]
      have e : 1 / 3 * min (μ z) (μ (z - v)) + g μ v z +
          (μ z - g μ v z - 1 / 3 * min (μ z) (μ (z - v))) = μ z := by ring
      rw [e]
      by_cases hz : z ∈ s <;> simp [hz]
    all_goals first
      | exact (hg.ennreal_ofReal.mul hind)
      | exact (hg2.ennreal_ofReal.mul hind)
      | exact (hg2.ennreal_ofReal.mul hind).add (hg.ennreal_ofReal.mul hind)
  · exact hg.ennreal_ofReal.mul (hind.comp (measurable_add_const v))
  · exact (hg.ennreal_ofReal.mul (hind.comp (measurable_add_const v))).add
      (hg2.ennreal_ofReal.mul (hind.comp (measurable_sub_const v)))

theorem fold (L : ℝ) (μ : (Fin n → ℝ) → ℝ) (ν : Measure (Fin n → ℝ))
    (h : ∀ w : Fin n → ℝ, ν.bind (stepMeasure μ L w) = ν) (vs : List (Fin n → ℝ)) :
    vs.foldl (fun ν v => ν.bind (stepMeasure μ L v)) ν = ν := by
  induction vs with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl_cons, h w]
    exact ih

end Dev.L22

theorem chk_lemma_2_2 {n : ℕ} (L : ℝ) (μ : (Fin n → ℝ) → ℝ) (hμm : Measurable μ)
    (hμpos : ∀ x ∈ cube L, 0 < μ x) (hμzero : ∀ x ∉ cube L, μ x = 0)
    (hμint : ∫ x, μ x = 1) (vs : List (Fin n → ℝ)) :
    walkLaw μ L vs = densityLaw μ := by
  unfold walkLaw
  exact Dev.L22.fold L μ _ (Dev.L22.invariant L μ hμm hμpos hμzero) vs

end OnlineBeckFiala

end

theorem solution : type_of% @OnlineBeckFiala.chk_lemma_2_2 := @OnlineBeckFiala.chk_lemma_2_2
