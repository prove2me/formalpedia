-- Prove2me | solution 1 for StoneRegression.Criterion.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:07:18.422935+00:00
-- url     : https://prove2.me/submissions/5c0ab7c4-0b16-4837-baed-14ba69f7a880

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction


namespace StoneRegression.Criterion

lemma p6_clip (t : ℝ) : 0 ≤ min 1 (max 0 t) ∧ min 1 (max 0 t) ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

noncomputable def p6g {d : ℕ} (a : ℝ) (c : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => min 1 (max 0 ((2 / a) * ‖z - c‖ - 1 / 2)),
      continuous_const.min (continuous_const.max
        ((continuous_const.mul (continuous_id.sub continuous_const).norm).sub continuous_const))⟩ 1
    (by
      intro x y
      simp only [ContinuousMap.coe_mk]
      rw [Real.dist_eq, abs_le]
      have h1 := p6_clip ((2 / a) * ‖x - c‖ - 1 / 2)
      have h2 := p6_clip ((2 / a) * ‖y - c‖ - 1 / 2)
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])

lemma p6g_apply {d : ℕ} (a : ℝ) (c z : EuclideanSpace ℝ (Fin d)) :
    p6g a c z = min 1 (max 0 ((2 / a) * ‖z - c‖ - 1 / 2)) := rfl

theorem p6_core {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hnn : Nonneg W)
    (hconv : ∀ f : EuclideanSpace ℝ (Fin d) →ᵇ ℝ, TendstoInMeasure (xLaw μ)
      (fun n ω => ∑ i : Fin n, wAt W n ω i * f (ω (i.val + 1))) atTop (fun ω => f (ω 0))) :
    Cond3 μ W := by
  intro a ha
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (EuclideanSpace ℝ (Fin d))
  set U : ℕ → Set (EuclideanSpace ℝ (Fin d)) :=
    fun J => ⋃ j ∈ Finset.range J, Metric.ball (u j) (a / 4) with hU
  have hUmono : Monotone U := by
    intro J K hJK x hx
    simp only [hU, Set.mem_iUnion, Finset.mem_range] at hx ⊢
    obtain ⟨j, hj, hx⟩ := hx
    exact ⟨j, by omega, hx⟩
  have hUall : ⋃ J, U J = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true, hU, Set.mem_iUnion, Finset.mem_range]
    obtain ⟨j, hj⟩ := hu.exists_dist_lt x (by positivity : (0:ℝ) < a / 4)
    exact ⟨j + 1, j, by omega, by rw [Metric.mem_ball]; exact hj⟩
  have hm : ∀ J, MeasurableSet (U J) := fun J =>
    Finset.measurableSet_biUnion _ (fun j _ => measurableSet_ball)
  have hlim := tendsto_measure_iUnion_atTop (μ := μ) hUmono
  rw [hUall, measure_univ] at hlim
  have hlimc : Tendsto (fun J => μ (U J)ᶜ) atTop (𝓝 0) := by
    have e : (fun J => μ (U J)ᶜ) = fun J => 1 - μ (U J) :=
      funext fun J => prob_compl_eq_one_sub (hm J)
    rw [e]
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1:ℝ≥0∞))) hlim
      (Or.inl ENNReal.one_ne_top)
    simpa using this
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨J, hJ⟩ := (ENNReal.tendsto_nhds_zero.1 hlimc (δ / 2) hδ2).exists
  have hsum : Tendsto (fun n => ∑ j ∈ Finset.range J, xLaw μ {ω | ε ≤ dist
      (∑ i : Fin n, wAt W n ω i * p6g a (u j) (ω (i.val + 1))) (p6g a (u j) (ω 0))}) atTop
      (𝓝 0) := by
    have := tendsto_finset_sum (Finset.range J) (fun j _ =>
      (tendstoInMeasure_iff_dist.1 (hconv (p6g a (u j)))) ε hε)
    simpa using this
  have hev := ENNReal.tendsto_nhds_zero.1 hsum (δ / 2) hδ2
  filter_upwards [hev] with n hn
  have hsub : {ω : ℕ → EuclideanSpace ℝ (Fin d) | ε ≤ dist (∑ i : Fin n, |wAt W n ω i| *
      (if a < ‖ω (i.val + 1) - ω 0‖ then (1:ℝ) else 0)) 0} ⊆
      (fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ω 0) ⁻¹' (U J)ᶜ ∪
        ⋃ j ∈ Finset.range J, {ω | ε ≤ dist
          (∑ i : Fin n, wAt W n ω i * p6g a (u j) (ω (i.val + 1))) (p6g a (u j) (ω 0))} := by
    intro ω hω
    by_cases h0 : ω 0 ∈ U J
    · right
      simp only [hU, Set.mem_iUnion, Finset.mem_range] at h0
      obtain ⟨j, hj, hball⟩ := h0
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq]
      refine ⟨j, hj, le_trans hω ?_⟩
      rw [Metric.mem_ball] at hball
      have hg0 : p6g a (u j) (ω 0) = 0 := by
        rw [p6g_apply, dist_eq_norm] at *
        have : (2 / a) * ‖ω 0 - u j‖ - 1 / 2 ≤ 0 := by
          have : (2 / a) * ‖ω 0 - u j‖ ≤ (2 / a) * (a / 4) := by gcongr
          have e : (2 / a) * (a / 4) = 1 / 2 := by field_simp; norm_num
          linarith
        rw [max_eq_left this, min_eq_right zero_le_one]
      have hZ0 : 0 ≤ ∑ i : Fin n, |wAt W n ω i| *
          (if a < ‖ω (i.val + 1) - ω 0‖ then (1:ℝ) else 0) :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (by split_ifs <;> norm_num))
      have hZ : ∑ i : Fin n, |wAt W n ω i| * (if a < ‖ω (i.val + 1) - ω 0‖ then (1:ℝ) else 0) ≤
          ∑ i : Fin n, wAt W n ω i * p6g a (u j) (ω (i.val + 1)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hw : 0 ≤ wAt W n ω i := hnn _ _ _ _
        rw [abs_of_nonneg hw]
        split_ifs with hfar
        · rw [mul_one]
          have : p6g a (u j) (ω (i.val + 1)) = 1 := by
            rw [p6g_apply]
            have htri : a - a / 4 < ‖ω (i.val + 1) - u j‖ := by
              have := norm_sub_le_norm_sub_add_norm_sub (ω (i.val + 1)) (u j) (ω 0)
              rw [dist_eq_norm] at hball
              have e2 : ‖u j - ω 0‖ = ‖ω 0 - u j‖ := norm_sub_rev _ _
              linarith
            have : 1 ≤ (2 / a) * ‖ω (i.val + 1) - u j‖ - 1 / 2 := by
              have h3 : (2 / a) * (a - a / 4) ≤ (2 / a) * ‖ω (i.val + 1) - u j‖ := by
                gcongr
              have e : (2 / a) * (a - a / 4) = 3 / 2 := by field_simp; norm_num
              linarith
            rw [max_eq_right (by linarith), min_eq_left this]
          rw [this, mul_one]
        · rw [mul_zero]
          exact mul_nonneg hw (p6_clip _).1
      rw [hg0, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, abs_of_nonneg hZ0]
      exact hZ.trans (le_abs_self _)
    · left
      exact h0
  calc xLaw μ {ω : ℕ → EuclideanSpace ℝ (Fin d) | ε ≤ dist (∑ i : Fin n, |wAt W n ω i| *
      (if a < ‖ω (i.val + 1) - ω 0‖ then (1:ℝ) else 0)) 0}
      ≤ xLaw μ ((fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ω 0) ⁻¹' (U J)ᶜ ∪
        ⋃ j ∈ Finset.range J, {ω | ε ≤ dist
          (∑ i : Fin n, wAt W n ω i * p6g a (u j) (ω (i.val + 1))) (p6g a (u j) (ω 0))}) :=
        measure_mono hsub
    _ ≤ xLaw μ ((fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ω 0) ⁻¹' (U J)ᶜ) +
        ∑ j ∈ Finset.range J, xLaw μ {ω | ε ≤ dist
          (∑ i : Fin n, wAt W n ω i * p6g a (u j) (ω (i.val + 1))) (p6g a (u j) (ω 0))} :=
        (measure_union_le _ _).trans (by gcongr; exact measure_biUnion_finset_le _ _)
    _ ≤ δ / 2 + δ / 2 := by
        gcongr
        rw [show xLaw μ ((fun ω : ℕ → EuclideanSpace ℝ (Fin d) => ω 0) ⁻¹' (U J)ᶜ) = μ (U J)ᶜ from
          (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) 0).measure_preimage
            (hm J).compl.nullMeasurableSet]
        exact hJ
    _ = δ := ENNReal.add_halves δ

end StoneRegression.Criterion

open StoneRegression.Criterion


theorem solution {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hnn : Nonneg W)
    (hconv : ∀ f : EuclideanSpace ℝ (Fin d) →ᵇ ℝ, TendstoInMeasure (xLaw μ)
      (fun n ω => ∑ i : Fin n, wAt W n ω i * f (ω (i.val + 1))) atTop (fun ω => f (ω 0))) :
    Cond3 μ W := by
  exact p6_core μ W hnn hconv
