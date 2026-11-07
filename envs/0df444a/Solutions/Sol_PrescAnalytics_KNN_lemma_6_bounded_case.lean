-- Prove2me | solution 1 for PrescAnalytics.KNN.lemma_6_bounded_case
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:05:08.676577+00:00
-- url     : https://prove2.me/submissions/ca9c15f3-b054-4ea3-aa3a-6bb99948ecf5

import Mathlib
import Definitions.Def_PrescAnalytics_KNN_Basic
import Theorems.Thm_PrescAnalytics_KNN_lemma_5_uniform_on_compacts

open MeasureTheory ProbabilityTheory Filter Topology

open PrescAnalytics.KNN in
theorem solution
    {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) (Ys : Set (EuclideanSpace ℝ (Fin dy)))
    (hZ_closed : IsClosed Z) (hZ_bdd : Bornology.IsBounded Z) (hZ_ne : Z.Nonempty)
    (x : EuclideanSpace ℝ (Fin dx))
    (w : ℕ → ℕ → ℝ) (ys : ℕ → EuclideanSpace ℝ (Fin dy))
    (hys : ∀ i, ys i ∈ Ys) (hYx : ∀ᵐ y ∂(μ.condKernel x), y ∈ Ys)
    (hw : ∀ᶠ N in atTop, (∀ i < N, 0 ≤ w N i) ∧ ∑ i ∈ Finset.range N, w N i = 1)
    (h3x : ∀ z ∈ Z, Integrable (c z) (μ.condKernel x))
    (h4 : Assumption4 c Z Ys)
    (hconv : ∀ z ∈ Z, Tendsto (fun N => weightedCost c w ys N z) atTop (𝓝 (condCost μ c z x))) :
    (optSet μ c Z x).Nonempty ∧
      (∀ᶠ N in atTop, (weightedArgmin c w ys Z N).Nonempty) ∧
      ∀ zN : ℕ → EuclideanSpace ℝ (Fin dz), (∀ᶠ N in atTop, zN N ∈ weightedArgmin c w ys Z N) →
        (∀ zstar ∈ optSet μ c Z x,
          Tendsto (fun N => weightedCost c w ys N (zN N)) atTop (𝓝 (condCost μ c zstar x)) ∧
          Tendsto (fun N => condCost μ c (zN N) x) atTop (𝓝 (condCost μ c zstar x))) ∧
        Tendsto (fun N => Metric.infDist (zN N) (optSet μ c Z x)) atTop (𝓝 0) := by
  have hKc : IsCompact Z := Metric.isCompact_of_isClosed_isBounded hZ_closed hZ_bdd
  -- difference of weighted costs
  have hWC : ∀ (N : ℕ) (z z' : EuclideanSpace ℝ (Fin dz)) (e : ℝ),
      (∀ i < N, 0 ≤ w N i) → ∑ i ∈ Finset.range N, w N i = 1 →
      (∀ y ∈ Ys, |c z y - c z' y| ≤ e) →
      |weightedCost c w ys N z - weightedCost c w ys N z'| ≤ e := by
    intro N z z' e hnn hsum hb
    unfold weightedCost weightedMean
    rw [← Finset.sum_sub_distrib]
    calc |∑ i ∈ Finset.range N, (w N i * c z (ys i) - w N i * c z' (ys i))|
        ≤ ∑ i ∈ Finset.range N, |w N i * c z (ys i) - w N i * c z' (ys i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, w N i * e := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_range.mp hi
          rw [← mul_sub, abs_mul, abs_of_nonneg (hnn i hi')]
          exact mul_le_mul_of_nonneg_left (hb _ (hys i)) (hnn i hi')
      _ = e := by rw [← Finset.sum_mul, hsum, one_mul]
  -- difference of conditional costs
  have hCC : ∀ (z z' : EuclideanSpace ℝ (Fin dz)) (e : ℝ), z ∈ Z → z' ∈ Z →
      (∀ y ∈ Ys, |c z y - c z' y| ≤ e) →
      |condCost μ c z x - condCost μ c z' x| ≤ e := by
    intro z z' e hz hz' hb
    unfold condCost
    rw [← integral_sub (h3x z hz) (h3x z' hz')]
    have := norm_integral_le_of_norm_le_const (μ := μ.condKernel x)
      (f := fun y => c z y - c z' y) (C := e)
      (hYx.mono fun y hy => by simpa [Real.norm_eq_abs] using hb y hy)
    simpa [Real.norm_eq_abs] using this
  -- continuity
  have hCcont : ContinuousOn (fun z => condCost μ c z x) Z := by
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    obtain ⟨δ, hδ, hδb⟩ := h4 b hb (ε / 2) (by linarith)
    refine ⟨δ, hδ, fun a ha hab => ?_⟩
    have hd : ‖b - a‖ ≤ δ := by rw [← dist_eq_norm, dist_comm]; exact le_of_lt hab
    have := hCC b a (ε / 2) hb ha (hδb a ha hd)
    rw [Real.dist_eq, abs_sub_comm]; linarith
  have hWcont : ∀ N, (∀ i < N, 0 ≤ w N i) → ∑ i ∈ Finset.range N, w N i = 1 →
      ContinuousOn (fun z => weightedCost c w ys N z) Z := by
    intro N hnn hsum
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    obtain ⟨δ, hδ, hδb⟩ := h4 b hb (ε / 2) (by linarith)
    refine ⟨δ, hδ, fun a ha hab => ?_⟩
    have hd : ‖b - a‖ ≤ δ := by rw [← dist_eq_norm, dist_comm]; exact le_of_lt hab
    have := hWC N b a (ε / 2) hnn hsum (hδb a ha hd)
    rw [Real.dist_eq, abs_sub_comm]; linarith
  obtain ⟨zs, hzsZ, hzsmin⟩ := hKc.exists_isMinOn hZ_ne hCcont
  have hzsopt : zs ∈ optSet μ c Z x := ⟨hzsZ, fun z' hz' => isMinOn_iff.mp hzsmin z' hz'⟩
  have hU := lemma_5_uniform_on_compacts μ c Z Ys x w ys hys hYx hw h3x h4 hconv Z hKc
    subset_rfl
  rw [Metric.tendstoUniformlyOn_iff] at hU
  refine ⟨⟨zs, hzsopt⟩, ?_, ?_⟩
  · filter_upwards [hw] with N hN
    obtain ⟨a, haZ, hamin⟩ := hKc.exists_isMinOn hZ_ne (hWcont N hN.1 hN.2)
    exact ⟨a, haZ, fun z' hz' => isMinOn_iff.mp hamin z' hz'⟩
  intro zN hzN
  have hB : ∀ zstar ∈ optSet μ c Z x,
      Tendsto (fun N => weightedCost c w ys N (zN N)) atTop (𝓝 (condCost μ c zstar x)) ∧
      Tendsto (fun N => condCost μ c (zN N) x) atTop (𝓝 (condCost μ c zstar x)) := by
    intro zstar hzstar
    constructor
    · rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hzN, hU (ε / 2) (by linarith)] with N hNa hNu
      have h1 := hNa.2 zstar hzstar.1
      have h2 := hNu zstar hzstar.1
      have h3 := hNu (zN N) hNa.1
      have h4' := hzstar.2 (zN N) hNa.1
      rw [Real.dist_eq] at h2 h3 ⊢
      rw [abs_sub_lt_iff] at h2 h3 ⊢
      constructor <;> linarith
    · rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [hzN, hU (ε / 2) (by linarith)] with N hNa hNu
      have h1 := hNa.2 zstar hzstar.1
      have h2 := hNu zstar hzstar.1
      have h3 := hNu (zN N) hNa.1
      have h4' := hzstar.2 (zN N) hNa.1
      rw [Real.dist_eq] at h2 h3 ⊢
      rw [abs_sub_lt_iff] at h2 h3 ⊢
      constructor <;> linarith
  refine ⟨hB, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  set A := Z ∩ {z | ε ≤ Metric.infDist z (optSet μ c Z x)} with hAdef
  have hAc : IsCompact A := hKc.of_isClosed_subset
    (hZ_closed.inter (isClosed_le continuous_const (Metric.continuous_infDist_pt _)))
    Set.inter_subset_left
  by_cases hA : A.Nonempty
  · obtain ⟨a, haA, hamin⟩ := hAc.exists_isMinOn hA (hCcont.mono Set.inter_subset_left)
    have hanot : a ∉ optSet μ c Z x := by
      intro hao
      have := haA.2
      simp only [Set.mem_setOf_eq, Metric.infDist_zero_of_mem hao] at this
      linarith
    have : ∃ z' ∈ Z, condCost μ c z' x < condCost μ c a x := by
      by_contra hcon
      push_neg at hcon
      exact hanot ⟨haA.1, hcon⟩
    obtain ⟨z', hz'Z, hz'lt⟩ := this
    have hzsz' := hzsopt.2 z' hz'Z
    have hη : 0 < condCost μ c a x - condCost μ c zs x := by linarith
    have hT := (Metric.tendsto_nhds.mp (hB zs hzsopt).2) _ hη
    filter_upwards [hT, hzN] with N h1 h2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
    by_contra hcon
    push_neg at hcon
    have hmemA : zN N ∈ A := ⟨h2.1, hcon⟩
    have := isMinOn_iff.mp hamin (zN N) hmemA
    rw [Real.dist_eq] at h1
    have := (abs_sub_lt_iff.mp h1).1
    linarith
  · filter_upwards [hzN] with N h2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
    by_contra hcon
    push_neg at hcon
    exact hA ⟨zN N, h2.1, hcon⟩
