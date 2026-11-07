-- Prove2me | solution 1 for PrescAnalytics.KNN.lemma_5_uniform_on_compacts
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:02:54.745089+00:00
-- url     : https://prove2.me/submissions/fdafc2e5-be2c-4d09-ae15-133ea5440426

import Mathlib
import Definitions.Def_PrescAnalytics_KNN_Basic

open MeasureTheory ProbabilityTheory Filter Topology

open PrescAnalytics.KNN in
theorem solution
    {dx dy dz : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure μ]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (Z : Set (EuclideanSpace ℝ (Fin dz))) (Ys : Set (EuclideanSpace ℝ (Fin dy)))
    (x : EuclideanSpace ℝ (Fin dx))
    (w : ℕ → ℕ → ℝ) (ys : ℕ → EuclideanSpace ℝ (Fin dy))
    (hys : ∀ i, ys i ∈ Ys) (hYx : ∀ᵐ y ∂(μ.condKernel x), y ∈ Ys)
    (hw : ∀ᶠ N in atTop, (∀ i < N, 0 ≤ w N i) ∧ ∑ i ∈ Finset.range N, w N i = 1)
    (h3x : ∀ z ∈ Z, Integrable (c z) (μ.condKernel x))
    (h4 : Assumption4 c Z Ys)
    (hconv : ∀ z ∈ Z, Tendsto (fun N => weightedCost c w ys N z) atTop (𝓝 (condCost μ c z x)))
    (K : Set (EuclideanSpace ℝ (Fin dz))) (hK : IsCompact K) (hKZ : K ⊆ Z) :
    TendstoUniformlyOn (fun N z => weightedCost c w ys N z) (fun z => condCost μ c z x) atTop K := by
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
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he : (0 : ℝ) < ε / 4 := by linarith
  choose δ hδpos hδ using fun z (hz : z ∈ K) => h4 z (hKZ hz) (ε / 4) he
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun z hz => Metric.ball z (δ z hz))
    (fun z hz => Metric.ball_mem_nhds z (hδpos z hz))
  have hev : ∀ᶠ N in atTop, ∀ s ∈ t,
      |weightedCost c w ys N (s : EuclideanSpace ℝ (Fin dz)) - condCost μ c s x| < ε / 4 := by
    rw [Filter.eventually_all_finset]
    intro s _
    have := (hconv s (hKZ s.2))
    rw [Metric.tendsto_atTop] at this
    obtain ⟨N0, hN0⟩ := this (ε / 4) he
    exact Filter.eventually_atTop.2 ⟨N0, fun N hN => by
      have := hN0 N hN; rwa [Real.dist_eq] at this⟩
  filter_upwards [hw, hev] with N hN hNt
  intro z hz
  have hz' := ht hz
  simp only [Set.mem_iUnion] at hz'
  obtain ⟨s, hs, hzs⟩ := hz'
  have hd : ‖(s : EuclideanSpace ℝ (Fin dz)) - z‖ ≤ δ s s.2 := by
    rw [← dist_eq_norm, dist_comm]; exact le_of_lt (Metric.mem_ball.mp hzs)
  have hb := hδ s s.2 z (hKZ hz) hd
  have h1 := hWC N s z (ε / 4) hN.1 hN.2 hb
  have h2 := hCC s z (ε / 4) (hKZ s.2) (hKZ hz) hb
  have h3 := hNt s hs
  rw [Real.dist_eq]
  have := abs_sub_lt_iff.mp h3
  have := abs_sub_le_iff.mp h1
  have := abs_sub_le_iff.mp h2
  rw [abs_sub_lt_iff]
  constructor <;> linarith
