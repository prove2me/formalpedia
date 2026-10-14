-- Prove2me | solution 1 for StochApproxDyn.WeakAPT.block_average_tendsto_eq53
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:37:15.239449+00:00
-- url     : https://prove2.me/submissions/9b35117a-91cb-4efa-bcd1-d59d3ecc5b27

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_OccupationMeasure



namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

lemma occ_integral_eq {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (x : ℝ≥0 → M) (hx : Measurable x) (f : M → ℝ) (hf : Continuous f) (t : ℝ≥0) (ht : 0 < t) :
    ∫ y, f y ∂(occupationMeasure x t : Measure M) =
      (1 / (t:ℝ)) * ∫ s in (0:ℝ)..t, f (x s.toNNReal) := by
  rw [coe_occupationMeasure hx ht]
  rw [integral_map (φ := fun s : ℝ => x s.toNNReal) (hx.comp measurable_real_toNNReal).aemeasurable
    hf.aestronglyMeasurable]
  rw [ProbabilityTheory.cond, integral_smul_measure, intervalIntegral.integral_of_le (by positivity),
    integral_Icc_eq_integral_Ioc]
  simp [Real.volume_Icc]

lemma e53_alg (C T τ t Aτ At : ℝ) (hC : 0 ≤ C) (hτ : 0 < τ) (hτt : τ ≤ t) (htT : t - τ ≤ T)
    (hd : |Aτ - At| ≤ C * (t - τ)) (hAt : |At| ≤ C * t) :
    |(1 / τ) * Aτ - (1 / t) * At| ≤ 2 * C * T / τ := by
  have ht : 0 < t := lt_of_lt_of_le hτ hτt
  have key : (1 / τ) * Aτ - (1 / t) * At = (Aτ - At) / τ + At * (t - τ) / (τ * t) := by
    field_simp; ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_div, abs_mul, abs_of_pos hτ, abs_of_pos (mul_pos hτ ht),
    abs_of_nonneg (sub_nonneg.2 hτt)]
  have e1 : |Aτ - At| / τ ≤ C * T / τ := by
    apply div_le_div_of_nonneg_right _ hτ.le
    nlinarith
  have e2 : |At| * (t - τ) / (τ * t) ≤ C * T / τ := by
    rw [div_le_div_iff₀ (mul_pos hτ ht) hτ]
    have h1 : |At| * (t - τ) ≤ C * t * T :=
      mul_le_mul hAt htT (sub_nonneg.2 hτt) (by positivity)
    nlinarith
  linarith [e1, e2, show C * T / τ + C * T / τ = 2 * C * T / τ by ring]

theorem e53_core {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (x : ℝ≥0 → M) (hx : Measurable x) (T : ℝ≥0) (hT : 0 < T)
    (t : ℕ → ℝ≥0) (ht : Tendsto t atTop atTop) (μ : ProbabilityMeasure M)
    (hμ : Tendsto (fun j => occupationMeasure x (t j)) atTop (𝓝 μ))
    (f : M → ℝ) (hf : Continuous f) (hfb : ∃ C : ℝ, ∀ y, |f y| ≤ C) :
    Tendsto
      (fun j : ℕ => (1 / ((⌊t j / T⌋₊ : ℝ) * T)) *
        ∑ i ∈ Finset.range ⌊t j / T⌋₊, ∫ s in (i : ℝ) * T..((i : ℝ) + 1) * T, f (x s.toNNReal))
      atTop (𝓝 (∫ y, f y ∂(μ : Measure M))) := by
  obtain ⟨C, hC⟩ := hfb
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (x 0))
  have hgm : Measurable (fun s : ℝ => f (x s.toNNReal)) :=
    hf.measurable.comp (hx.comp measurable_real_toNNReal)
  have hgb : ∀ s : ℝ, ‖f (x s.toNNReal)‖ ≤ C := fun s => by
    rw [Real.norm_eq_abs]; exact hC _
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => f (x s.toNNReal)) volume a b :=
    fun a b => ⟨Measure.integrableOn_of_bounded (s := Set.Ioc a b) (by simp)
      hgm.aestronglyMeasurable (ae_of_all _ hgb), Measure.integrableOn_of_bounded
      (s := Set.Ioc b a) (by simp) hgm.aestronglyMeasurable (ae_of_all _ hgb)⟩
  set A : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, f (x s.toNNReal) with hAdef
  have hA : ∀ a b : ℝ, |A b - A a| ≤ C * |b - a| := by
    intro a b
    simp only [hAdef]
    rw [intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _), ← Real.norm_eq_abs]
    exact intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hgb s)
  -- weak convergence
  let F : BoundedContinuousFunction M ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * C) (fun a b => by
      rw [Real.dist_eq]
      have := abs_sub (f a) (f b)
      simp only [ContinuousMap.coe_mk]
      linarith [hC a, hC b])
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ) F
  have h1' : Tendsto (fun j => (1 / (t j : ℝ)) * A (t j)) atTop (𝓝 (∫ y, f y ∂(μ : Measure M))) := by
    refine h1.congr' ?_
    filter_upwards [ht.eventually_gt_atTop 0] with j hj
    exact occ_integral_eq x hx f hf (t j) hj
  -- the block sums
  have hT' : (0:ℝ) < T := hT
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, ∫ s in (i : ℝ) * T..((i : ℝ) + 1) * T,
      f (x s.toNNReal) = A (n * T) := by
    intro n
    have := intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => (i : ℝ) * T)
      (f := fun s : ℝ => f (x s.toNNReal)) (μ := volume) (n := n) (fun k _ => hii _ _)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul] at this
    rw [this]
  have htR : Tendsto (fun j => (t j : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 ht
  have hfl : ∀ j, (⌊t j / T⌋₊ : ℝ) * T ≤ t j ∧ (t j : ℝ) - T < (⌊t j / T⌋₊ : ℝ) * T := by
    intro j
    have a1 : (⌊t j / T⌋₊ : ℝ≥0) ≤ t j / T := Nat.floor_le zero_le
    have a2 : t j / T < (⌊t j / T⌋₊ : ℝ≥0) + 1 := Nat.lt_floor_add_one _
    rw [le_div_iff₀ hT] at a1
    rw [div_lt_iff₀ hT] at a2
    constructor
    · exact_mod_cast (NNReal.coe_le_coe.2 a1)
    · have := NNReal.coe_lt_coe.2 a2
      push_cast at this
      linarith
  have hτ : Tendsto (fun j => (⌊t j / T⌋₊ : ℝ) * T) atTop atTop := by
    have : Tendsto (fun j => (t j : ℝ) - T) atTop atTop := tendsto_atTop_add_const_right _ _ htR
    exact tendsto_atTop_mono (fun j => (hfl j).2.le) this
  have hdiff : Tendsto (fun j => (1 / ((⌊t j / T⌋₊ : ℝ) * T)) * A ((⌊t j / T⌋₊ : ℝ) * T)
      - (1 / (t j : ℝ)) * A (t j)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := 2 * C * (T:ℝ))).div_atTop hτ)
    filter_upwards [hτ.eventually_gt_atTop 0] with j hj
    rw [Real.norm_eq_abs]
    refine e53_alg C T _ _ _ _ hC0 hj (hfl j).1 (by linarith [(hfl j).2]) ?_ ?_
    · have := hA (t j) ((⌊t j / T⌋₊ : ℝ) * T)
      rwa [abs_sub_comm (((⌊t j / T⌋₊ : ℝ)) * T) _, abs_of_nonneg (sub_nonneg.2 (hfl j).1)] at this
    · have := hA 0 (t j)
      simpa [hAdef, abs_of_nonneg (NNReal.coe_nonneg (t j))] using this
  have := hdiff.add h1'
  simp only [sub_add_cancel, zero_add] at this
  refine this.congr' (Eventually.of_forall fun j => ?_)
  simp only [hsum]
end StochApproxDyn.WeakAPT

open StochApproxDyn.WeakAPT
open MeasureTheory Filter Topology
open scoped NNReal

theorem solution
    {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (x : ℝ≥0 → M) (hx : Measurable x) (T : ℝ≥0) (hT : 0 < T)
    (t : ℕ → ℝ≥0) (ht : Tendsto t atTop atTop) (μ : ProbabilityMeasure M)
    (hμ : Tendsto (fun j => occupationMeasure x (t j)) atTop (𝓝 μ))
    (f : M → ℝ) (hf : Continuous f) (hfb : ∃ C : ℝ, ∀ y, |f y| ≤ C) :
    Tendsto
      (fun j : ℕ => (1 / ((⌊t j / T⌋₊ : ℝ) * T)) *
        ∑ i ∈ Finset.range ⌊t j / T⌋₊, ∫ s in (i : ℝ) * T..((i : ℝ) + 1) * T, f (x s.toNNReal))
      atTop (𝓝 (∫ y, f y ∂(μ : Measure M))) := by
  exact e53_core x hx T hT t ht μ hμ f hf hfb
