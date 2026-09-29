-- Prove2me | solution 1 for Statistics.cramer_rao_quadratic_le_variance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-21T23:58:45.22666+00:00
-- url     : https://prove2.me/submissions/b6494a16-268f-4111-85cc-ff48f085c10d

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Probability.Moments.Variance

open MeasureTheory
open scoped ENNReal NNReal

namespace StatCRAux

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cauchy–Schwarz for the Bochner integral of a product of two `L²` functions. -/
theorem sq_integral_mul_le_mul_integral_sq (μ : Measure Ω) (d g : Ω → ℝ)
    (hd : MemLp d 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, d ω * g ω ∂μ) ^ 2 ≤ (∫ ω, (d ω) ^ 2 ∂μ) * (∫ ω, (g ω) ^ 2 ∂μ) := by
  have hdg : Integrable (fun ω => d ω * g ω) μ := hd.integrable_mul hg
  have hd2 : Integrable (fun ω => (d ω) ^ 2) μ := hd.integrable_sq
  have hg2 : Integrable (fun ω => (g ω) ^ 2) μ := hg.integrable_sq
  set A := ∫ ω, (d ω) ^ 2 ∂μ with hA
  set B := ∫ ω, d ω * g ω ∂μ with hB
  set C := ∫ ω, (g ω) ^ 2 ∂μ with hC
  have key : ∀ t : ℝ, 0 ≤ C * (t * t) + (-2 * B) * t + A := by
    intro t
    have e : (fun ω => (d ω - t * g ω) ^ 2)
        = fun ω => (d ω) ^ 2 - (2 * t) * (d ω * g ω) + (t * t) * (g ω) ^ 2 := by
      funext ω; ring
    have hnn : 0 ≤ ∫ ω, (d ω - t * g ω) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have hA1 : Integrable (fun ω => (2 * t) * (d ω * g ω)) μ := hdg.const_mul _
    have hA2 : Integrable (fun ω => (t * t) * (g ω) ^ 2) μ := hg2.const_mul _
    have hA3 : Integrable (fun ω => (d ω) ^ 2 - (2 * t) * (d ω * g ω)) μ := hd2.sub hA1
    rw [e, integral_add hA3 hA2, integral_sub hd2 hA1, integral_const_mul,
      integral_const_mul] at hnn
    rw [← hA, ← hB, ← hC] at hnn
    linarith
  have hdisc := discrim_le_zero key
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- **Information inequality** (the analytic core of the Cramér–Rao bound).  If `g` is a
centred `L²` function (a *score*), then the squared correlation of an `L²` statistic `δ`
with `g` is bounded by the variance of `δ` times the second moment of `g`. -/
theorem information_inequality (μ : Measure Ω) [IsProbabilityMeasure μ] (δ g : Ω → ℝ)
    (hδ : MemLp δ 2 μ) (hg : MemLp g 2 μ) (hg0 : ∫ ω, g ω ∂μ = 0) :
    (∫ ω, δ ω * g ω ∂μ) ^ 2
      ≤ (∫ ω, (δ ω - ∫ ω', δ ω' ∂μ) ^ 2 ∂μ) * (∫ ω, (g ω) ^ 2 ∂μ) := by
  set m := ∫ ω', δ ω' ∂μ with hm
  have hd : MemLp (fun ω => δ ω - m) 2 μ := hδ.sub (memLp_const m)
  have h := sq_integral_mul_le_mul_integral_sq μ (fun ω => δ ω - m) g hd hg
  have he : ∫ ω, (δ ω - m) * g ω ∂μ = ∫ ω, δ ω * g ω ∂μ := by
    have e : (fun ω => (δ ω - m) * g ω) = fun ω => δ ω * g ω - m * g ω := by
      funext ω; ring
    have hi1 : Integrable (fun ω => δ ω * g ω) μ := hδ.integrable_mul hg
    have hi2 : Integrable (fun ω => m * g ω) μ := (hg.integrable one_le_two).const_mul m
    rw [e, integral_sub hi1 hi2, integral_const_mul, hg0]
    ring
  rwa [he] at h

/-- **Hammersley–Chapman–Robbins bound.**  If `L` is the density of an alternative
probability law with respect to `μ`, then the squared bias shift of an `L²` statistic `δ`
under the alternative is at most its variance times the χ²-divergence `∫ (L - 1)²`. -/
theorem hammersley_chapman_robbins (μ : Measure Ω) [IsProbabilityMeasure μ] (δ L : Ω → ℝ)
    (hδ : MemLp δ 2 μ) (hL : MemLp L 2 μ) (hL1 : ∫ ω, L ω ∂μ = 1) :
    (∫ ω, δ ω * L ω ∂μ - ∫ ω, δ ω ∂μ) ^ 2
      ≤ (∫ ω, (δ ω - ∫ ω', δ ω' ∂μ) ^ 2 ∂μ) * (∫ ω, (L ω - 1) ^ 2 ∂μ) := by
  have hg : MemLp (fun ω => L ω - 1) 2 μ := hL.sub (memLp_const 1)
  have hg0 : ∫ ω, (L ω - 1) ∂μ = 0 := by
    rw [integral_sub (hL.integrable one_le_two) (integrable_const 1), hL1]
    simp
  have h := information_inequality μ δ (fun ω => L ω - 1) hδ hg hg0
  have he : ∫ ω, δ ω * (L ω - 1) ∂μ = ∫ ω, δ ω * L ω ∂μ - ∫ ω, δ ω ∂μ := by
    have e : (fun ω => δ ω * (L ω - 1)) = fun ω => δ ω * L ω - δ ω := by
      funext ω; ring
    have hi1 : Integrable (fun ω => δ ω * L ω) μ := hδ.integrable_mul hL
    have hi2 : Integrable (fun ω => δ ω) μ := hδ.integrable one_le_two
    rw [e, integral_sub hi1 hi2]
  rwa [he] at h

/-- **Multiparameter (constrained) Cramér–Rao bound**, in the form that avoids inverting
the Fisher information matrix.  Let `g i` be centred `L²` scores with Gram (Fisher)
matrix `I i j = ∫ g i * g j`, and let `δ` be an `L²` statistic whose covariances with the
scores are `I.mulVec y` for some vector `y` — i.e. the gradient of the estimand lies in
the range of `I`, with `y` a solution of the normal equations.  Then the variance of `δ`
is at least the quadratic form `yᵀ I y`, which is `∇gᵀ I⁺ ∇g`, the constrained
Cramér–Rao bound. -/
theorem cramer_rao_quadratic_le_variance {ι : Type*} [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (δ : Ω → ℝ) (hδ : MemLp δ 2 μ)
    (g : ι → Ω → ℝ) (hg : ∀ i, MemLp (g i) 2 μ) (hg0 : ∀ i, ∫ ω, g i ω ∂μ = 0)
    (I : ι → ι → ℝ) (hI : ∀ i j, I i j = ∫ ω, g i ω * g j ω ∂μ)
    (y : ι → ℝ) (hy : ∀ i, ∫ ω, δ ω * g i ω ∂μ = ∑ j, I i j * y j) :
    ∑ i, ∑ j, y i * I i j * y j ≤ ∫ ω, (δ ω - ∫ ω', δ ω' ∂μ) ^ 2 ∂μ := by
  classical
  set Q := ∑ i, ∑ j, y i * I i j * y j with hQ
  set G : Ω → ℝ := fun ω => ∑ i, y i * g i ω with hG
  have hGmem : MemLp G 2 μ :=
    memLp_finsetSum (μ := μ) (p := 2) Finset.univ
      (f := fun i ω => y i * g i ω) fun i _ => (hg i).const_mul (y i)
  have hgint : ∀ i, Integrable (g i) μ := fun i => (hg i).integrable one_le_two
  -- the score `G` is centred
  have hG0 : ∫ ω, G ω ∂μ = 0 := by
    have := integral_finsetSum (μ := μ) (f := fun i ω => y i * g i ω) Finset.univ
      (fun i _ => (hgint i).const_mul (y i))
    rw [hG]
    rw [this]
    simp only [integral_const_mul, hg0, mul_zero, Finset.sum_const_zero]
  -- the covariance of `δ` with `G` is the quadratic form `Q`
  have hδG : ∫ ω, δ ω * G ω ∂μ = Q := by
    have e : (fun ω => δ ω * G ω) = fun ω => ∑ i, y i * (δ ω * g i ω) := by
      funext ω
      simp only [hG, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hint := integral_finsetSum (μ := μ) (f := fun i ω => y i * (δ ω * g i ω)) Finset.univ
      (fun i _ => (hδ.integrable_mul (hg i)).const_mul (y i))
    rw [e, hint]
    simp only [integral_const_mul, hy, hQ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the second moment of `G` is also `Q`
  have hGG : ∫ ω, (G ω) ^ 2 ∂μ = Q := by
    have e : (fun ω => (G ω) ^ 2)
        = fun ω => ∑ i, (∑ j, (y i * y j) * (g i ω * g j ω)) := by
      funext ω
      simp only [hG, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hinner : ∀ i : ι, Integrable (fun ω => ∑ j, (y i * y j) * (g i ω * g j ω)) μ := by
      intro i
      exact integrable_finsetSum (μ := μ) (f := fun j ω => (y i * y j) * (g i ω * g j ω))
        Finset.univ (fun j _ => ((hg i).integrable_mul (hg j)).const_mul (y i * y j))
    have hout := integral_finsetSum (μ := μ)
      (f := fun i ω => ∑ j, (y i * y j) * (g i ω * g j ω)) Finset.univ (fun i _ => hinner i)
    rw [e, hout, hQ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum (μ := μ) (f := fun j ω => (y i * y j) * (g i ω * g j ω))
      Finset.univ (fun j _ => ((hg i).integrable_mul (hg j)).const_mul (y i * y j))]
    exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul, hI]; ring
  have hV : 0 ≤ ∫ ω, (δ ω - ∫ ω', δ ω' ∂μ) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  by_cases hQ0 : Q ≤ 0
  · exact hQ0.trans hV
  · push_neg at hQ0
    have h := information_inequality μ δ G hδ hGmem hG0
    rw [hδG, hGG] at h
    have hmul : Q * Q ≤ (∫ ω, (δ ω - ∫ ω', δ ω' ∂μ) ^ 2 ∂μ) * Q := by
      calc Q * Q = Q ^ 2 := by ring
        _ ≤ _ := h
    exact le_of_mul_le_mul_right hmul hQ0

end StatCRAux


theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (δ : Ω → ℝ) (hδ : MemLp δ 2 μ)
    (g : ι → Ω → ℝ) (hg : ∀ i, MemLp (g i) 2 μ) (hg0 : ∀ i, ∫ ω, g i ω ∂μ = 0)
    (I : ι → ι → ℝ) (hI : ∀ i j, I i j = ∫ ω, g i ω * g j ω ∂μ)
    (y : ι → ℝ) (hy : ∀ i, ∫ ω, δ ω * g i ω ∂μ = ∑ j, I i j * y j) :
    ∑ i, ∑ j, y i * I i j * y j ≤ ∫ ω, (δ ω - ∫ ω', δ ω' ∂μ) ^ 2 ∂μ :=
  StatCRAux.cramer_rao_quadratic_le_variance μ δ hδ g hg hg0 I hI y hy
