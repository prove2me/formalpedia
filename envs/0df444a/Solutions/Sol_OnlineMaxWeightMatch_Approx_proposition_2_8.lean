-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.proposition_2_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T15:07:20.199367+00:00
-- url     : https://prove2.me/submissions/a61f542d-6d9d-47b7-b016-4c7e6e3a41e0

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated

open MeasureTheory ProbabilityTheory Filter Topology

open OnlineMaxWeightMatch.Approx in
theorem solution {Ω κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : κ → Ω → ℝ) (hNA : NegativelyAssociated X μ)
    {i j : κ} (hij : i ≠ j) (hi : MemLp (X i) 2 μ) (hj : MemLp (X j) 2 μ) :
    cov[X i, X j; μ] ≤ 0 := by
  -- truncation at level `N`
  let φ : ℕ → ℝ → ℝ := fun N y => max (-(N : ℝ)) (min (N : ℝ) y)
  have hφabs : ∀ N y, |φ N y| ≤ |y| := by
    intro N y
    have hN : (0 : ℝ) ≤ N := N.cast_nonneg
    have h1 := neg_abs_le y
    have h2 := le_abs_self y
    have h3 := abs_nonneg y
    rw [abs_le]
    constructor
    · exact le_max_of_le_right (le_min (by linarith) h1)
    · exact max_le (by linarith) (min_le_of_right_le h2)
  have hφbound : ∀ N y, |φ N y| ≤ N := by
    intro N y
    have hN : (0 : ℝ) ≤ N := N.cast_nonneg
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hφeq : ∀ y : ℝ, ∀ N : ℕ, |y| ≤ (N : ℝ) → φ N y = y := by
    intro y N hN
    have h1 := neg_abs_le y
    have h2 := le_abs_self y
    simp only [φ]
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  have hφlim : ∀ y, Tendsto (fun N => φ N y) atTop (𝓝 y) := by
    intro y
    apply tendsto_atTop_of_eventually_const (i₀ := ⌈|y|⌉₊)
    intro N hN
    exact hφeq y N ((Nat.le_ceil _).trans (by exact_mod_cast hN))
  have hφmono : ∀ N, Monotone (φ N) := by
    intro N a b hab
    exact max_le_max le_rfl (min_le_min le_rfl hab)
  have hφcont : ∀ N, Continuous (φ N) := by
    intro N
    exact continuous_const.max (continuous_const.min continuous_id)
  -- NA applied to the truncations
  have hdisj : Disjoint ({i} : Finset κ) {j} := Finset.disjoint_singleton.mpr hij
  have hNA' : ∀ N : ℕ, ∫ ω, φ N (X i ω) * φ N (X j ω) ∂μ ≤
      (∫ ω, φ N (X i ω) ∂μ) * ∫ ω, φ N (X j ω) ∂μ := by
    intro N
    have := hNA {i} {j} hdisj
      (fun y => φ N (y ⟨i, Finset.mem_singleton_self i⟩))
      (fun y => φ N (y ⟨j, Finset.mem_singleton_self j⟩))
      (fun y y' h => hφmono N (h _)) (fun y y' h => hφmono N (h _))
      ((hφcont N).measurable.comp (measurable_pi_apply _))
      ((hφcont N).measurable.comp (measurable_pi_apply _))
      ⟨N, fun y => hφbound N _⟩ ⟨N, fun y => hφbound N _⟩
    exact this
  -- dominated convergence
  have hiI : Integrable (X i) μ := hi.integrable (by norm_num)
  have hjI : Integrable (X j) μ := hj.integrable (by norm_num)
  have hijI : Integrable (X i * X j) μ := hi.integrable_mul hj
  have hmi : ∀ N, AEStronglyMeasurable (fun ω => φ N (X i ω)) μ := fun N =>
    (hφcont N).comp_aestronglyMeasurable hi.aestronglyMeasurable
  have hmj : ∀ N, AEStronglyMeasurable (fun ω => φ N (X j ω)) μ := fun N =>
    (hφcont N).comp_aestronglyMeasurable hj.aestronglyMeasurable
  have tI : Tendsto (fun N : ℕ => ∫ ω, φ N (X i ω) ∂μ) atTop (𝓝 (∫ ω, X i ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => |X i ω|) hmi hiI.abs
      (fun N => Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hφabs N _))
      (Eventually.of_forall (fun ω => hφlim _))
  have tJ : Tendsto (fun N : ℕ => ∫ ω, φ N (X j ω) ∂μ) atTop (𝓝 (∫ ω, X j ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => |X j ω|) hmj hjI.abs
      (fun N => Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hφabs N _))
      (Eventually.of_forall (fun ω => hφlim _))
  have tIJ : Tendsto (fun N : ℕ => ∫ ω, φ N (X i ω) * φ N (X j ω) ∂μ) atTop
      (𝓝 (∫ ω, X i ω * X j ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => |X i ω * X j ω|)
      (fun N => (hmi N).mul (hmj N)) hijI.abs
      (fun N => Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        exact mul_le_mul (hφabs N _) (hφabs N _) (abs_nonneg _) (abs_nonneg _)))
      (Eventually.of_forall (fun ω => (hφlim _).mul (hφlim _)))
  have hlim : ∫ ω, X i ω * X j ω ∂μ ≤ (∫ ω, X i ω ∂μ) * ∫ ω, X j ω ∂μ :=
    le_of_tendsto_of_tendsto' tIJ (tI.mul tJ) hNA'
  rw [covariance_eq_sub hi hj]
  have : μ[X i * X j] = ∫ ω, X i ω * X j ω ∂μ := rfl
  rw [this]
  linarith
