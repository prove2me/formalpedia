-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P42.eof_roof_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:01:06.52317+00:00
-- url     : https://prove2.me/submissions/922919c6-043a-45d0-ba65-58925ac76401

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P42
noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsBarycenter IsTraceClassChannel traceSize traceClosure
    productCoeff IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel IsPositive TraceOperatorLE RankAtMost SpectralPresentation spectralTruncation
    convexOperatorMixture traceSecond traceFirst channelTensorAction boundedConjugation)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasAverage HasFiniteSupport pureStates extendedEntropyNats
    extendedRelativeEntropyNats relativeIntegral finiteEnsembleCapacity stateChi)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable closedFormExpectation)

attribute [local instance] Classical.propDecidable Classical.decEq


open QAlgorithms.Papers.Independent.Next46.P42

theorem g62a_coef_le {I : Type} (X : Matrix I I ℂ) (i j : I) :
    ENNReal.ofReal ‖X i j‖ ≤ traceSize X := by
  unfold traceSize
  refine le_iInf fun e => ENNReal.ofReal_le_ofReal ?_
  rw [e.coefficients i j]
  have hb : ∀ n, ‖e.left n i * star (e.right n j)‖ ≤ ‖e.left n‖ * ‖e.right n‖ := by
    intro n
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _)
      (lp.norm_apply_le_norm two_ne_zero _ _) (norm_nonneg _) (norm_nonneg _)
  have hs : Summable (fun n => ‖e.left n i * star (e.right n j)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb e.summable
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb e.summable)

theorem g62a_traceSize_zero {I : Type} : traceSize (0 : Matrix I I ℂ) = 0 := by
  refine le_antisymm ?_ bot_le
  refine iInf_le_of_le (⟨fun _ => 0, fun _ => 0, by simp, by intro i j; simp⟩ :
    QAlgorithms.Papers.Independent.Dependency50.P33.NuclearExpansion (0 : Matrix I I ℂ)) ?_
  simp

theorem g62a_cont {I : Type} (i j : I) :
    Continuous (fun rho : State I => rho.coefficients i j) := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hB : IsOpen {t : State I | traceSize (t.coefficients - s.coefficients) <
      ENNReal.ofReal ε} :=
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨s, ε, hε, rfl⟩
  have hs : s ∈ {t : State I | traceSize (t.coefficients - s.coefficients) <
      ENNReal.ofReal ε} := by
    simp only [Set.mem_setOf_eq, sub_self, g62a_traceSize_zero]
    exact ENNReal.ofReal_pos.mpr hε
  filter_upwards [hB.mem_nhds hs] with t ht
  have h1 := (g62a_coef_le (t.coefficients - s.coefficients) i j).trans_lt ht
  rw [Matrix.sub_apply, ENNReal.ofReal_lt_ofReal_iff hε] at h1
  rwa [dist_eq_norm]

instance g62a_t1 {I : Type} : T1Space (State I) := by
  rw [t1Space_iff_exists_open]
  intro x y hxy
  have : ∃ i j, x.coefficients i j ≠ y.coefficients i j := by
    by_contra h
    push_neg at h
    apply hxy
    cases x; cases y
    congr
    funext i j
    exact h i j
  obtain ⟨i, j, hij⟩ := this
  refine ⟨(fun rho : State I => rho.coefficients i j) ⁻¹' {z | z ≠ y.coefficients i j},
    (isOpen_ne.preimage (g62a_cont i j)), hij, by simp⟩

theorem g62a_pure_bound {I : Type} (p : PureState I) (i j : I) :
    ‖p.val.coefficients i j‖ ≤ 1 := by
  obtain ⟨u, hu, h⟩ := p.property
  rw [h]
  simp only [QAlgorithms.Papers.Independent.Dependency50.P33.rankOne, norm_mul, norm_star]
  calc ‖u i‖ * ‖u j‖ ≤ ‖u‖ * ‖u‖ :=
        mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _)
          (lp.norm_apply_le_norm two_ne_zero _ _) (norm_nonneg _) (norm_nonneg _)
    _ = 1 := by rw [hu, one_mul]

variable {I J K L : Type}

theorem solution [Countable I] [Nonempty I] [Countable K] [Nonempty K]
    (rho : State (I × K)) :
    measureEof rho.coefficients ≤ countableEof rho.coefficients := by
  unfold countableEof measureEof entropyRoof
  refine le_iInf fun e => ?_
  obtain ⟨e, he⟩ := e
  let x : ℕ → State (I × K) := fun n => (e.state n).val
  let μ : Measure (State (I × K)) :=
    Measure.sum fun n => ((e.weight n : ℝ≥0∞)) • Measure.dirac (x n)
  have hw : (∑' n, (e.weight n : ℝ≥0∞)) = 1 := by
    rw [← ENNReal.coe_tsum (NNReal.summable_coe.mp e.summable)]
    have : (∑' n, e.weight n) = 1 := by
      apply NNReal.coe_injective; rw [NNReal.coe_tsum]; simpa using e.mass
    simp [this]
  haveI : IsProbabilityMeasure μ := ⟨by simp [μ, hw]⟩
  let P : GeneralizedEnsemble (I × K) := ⟨μ, inferInstance⟩
  have hlin : ∀ g : State (I × K) → ℝ≥0∞,
      ∫⁻ r, g r ∂μ = ∑' n, (e.weight n : ℝ≥0∞) * g (x n) := by
    intro g
    simp [μ, lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac]
    rfl
  have hbar : IsBarycenter μ State.coefficients rho.coefficients := by
    intro i j
    have hint : Integrable (fun r : State (I × K) => r.coefficients i j) μ := by
      refine ⟨(g62a_cont i j).aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral, hlin]
      calc ∑' n, (e.weight n : ℝ≥0∞) * ‖(x n).coefficients i j‖ₑ
          ≤ ∑' n, (e.weight n : ℝ≥0∞) * 1 := by
            refine ENNReal.tsum_le_tsum fun n => mul_le_mul' le_rfl ?_
            have := g62a_pure_bound (e.state n) i j
            rw [← ofReal_norm_eq_enorm]
            simpa using ENNReal.ofReal_le_ofReal this
        _ < ⊤ := by simp [hw]
    refine ⟨hint, ?_⟩
    rw [integral_sum_measure hint]
    simp only [integral_smul_measure, integral_dirac, ENNReal.coe_toReal]
    have hsum : Summable (fun n => ((e.weight n : ℝ) : ℂ) * (x n).coefficients i j) := by
      refine Summable.of_norm_bounded e.summable fun n => ?_
      rw [norm_mul]
      have := g62a_pure_bound (e.state n) i j
      have h0 : (0 : ℝ) ≤ (e.weight n : ℝ) := (e.weight n).2
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      nlinarith
    have ht : Tendsto (fun N => ∑ n ∈ Finset.range N,
        ((e.weight n : ℝ) : ℂ) * (x n).coefficients i j) atTop (𝓝 (rho.coefficients i j)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 : Tendsto (fun N => ENNReal.ofReal ‖(∑ n ∈ Finset.range N,
          ((e.weight n : ℝ) : ℂ) * (x n).coefficients i j) - rho.coefficients i j‖)
          atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
          (fun _ => bot_le) fun N => ?_
        refine le_trans (le_of_eq ?_) (g62a_coef_le _ i j)
        rw [norm_sub_rev]
        simp [Matrix.sub_apply, Matrix.sum_apply, x]
      have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      simpa [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _)] using h2
    rw [tendsto_nhds_unique ht hsum.hasSum.tendsto_sum_nat]
    congr 1
  refine (iInf_le _ ⟨P, hbar⟩).trans (le_of_eq ?_)
  exact hlin _
