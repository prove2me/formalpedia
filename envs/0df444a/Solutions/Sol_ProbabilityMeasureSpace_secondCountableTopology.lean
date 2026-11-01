-- Prove2me | solution 1 for ProbabilityMeasureSpace.secondCountableTopology
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T10:50:00.605489+00:00
-- url     : https://prove2.me/submissions/d5d3a3db-038a-4612-b5ba-df20b1172e4b

import Mathlib

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BoundedContinuousFunction

/-- Pushforwards along pointwise convergent measurable maps converge weakly. -/
private lemma tendsto_map_of_pointwise {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : ProbabilityMeasure X) {q : ℕ → X → X} {q0 : X → X}
    (hq : ∀ n, Measurable (q n)) (hq0 : Measurable q0)
    (h : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 (q0 x))) :
    Tendsto (fun n => μ.map (hq n).aemeasurable) atTop (𝓝 (μ.map hq0.aemeasurable)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [integral_map hq0.aemeasurable f.continuous.aestronglyMeasurable]
  have : ∀ n, ∫ ω, f ω ∂((μ : Measure X).map (q n)) = ∫ x, f (q n x) ∂(μ : Measure X) :=
    fun n => integral_map (hq n).aemeasurable f.continuous.aestronglyMeasurable
  simp_rw [this]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    (fun n => (f.continuous.measurable.comp (hq n)).aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ (fun x => f.norm_coe_le_norm _))
    (ae_of_all _ (fun x => (f.continuous.tendsto _).comp (h x)))

theorem solution {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    SecondCountableTopology (ProbabilityMeasure X) := by
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  letI : PseudoMetricSpace (ProbabilityMeasure X) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
  suffices SeparableSpace (ProbabilityMeasure X) by infer_instance
  rcases isEmpty_or_nonempty X with hX | hX
  · have : IsEmpty (ProbabilityMeasure X) := ⟨fun μ => by
      have h1 := measure_univ (μ := (μ : Measure X))
      rw [Set.univ_eq_empty_iff.mpr hX, measure_empty] at h1
      exact zero_ne_one h1⟩
    infer_instance
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq X
  have hex : ∀ n : ℕ, ∀ x, ∃ j, dist x (d j) < 1 / ((n : ℝ) + 1) :=
    fun n x => hd.exists_dist_lt x (by positivity)
  classical
  let k : ℕ → X → ℕ := fun n x => Nat.find (hex n x)
  have hk_meas : ∀ n, Measurable (k n) := fun n =>
    measurable_find _ (fun j => measurableSet_lt (measurable_id.dist measurable_const)
      measurable_const)
  have hk_spec : ∀ n x, dist x (d (k n x)) < 1 / ((n : ℝ) + 1) :=
    fun n x => Nat.find_spec (hex n x)
  let dN : (N : ℕ) → Fin (N + 1) → X := fun N i => d i.val
  have hdN : ∀ N, Continuous (dN N) := fun N => continuous_of_discreteTopology
  let A : Set (ProbabilityMeasure X) := ⋃ N : ℕ,
    Set.range (fun ν : ProbabilityMeasure (Fin (N + 1)) => ν.map (hdN N).measurable.aemeasurable)
  have hA : IsSeparable A := by
    refine IsSeparable.iUnion (fun N => ?_)
    letI : PseudoMetricSpace (ProbabilityMeasure (Fin (N + 1))) :=
      TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
    exact isSeparable_range (ProbabilityMeasure.continuous_map (hdN N))
  have hdense : Dense A := by
    intro μ
    let qn : ℕ → X → X := fun n x => d (k n x)
    have hqn : ∀ n, Measurable (qn n) := fun n => measurable_from_nat.comp (hk_meas n)
    have step : ∀ n, μ.map (hqn n).aemeasurable ∈ closure A := by
      intro n
      let idx : (N : ℕ) → X → Fin (N + 1) := fun N x => Fin.ofNat (N + 1) (k n x)
      have hidx : ∀ N, Measurable (idx N) := fun N =>
        show Measurable ((fun m : ℕ => Fin.ofNat (N + 1) m) ∘ k n) from
          measurable_from_nat.comp (hk_meas n)
      let qnN : ℕ → X → X := fun N x => dN N (idx N x)
      have hqnN : ∀ N, Measurable (qnN N) := fun N => (hdN N).measurable.comp (hidx N)
      have hmem : ∀ N, μ.map (hqnN N).aemeasurable ∈ A := by
        intro N
        refine Set.mem_iUnion.mpr ⟨N, μ.map (hidx N).aemeasurable, ?_⟩
        apply ProbabilityMeasure.toMeasure_injective
        simp only [ProbabilityMeasure.toMeasure_map]
        rw [Measure.map_map (hdN N).measurable (hidx N)]
        rfl
      have hlim : ∀ x, Tendsto (fun N => qnN N x) atTop (𝓝 (qn n x)) := by
        intro x
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop (k n x)] with N hN
        simp only [qnN, dN, idx, qn, Fin.val_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]
      exact mem_closure_of_tendsto (tendsto_map_of_pointwise μ hqnN (hqn n) hlim)
        (Eventually.of_forall hmem)
    have hid : Tendsto (fun n => μ.map (hqn n).aemeasurable) atTop
        (𝓝 (μ.map measurable_id.aemeasurable)) := by
      refine tendsto_map_of_pointwise μ hqn measurable_id (fun x => ?_)
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [dist_comm]
      exact (hk_spec n x).le
    have hμ : μ.map measurable_id.aemeasurable = μ :=
      ProbabilityMeasure.toMeasure_injective (by simp [ProbabilityMeasure.toMeasure_map, Measure.map_id])
    rw [hμ] at hid
    have := mem_closure_of_tendsto hid (Eventually.of_forall step)
    rwa [closure_closure] at this
  exact (hdense.isSeparable_iff).mp hA

