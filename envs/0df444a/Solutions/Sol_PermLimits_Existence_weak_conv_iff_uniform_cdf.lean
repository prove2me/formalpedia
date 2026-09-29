-- Prove2me | solution 1 for PermLimits.Existence.weak_conv_iff_uniform_cdf
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:34:55.458996+00:00
-- url     : https://prove2.me/submissions/b0ce8998-5112-419a-bff1-489bdb8b785c

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_LimitConvergence
open PermLimits.Shared

namespace PermLimits.Existence

open MeasureTheory Filter unitInterval Topology

open scoped symmDiff

lemma aux_wcu_measSet (x y : I) : MeasurableSet (Set.Iic x ×ˢ Set.Iic y) :=
  measurableSet_Iic.prod measurableSet_Iic

lemma aux_wcu_lip1 (ν : Measure (I × I)) [IsFiniteMeasure ν] (hX : ν.map Prod.fst = volume)
    (x x' y : I) : |jointCDF ν x y - jointCDF ν x' y| ≤ dist x x' := by
  unfold jointCDF
  refine (abs_measureReal_sub_le_measureReal_symmDiff (aux_wcu_measSet _ _).nullMeasurableSet
    (aux_wcu_measSet _ _).nullMeasurableSet).trans ?_
  have hsub : (Set.Iic x ×ˢ Set.Iic y) ∆ (Set.Iic x' ×ˢ Set.Iic y) ⊆
      Prod.fst ⁻¹' (Set.uIoc x x') := by
    rintro ⟨a, b⟩ hp
    simp only [Set.mem_symmDiff, Set.mem_prod, Set.mem_Iic, not_and, not_le] at hp
    simp only [Set.mem_preimage, Set.mem_uIoc]
    rcases hp with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · right; exact ⟨lt_of_not_ge fun h => (h3 h).not_ge h2, h1⟩
    · left; exact ⟨lt_of_not_ge fun h => (h3 h).not_ge h2, h1⟩
  calc ν.real _ ≤ ν.real (Prod.fst ⁻¹' (Set.uIoc x x')) := measureReal_mono hsub
    _ = (ν.map Prod.fst).real (Set.uIoc x x') := by
        rw [map_measureReal_apply measurable_fst measurableSet_uIoc]
    _ = dist x x' := by
        rw [hX, measureReal_def, volume_uIoc, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
          dist_comm]

lemma aux_wcu_lip2 (ν : Measure (I × I)) [IsFiniteMeasure ν] (hY : ν.map Prod.snd = volume)
    (x y y' : I) : |jointCDF ν x y - jointCDF ν x y'| ≤ dist y y' := by
  unfold jointCDF
  refine (abs_measureReal_sub_le_measureReal_symmDiff (aux_wcu_measSet _ _).nullMeasurableSet
    (aux_wcu_measSet _ _).nullMeasurableSet).trans ?_
  have hsub : (Set.Iic x ×ˢ Set.Iic y) ∆ (Set.Iic x ×ˢ Set.Iic y') ⊆
      Prod.snd ⁻¹' (Set.uIoc y y') := by
    rintro ⟨a, b⟩ hp
    simp only [Set.mem_symmDiff, Set.mem_prod, Set.mem_Iic, not_and, not_le] at hp
    simp only [Set.mem_preimage, Set.mem_uIoc]
    rcases hp with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · right; exact ⟨h3 h1, h2⟩
    · left; exact ⟨h3 h1, h2⟩
  calc ν.real _ ≤ ν.real (Prod.snd ⁻¹' (Set.uIoc y y')) := measureReal_mono hsub
    _ = (ν.map Prod.snd).real (Set.uIoc y y') := by
        rw [map_measureReal_apply measurable_snd measurableSet_uIoc]
    _ = dist y y' := by
        rw [hY, measureReal_def, volume_uIoc, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
          dist_comm]

lemma aux_wcu_lipschitz (ν : Measure (I × I)) [IsFiniteMeasure ν]
    (hX : ν.map Prod.fst = volume) (hY : ν.map Prod.snd = volume) :
    LipschitzWith 2 (fun p : I × I => jointCDF ν p.1 p.2) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.dist_eq]
  have h1 := aux_wcu_lip1 ν hX p.1 q.1 p.2
  have h2 := aux_wcu_lip2 ν hY q.1 p.2 q.2
  have hp1 : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hp2 : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h3 := abs_sub_le (jointCDF ν p.1 p.2) (jointCDF ν q.1 p.2) (jointCDF ν q.1 q.2)
  push_cast
  linarith

/-- Bundle a probability measure. -/
noncomputable def aux_wcu_PM (ν : Measure (I × I)) (h : IsProbabilityMeasure ν) :
    ProbabilityMeasure (I × I) := ⟨ν, h⟩

@[simp] lemma aux_wcu_PM_coe (ν : Measure (I × I)) (h : IsProbabilityMeasure ν) :
    (aux_wcu_PM ν h : Measure (I × I)) = ν := rfl

lemma aux_wcu_toPM (μs : ℕ → Measure (I × I)) (μ : Measure (I × I))
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) [IsProbabilityMeasure μ]
    (h : WeakConvMeasures μs μ) :
    Tendsto (fun n => aux_wcu_PM (μs n) (hμs n)) atTop
      (𝓝 (aux_wcu_PM μ inferInstance)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  exact h f.toContinuousMap

lemma aux_wcu_marg (μs : ℕ → Measure (I × I)) (μ : Measure (I × I))
    [IsProbabilityMeasure μ]
    (h : WeakConvMeasures μs μ) (π : I × I → I) (hπ : Continuous π)
    (hmarg : ∀ n, (μs n).map π = volume) : μ.map π = volume := by
  have hm : Measurable π := hπ.measurable
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  have h1 := h ((g.toContinuousMap).comp ⟨π, hπ⟩)
  have h2 : ∀ n, ∫ p, (g.toContinuousMap.comp ⟨π, hπ⟩) p ∂(μs n) = ∫ x, g x ∂volume := by
    intro n
    rw [← hmarg n, integral_map hm.aemeasurable g.continuous.aestronglyMeasurable]
    rfl
  simp_rw [h2] at h1
  rw [integral_map hm.aemeasurable g.continuous.aestronglyMeasurable]
  exact tendsto_nhds_unique h1 tendsto_const_nhds

lemma aux_wcu_frontier (μ : Measure (I × I)) (hX : μ.map Prod.fst = volume)
    (hY : μ.map Prod.snd = volume) (x y : I) :
    μ (frontier (Set.Iic x ×ˢ Set.Iic y)) = 0 := by
  have hsub : frontier (Set.Iic x ×ˢ Set.Iic y) ⊆ Prod.fst ⁻¹' {x} ∪ Prod.snd ⁻¹' {y} := by
    rw [frontier_prod_eq]
    have hx : frontier (Set.Iic x) ⊆ {x} := frontier_Iic_subset x
    have hy : frontier (Set.Iic y) ⊆ {y} := frontier_Iic_subset y
    rintro ⟨a, b⟩ (⟨_, hb⟩ | ⟨ha, _⟩)
    · right; exact hy hb
    · left; exact hx ha
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [← Measure.map_apply measurable_fst (measurableSet_singleton x), hX]; simp
  · rw [← Measure.map_apply measurable_snd (measurableSet_singleton y), hY]; simp

lemma aux_wcu_pointwise (μs : ℕ → Measure (I × I)) (μ : Measure (I × I))
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) [IsProbabilityMeasure μ]
    (hX : ∀ n, (μs n).map Prod.fst = volume) (hY : ∀ n, (μs n).map Prod.snd = volume)
    (h : WeakConvMeasures μs μ) (x y : I) :
    Tendsto (fun n => jointCDF (μs n) x y) atTop (𝓝 (jointCDF μ x y)) := by
  have hX' := aux_wcu_marg μs μ h Prod.fst continuous_fst hX
  have hY' := aux_wcu_marg μs μ h Prod.snd continuous_snd hY
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (aux_wcu_toPM μs μ hμs h) (E := Set.Iic x ×ˢ Set.Iic y) (aux_wcu_frontier μ hX' hY' x y)
  unfold jointCDF
  simp only [measureReal_def]
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp key

lemma aux_wcu_ext (ν μ : Measure (I × I)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (h : ∀ x y : I, jointCDF ν x y = jointCDF μ x y) : ν = μ := by
  have hspan : IsCountablySpanning (Set.range (Set.Iic : I → Set I)) :=
    ⟨fun _ => Set.Iic 1, fun _ => ⟨1, rfl⟩, by
      ext z; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
      exact ⟨0, unitInterval.le_one z⟩⟩
  have hgenI : MeasurableSpace.generateFrom (Set.range (Set.Iic : I → Set I)) =
      (inferInstance : MeasurableSpace I) :=
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic I)).symm
  have hgen : (inferInstance : MeasurableSpace (I × I)) =
      MeasurableSpace.generateFrom
        (Set.image2 (· ×ˢ ·) (Set.range (Set.Iic : I → Set I)) (Set.range Set.Iic)) :=
    (generateFrom_eq_prod hgenI hgenI hspan hspan).symm
  refine ext_of_generate_finite _ hgen (isPiSystem_Iic.prod isPiSystem_Iic) ?_ ?_
  · rintro s ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, rfl⟩
    have := h x y
    unfold jointCDF at this
    rw [measureReal_def, measureReal_def] at this
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp this
  · simp [measure_univ]

end PermLimits.Existence

open PermLimits.Existence
open MeasureTheory Filter unitInterval Topology

theorem solution (μs : ℕ → Measure (I × I)) (μ : Measure (I × I))
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) [IsProbabilityMeasure μ]
    (hX : ∀ n, (μs n).map Prod.fst = volume) (hY : ∀ n, (μs n).map Prod.snd = volume) :
    WeakConvMeasures μs μ ↔
      TendstoUniformly (fun n (p : I × I) => jointCDF (μs n) p.1 p.2)
        (fun p : I × I => jointCDF μ p.1 p.2) atTop := by
  constructor
  · intro h
    have hpt := aux_wcu_pointwise μs μ hμs hX hY h
    have heq : Equicontinuous (fun n (p : I × I) => jointCDF (μs n) p.1 p.2) :=
      (LipschitzWith.uniformEquicontinuous _ 2 (fun n => by
        have := hμs n
        exact aux_wcu_lipschitz (μs n) (hX n) (hY n))).equicontinuous
    have := (heq.tendsto_uniformFun_iff_pi atTop _).mpr
      (tendsto_pi_nhds.mpr fun p => hpt p.1 p.2)
    exact UniformFun.tendsto_iff_tendstoUniformly.mp this
  · intro hU f
    have hpt : ∀ p : I × I, Tendsto (fun n => jointCDF (μs n) p.1 p.2) atTop
        (𝓝 (jointCDF μ p.1 p.2)) := fun p => hU.tendsto_at p
    apply tendsto_of_subseq_tendsto
    intro ns hns
    let P : ℕ → ProbabilityMeasure (I × I) := fun k => aux_wcu_PM (μs (ns k)) (hμs _)
    obtain ⟨ν, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq P
    have hweak : WeakConvMeasures (fun k => μs (ns (φ k))) (ν : Measure (I × I)) := by
      intro g
      have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim)
        (BoundedContinuousFunction.mkOfCompact g)
      simpa [P] using this
    have hpt' := aux_wcu_pointwise (fun k => μs (ns (φ k))) ν (fun k => hμs _)
      (fun k => hX _) (fun k => hY _) hweak
    have hsubseq : Tendsto (fun k => ns (φ k)) atTop atTop := hns.comp hφ.tendsto_atTop
    have hcdf : ∀ x y : I, jointCDF (ν : Measure (I × I)) x y = jointCDF μ x y := by
      intro x y
      exact tendsto_nhds_unique (hpt' x y) ((hpt (x, y)).comp hsubseq)
    have hνμ : (ν : Measure (I × I)) = μ := aux_wcu_ext _ _ hcdf
    refine ⟨φ, ?_⟩
    have := hweak f
    rw [hνμ] at this
    exact this
