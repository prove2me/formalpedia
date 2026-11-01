-- Prove2me | solution 1 for ProbabilityMeasureSpace.standardBorelSpace
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T10:53:38.442992+00:00
-- url     : https://prove2.me/submissions/31ea41de-5fe7-4306-9f25-b89e37290770

import Mathlib

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

private lemma standardBorel_of_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [StandardBorelSpace α] (e : α ≃ᵐ β) : StandardBorelSpace β := by
  letI := upgradeStandardBorel α
  letI τ : TopologicalSpace β := TopologicalSpace.induced e.symm (inferInstance : TopologicalSpace α)
  haveI : PolishSpace β := e.symm.toEquiv.polishSpace_induced
  haveI : BorelSpace β := ⟨by
    show _ = @borel β (TopologicalSpace.induced e.symm _)
    rw [borel_comap, ← BorelSpace.measurable_eq]
    exact e.symm.measurableEmbedding.comap_eq.symm⟩
  exact ⟨⟨τ, inferInstance, inferInstance⟩⟩

private lemma isRatStieltjesPoint_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsRatStieltjesPoint (id : (ℚ → ℝ) → ℚ → ℝ) (fun q : ℚ => cdf μ q) where
  mono := fun a b h => monotone_cdf μ (by exact_mod_cast h)
  tendsto_atTop_one := (tendsto_cdf_atTop μ).comp (tendsto_ratCast_atTop_iff.2 tendsto_id)
  tendsto_atBot_zero := (tendsto_cdf_atBot μ).comp (tendsto_ratCast_atBot_iff.2 tendsto_id)
  iInf_rat_gt_eq := by
    intro t
    show ⨅ r : Ioi t, cdf μ ((r : ℚ) : ℝ) = cdf μ (t : ℝ)
    have := (cdf μ).iInf_rat_gt_eq t
    rw [← this]
    exact (Equiv.subtypeEquivRight (fun r => by simp)).iInf_congr (fun _ => rfl)

private lemma standardBorel_PM_real : StandardBorelSpace (ProbabilityMeasure ℝ) := by
  let S : Set (ℚ → ℝ) := {F | IsRatStieltjesPoint (id : (ℚ → ℝ) → ℚ → ℝ) F}
  have hS : MeasurableSet S := measurableSet_isRatStieltjesPoint measurable_id
  haveI : StandardBorelSpace S := hS.standardBorel
  let st : (ℚ → ℝ) → StieltjesFunction ℝ := stieltjesOfMeasurableRat id measurable_id
  let Φ : S → ProbabilityMeasure ℝ := fun F => ⟨(st F.1).measure, inferInstance⟩
  let Ψ : ProbabilityMeasure ℝ → S := fun μ =>
    ⟨fun q => cdf (μ : Measure ℝ) q, isRatStieltjesPoint_cdf μ⟩
  have hΦ : Measurable Φ :=
    ((measurable_measure_stieltjesOfMeasurableRat measurable_id).comp
      measurable_subtype_coe).subtype_mk
  have hΨ : Measurable Ψ := by
    refine Measurable.subtype_mk (measurable_pi_lambda _ fun q => ?_)
    simp_rw [cdf_eq_real, measureReal_def]
    exact ((Measure.measurable_coe measurableSet_Iic).comp
      measurable_subtype_coe).ennreal_toReal
  have hst : ∀ F : S, ∀ q : ℚ, st F.1 q = F.1 q := fun F q => by
    simp only [st]
    rw [stieltjesOfMeasurableRat_eq, toRatCDF_of_isRatStieltjesPoint F.2]
    rfl
  have h1 : ∀ F, Ψ (Φ F) = F := by
    intro F
    apply Subtype.ext
    funext q
    show cdf (st F.1).measure q = F.1 q
    rw [cdf_measure_stieltjesFunction _ (tendsto_stieltjesOfMeasurableRat_atBot _ _)
      (tendsto_stieltjesOfMeasurableRat_atTop _ _)]
    exact hst F q
  have h2 : ∀ μ, Φ (Ψ μ) = μ := by
    intro μ
    apply ProbabilityMeasure.toMeasure_injective
    show (st (Ψ μ).1).measure = μ
    have : st (Ψ μ).1 = cdf (μ : Measure ℝ) := by
      ext x
      rw [← (st (Ψ μ).1).iInf_rat_gt_eq x, ← (cdf (μ : Measure ℝ)).iInf_rat_gt_eq x]
      congr 1
      funext r
      exact hst (Ψ μ) r
    rw [this, measure_cdf]
  exact standardBorel_of_measurableEquiv
    { toFun := Φ, invFun := Ψ, left_inv := h1, right_inv := h2,
      measurable_toFun := hΦ, measurable_invFun := hΨ }

theorem solution {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] :
    StandardBorelSpace (ProbabilityMeasure X) := by
  haveI := standardBorel_PM_real
  rcases isEmpty_or_nonempty X with hX | hX
  · haveI : IsEmpty (ProbabilityMeasure X) := ⟨fun μ => by
      have h1 := measure_univ (μ := (μ : Measure X))
      rw [Set.univ_eq_empty_iff.mpr hX, measure_empty] at h1
      exact zero_ne_one h1⟩
    exact standardBorel_of_measurableEquiv (α := Empty)
      { toEquiv := Equiv.equivOfIsEmpty _ _,
        measurable_toFun := measurable_of_subsingleton_codomain _,
        measurable_invFun := measurable_of_subsingleton_codomain _ }
  let f := embeddingReal X
  have hf := measurableEmbedding_embeddingReal X
  obtain ⟨g, hg, hgf⟩ := hf.exists_measurable_extend measurable_id (fun _ => hX)
  let T : ProbabilityMeasure X → ProbabilityMeasure ℝ := fun μ => μ.map hf.measurable.aemeasurable
  let R : ProbabilityMeasure ℝ → ProbabilityMeasure X := fun ν => ν.map hg.aemeasurable
  have hT : Measurable T :=
    ((Measure.measurable_map _ hf.measurable).comp measurable_subtype_coe).subtype_mk
  have hR : Measurable R :=
    ((Measure.measurable_map _ hg).comp measurable_subtype_coe).subtype_mk
  have hRT : ∀ μ, R (T μ) = μ := by
    intro μ
    apply ProbabilityMeasure.toMeasure_injective
    show ((μ : Measure X).map f).map g = μ
    rw [Measure.map_map hg hf.measurable, hgf, Measure.map_id]
  let s : Set (ProbabilityMeasure ℝ) := {ν | (ν : Measure ℝ) (Set.range f)ᶜ = 0}
  have hs : MeasurableSet s :=
    ((Measure.measurable_coe hf.measurableSet_range.compl).comp measurable_subtype_coe)
      (measurableSet_singleton 0)
  have hTR : ∀ ν ∈ s, T (R ν) = ν := by
    intro ν hν
    apply ProbabilityMeasure.toMeasure_injective
    show ((ν : Measure ℝ).map g).map f = ν
    rw [Measure.map_map hf.measurable hg]
    conv_rhs => rw [← Measure.map_id (μ := (ν : Measure ℝ))]
    apply Measure.map_congr
    have : Set.range f ∈ ae (ν : Measure ℝ) := mem_ae_iff.2 hν
    filter_upwards [this] with y hy
    obtain ⟨x, rfl⟩ := hy
    show f (g (f x)) = f x
    rw [show g (f x) = x from congrFun hgf x]
  have hTs : ∀ μ, T μ ∈ s := by
    intro μ
    show ((μ : Measure X).map f) (Set.range f)ᶜ = 0
    rw [Measure.map_apply hf.measurable hf.measurableSet_range.compl]
    simp
  haveI : StandardBorelSpace s := hs.standardBorel
  exact standardBorel_of_measurableEquiv (α := s)
    { toFun := fun ν => R ν.1, invFun := fun μ => ⟨T μ, hTs μ⟩,
      left_inv := fun ν => Subtype.ext (hTR ν.1 ν.2), right_inv := hRT,
      measurable_toFun := hR.comp measurable_subtype_coe,
      measurable_invFun := hT.subtype_mk }
