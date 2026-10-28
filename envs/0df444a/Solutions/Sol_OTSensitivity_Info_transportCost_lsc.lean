-- Prove2me | solution 1 for OTSensitivity.Info.transportCost_lsc
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:29:55.377985+00:00
-- url     : https://prove2.me/submissions/723ccebb-4f24-4f85-9db1-6ca4db158143

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

/-- Truncated cost `min (k y y') M` as a bounded continuous `ℝ≥0`-valued function. -/
noncomputable def OTILsc_trunc {𝓨 : Type*} [TopologicalSpace 𝓨] (k : 𝓨 → 𝓨 → ℝ≥0∞)
    (hk : Continuous (Function.uncurry k)) (M : ℕ) : (𝓨 × 𝓨) →ᵇ NNReal :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun w => (min (k w.1 w.2) (M : ℝ≥0∞)).toNNReal, by
      have h1 : Continuous fun w : 𝓨 × 𝓨 => min (k w.1 w.2) (M : ℝ≥0∞) :=
        Continuous.min hk continuous_const
      refine ENNReal.continuousOn_toNNReal.comp_continuous h1 (fun w => ?_)
      exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top M) (min_le_right _ _)⟩
    M (by
      intro x y
      have hx : (min (k x.1 x.2) (M : ℝ≥0∞)).toNNReal ≤ (M : NNReal) := by
        have := ENNReal.toNNReal_mono (ENNReal.natCast_ne_top M) (min_le_right (k x.1 x.2) _)
        simpa using this
      have hy : (min (k y.1 y.2) (M : ℝ≥0∞)).toNNReal ≤ (M : NNReal) := by
        have := ENNReal.toNNReal_mono (ENNReal.natCast_ne_top M) (min_le_right (k y.1 y.2) _)
        simpa using this
      simp only [ContinuousMap.coe_mk]
      rw [NNReal.dist_eq]
      have hx' : ((min (k x.1 x.2) (M : ℝ≥0∞)).toNNReal : ℝ) ≤ M := by exact_mod_cast hx
      have hy' : ((min (k y.1 y.2) (M : ℝ≥0∞)).toNNReal : ℝ) ≤ M := by exact_mod_cast hy
      have hx0 := ((min (k x.1 x.2) (M : ℝ≥0∞)).toNNReal).2
      have hy0 := ((min (k y.1 y.2) (M : ℝ≥0∞)).toNNReal).2
      rw [abs_le]; constructor <;> linarith)

lemma OTILsc_trunc_coe {𝓨 : Type*} [TopologicalSpace 𝓨] (k : 𝓨 → 𝓨 → ℝ≥0∞)
    (hk : Continuous (Function.uncurry k)) (M : ℕ) (w : 𝓨 × 𝓨) :
    ((OTILsc_trunc k hk M w : NNReal) : ℝ≥0∞) = min (k w.1 w.2) (M : ℝ≥0∞) := by
  simp only [OTILsc_trunc, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
  exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top M) (min_le_right _ _))

theorem solution {𝓨 : Type*}
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (ν : Measure 𝓨) [IsProbabilityMeasure ν]
    (νs : ℕ → Measure 𝓨) (hνs : ∀ n, IsProbabilityMeasure (νs n))
    (ν' : Measure 𝓨) [IsProbabilityMeasure ν']
    (hconv : ∀ φ : 𝓨 →ᵇ ℝ, Tendsto (fun n => ∫ y, φ y ∂(νs n)) atTop (𝓝 (∫ y, φ y ∂ν'))) :
    RWPI.SqrtLasso.transportCost k ν ν'
      ≤ liminf (fun n => RWPI.SqrtLasso.transportCost k ν (νs n)) atTop := by
  classical
  let := TopologicalSpace.upgradeIsCompletelyMetrizable 𝓨
  let Ps : ℕ → ProbabilityMeasure 𝓨 := fun n => ⟨νs n, hνs n⟩
  let P' : ProbabilityMeasure 𝓨 := ⟨ν', inferInstance⟩
  let νP : ProbabilityMeasure 𝓨 := ⟨ν, inferInstance⟩
  have hPs : Tendsto Ps atTop (𝓝 P') := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]; exact hconv
  have hkc : Continuous (Function.uncurry k) := hk.1
  have hkm : Measurable (Function.uncurry k) := hkc.measurable
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  have hfreq := frequently_lt_of_liminf_lt (by isBoundedDefault) hc
  obtain ⟨φ, hφmono, hφ⟩ := extraction_of_frequently_atTop hfreq
  have hex : ∀ j, ∃ π : Measure (𝓨 × 𝓨),
      (IsProbabilityMeasure π ∧ π.map Prod.fst = ν ∧ π.map Prod.snd = νs (φ j)) ∧
        ∫⁻ w, k w.1 w.2 ∂π < c := by
    intro j
    have := hφ j
    unfold RWPI.SqrtLasso.transportCost at this
    rw [iInf_lt_iff] at this
    obtain ⟨π, hπ⟩ := this
    rw [iInf_lt_iff] at hπ
    obtain ⟨h, hh⟩ := hπ
    exact ⟨π, h, hh⟩
  choose π hπ hcost using hex
  let πP : ℕ → ProbabilityMeasure (𝓨 × 𝓨) := fun j => ⟨π j, (hπ j).1⟩
  let S : Set (ProbabilityMeasure (𝓨 × 𝓨)) := Set.range πP
  -- tightness
  have hcl : IsCompact (closure (Set.range Ps)) := by
    have hK := hPs.isCompact_insert_range
    exact hK.of_isClosed_subset isClosed_closure
      (closure_minimal (Set.subset_insert _ _) hK.isClosed)
  have hTs : IsTightMeasureSet {((μ : ProbabilityMeasure 𝓨) : Measure 𝓨) | μ ∈ Set.range Ps} :=
    isTightMeasureSet_of_isCompact_closure hcl
  have hT : IsTightMeasureSet {((μ : ProbabilityMeasure (𝓨 × 𝓨)) : Measure (𝓨 × 𝓨)) | μ ∈ S} := by
    apply IsTightMeasureSet.prodMk
    · refine (isTightMeasureSet_singleton (μ := ν)).subset ?_
      rintro _ ⟨_, ⟨μ, ⟨j, rfl⟩, rfl⟩, rfl⟩
      exact (hπ j).2.1
    · refine hTs.subset ?_
      rintro _ ⟨_, ⟨μ, ⟨j, rfl⟩, rfl⟩, rfl⟩
      exact ⟨Ps (φ j), ⟨φ j, rfl⟩, (hπ j).2.2.symm⟩
  have hcomp : IsCompact (closure S) := isCompact_closure_of_isTightMeasureSet hT
  obtain ⟨πl, -, ψ, hψ, hlim⟩ := hcomp.tendsto_subseq (fun j => subset_closure ⟨j, rfl⟩)
  -- marginals of the limit
  have hfst : (πl : Measure (𝓨 × 𝓨)).map Prod.fst = ν := by
    have h1 := ((ProbabilityMeasure.continuous_map continuous_fst).tendsto πl).comp hlim
    have h2 : (fun j => ProbabilityMeasure.map ((πP ∘ ψ) j)
        continuous_fst.measurable.aemeasurable) = fun _ => νP := by
      funext j
      apply Subtype.ext
      simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map]
      exact (hπ (ψ j)).2.1
    have h3 : ProbabilityMeasure.map πl continuous_fst.measurable.aemeasurable =
        νP := by
      have h1' : Tendsto (fun _ : ℕ => νP) atTop
          (𝓝 (ProbabilityMeasure.map πl continuous_fst.measurable.aemeasurable)) := by
        rw [← h2]; exact h1
      exact tendsto_nhds_unique (X := ProbabilityMeasure 𝓨) h1' tendsto_const_nhds
    have := congrArg (fun μ : ProbabilityMeasure 𝓨 => (μ : Measure 𝓨)) h3
    simpa [νP, ProbabilityMeasure.toMeasure_map] using this
  have hsnd : (πl : Measure (𝓨 × 𝓨)).map Prod.snd = ν' := by
    have h1 := ((ProbabilityMeasure.continuous_map continuous_snd).tendsto πl).comp hlim
    have h2 : (fun j => ProbabilityMeasure.map ((πP ∘ ψ) j)
        continuous_snd.measurable.aemeasurable) = fun j => Ps (φ (ψ j)) := by
      funext j
      apply Subtype.ext
      simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map]
      exact (hπ (ψ j)).2.2
    have h4 : Tendsto (fun j => Ps (φ (ψ j))) atTop (𝓝 P') :=
      hPs.comp ((hφmono.comp hψ).tendsto_atTop)
    have h3 : ProbabilityMeasure.map πl continuous_snd.measurable.aemeasurable = P' := by
      have h1' : Tendsto (fun j => Ps (φ (ψ j))) atTop
          (𝓝 (ProbabilityMeasure.map πl continuous_snd.measurable.aemeasurable)) := by
        rw [← h2]; exact h1
      exact tendsto_nhds_unique h1' h4
    have := congrArg (fun μ : ProbabilityMeasure 𝓨 => (μ : Measure 𝓨)) h3
    simpa [P', ProbabilityMeasure.toMeasure_map] using this
  -- cost of the limit
  have htr : ∀ M : ℕ, ∫⁻ w, ((OTILsc_trunc k hkc M w : NNReal) : ℝ≥0∞) ∂(πl : Measure (𝓨 × 𝓨)) ≤ c := by
    intro M
    have h1 := (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 hlim) (OTILsc_trunc k hkc M)
    refine le_of_tendsto' h1 (fun j => ?_)
    simp only [Function.comp_apply]
    refine le_trans ?_ (hcost (ψ j)).le
    show ∫⁻ w, ((OTILsc_trunc k hkc M w : NNReal) : ℝ≥0∞) ∂(π (ψ j)) ≤ _
    refine lintegral_mono fun w => ?_
    rw [OTILsc_trunc_coe]
    exact min_le_left _ _
  have hcostl : ∫⁻ w, k w.1 w.2 ∂(πl : Measure (𝓨 × 𝓨)) ≤ c := by
    have hpt : ∀ w : 𝓨 × 𝓨, k w.1 w.2 = ⨆ M : ℕ, ((OTILsc_trunc k hkc M w : NNReal) : ℝ≥0∞) := by
      intro w
      simp_rw [OTILsc_trunc_coe]
      rw [← inf_iSup_eq]
      simp [ENNReal.iSup_natCast]
    simp_rw [hpt]
    rw [lintegral_iSup]
    · exact iSup_le htr
    · intro M
      exact (OTILsc_trunc k hkc M).continuous.measurable.coe_nnreal_ennreal
    · intro M N hMN w
      simp only [OTILsc_trunc_coe]
      exact min_le_min le_rfl (by exact_mod_cast hMN)
  unfold RWPI.SqrtLasso.transportCost
  exact (iInf₂_le (πl : Measure (𝓨 × 𝓨)) ⟨inferInstance, hfst, hsnd⟩).trans hcostl
