-- Prove2me | solution 1 for ProbabilityTheory.levyBandPath_ae_eq_compensated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:04:42.819803+00:00
-- url     : https://prove2.me/submissions/5bf723a2-20ed-46e8-9549-3e6b9ec3e575

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    (fun ω => levyBandPath K X ν A t ω)
      =ᵐ[μ] compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 t).toLp _) := by
  have hfmeas : Measurable ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) :=
    measurable_snd.indicator (measurableSet_Ioc.prod hA)
  have hf1 : Integrable ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) (volume.prod ν) := by
    have hset : MeasurableSet (Set.Ioc 0 t ×ˢ A) := measurableSet_Ioc.prod hA
    have hfin : (volume.prod ν) (Set.Ioc 0 t ×ˢ A) < ⊤ :=
      volume_prod_Ioc_prod_lt_top (m := ν) (s := 0) (t := t) hAfin
    rw [integrable_indicator_iff hset]
    refine IntegrableOn.of_bound hfin measurable_snd.aestronglyMeasurable 1 ?_
    refine (ae_restrict_mem hset).mono fun p hp => ?_
    obtain ⟨h1, h2⟩ := hAsub hp.2
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨le_of_lt h1, le_of_lt h2⟩
  have hbandmeas : MeasurableSet (Set.Ioc 0 t ×ˢ A) := measurableSet_Ioc.prod hA
  -- the compensator drift equals the integral of the band test function
  have hint : (∫ p, ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) p ∂(volume.prod ν))
      = t * ∫ x in A, x ∂ν := by
    rw [integral_indicator hbandmeas,
      setIntegral_prod (fun z : ℝ × ℝ => z.2) ((integrable_indicator_iff hbandmeas).mp hf1)]
    dsimp only
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal ht, smul_eq_mul]
  -- the piece integrals sum to the integral over the whole band
  have hHasSum : HasSum (fun k => ∫ p in prmPiece (volume.prod ν) k,
        ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) p ∂(volume.prod ν))
      (∫ p, ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) p ∂(volume.prod ν)) := by
    have h := hasSum_integral_iUnion (μ := volume.prod ν)
      (f := (Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
      (fun k => measurableSet_prmPiece (m := volume.prod ν))
      (pairwise_disjoint_prmPiece (m := volume.prod ν))
      (by rw [iUnion_prmPiece]; exact hf1.integrableOn)
    rwa [iUnion_prmPiece, setIntegral_univ] at h
  refine EventuallyEq.trans ?_
    (compensatedPoissonIntegral_eq_sum hd hfmeas hf1 (memLp_two_bandFun hA hAsub hAfin 0 t)).symm
  have hfinite {R : Set (ℝ × ℝ)} (hR : MeasurableSet R)
      (hRfin : ((volume : Measure ℝ).prod ν) R < ⊤) :
      ∀ᵐ ω ∂μ, {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ R}.Finite := by
    have hg1 : Measurable (R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞))) :=
      measurable_const.indicator hR
    have hlintegral (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) (ω : Ω) :
        ∫⁻ x, g x ∂(poissonRandomMeasure K X ω)
          = ∑' k, ∑ n ∈ Finset.range (K k ω), g (X k n ω) := by
      rw [poissonRandomMeasure, lintegral_sum_measure]
      refine tsum_congr fun k => ?_
      rw [lintegral_sum_measure]
      have hterm : ∀ n, ∫⁻ x, g x ∂(if n < K k ω then Measure.dirac (X k n ω) else 0)
          = if n < K k ω then g (X k n ω) else 0 := fun n => by
        by_cases h : n < K k ω
        · rw [if_pos h, if_pos h, lintegral_dirac' _ hg]
        · rw [if_neg h, if_neg h, lintegral_zero_measure]
      simp_rw [hterm]
      rw [tsum_eq_sum (s := Finset.range (K k ω))
        fun n hn => if_neg (by simpa [Finset.mem_range] using hn)]
      exact Finset.sum_congr rfl fun n hn => if_pos (by simpa [Finset.mem_range] using hn)
    filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hR hRfin] with ω hω
    have hcount : ∑' k, ∑ n ∈ Finset.range (K k ω),
          R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)
        = poissonRandomMeasure K X ω R := by
      rw [← hlintegral _ hg1 ω, lintegral_indicator hR, setLIntegral_one]
    have hCfin : {k | (1 : ℝ≥0∞) ≤ ∑ n ∈ Finset.range (K k ω),
          R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)}.Finite :=
      ENNReal.finite_const_le_of_tsum_ne_top (by rw [hcount]; exact hω.ne) one_ne_zero
    refine hCfin.subset fun k hk => ?_
    simp only [Set.mem_setOf_eq] at hk ⊢
    obtain ⟨n, hn, hmem⟩ := hk
    calc (1 : ℝ≥0∞)
        = R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω) := by
            rw [Set.indicator_of_mem hmem]
      _ ≤ _ := Finset.single_le_sum
          (f := fun n => R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω))
          (fun _ _ => zero_le) hn
  have hfiniteSupport {R : Set (ℝ × ℝ)} (hR : MeasurableSet R)
      (hRfin : ((volume : Measure ℝ).prod ν) R < ⊤)
      {g : ℝ × ℝ → ℝ} (hg : ∀ p ∉ R, g p = 0) :
      ∀ᵐ ω ∂μ, {k | pieceSum K X g k ω ≠ 0}.Finite := by
    filter_upwards [hfinite hR hRfin] with ω hω
    refine hω.subset fun k hk => ?_
    simp only [Set.mem_setOf_eq] at hk ⊢
    have hk' : (∑ n ∈ Finset.range (K k ω), g (X k n ω)) ≠ 0 := hk
    obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk'
    refine ⟨n, hn, ?_⟩
    by_contra hnm
    exact hterm (hg _ hnm)
  filter_upwards [hfiniteSupport hbandmeas
    (volume_prod_Ioc_prod_lt_top (m := ν) (s := 0) (t := t) hAfin)
    (fun p hp => Set.indicator_of_notMem hp _)] with ω hfinsupp
  have hsummable_piece : Summable (fun k =>
      pieceSum K X ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) k ω) :=
    summable_of_ne_finset_zero (s := hfinsupp.toFinset) fun k hk => by
      by_contra hne
      exact hk (hfinsupp.mem_toFinset.mpr hne)
  simp only [levyBandPath, bandJumpSum, compensatedPoissonSum, compensatedPieceSum]
  rw [hsummable_piece.tsum_sub hHasSum.summable, hHasSum.tsum_eq, hint]
