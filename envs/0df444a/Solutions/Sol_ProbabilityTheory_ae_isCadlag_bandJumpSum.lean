-- Prove2me | solution 1 for ProbabilityTheory.ae_isCadlag_bandJumpSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:58:19.606205+00:00
-- url     : https://prove2.me/submissions/447d3bac-cf15-4804-92f3-246108282285

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
    (hA : MeasurableSet A) (hAfin : ν A < ⊤) :
    ∀ᵐ ω ∂μ, IsCadlag (fun t : ℝ => bandJumpSum K X A t ω) := by
  have hfinset :
      ∀ {ι : Type} (s : Finset ι) {f : ι → ℝ → ℝ},
        (∀ i ∈ s, IsCadlag (f i)) →
          IsCadlag (fun t => ∑ i ∈ s, f i t) := by
    classical
    intro ι s f h t
    refine ⟨tendsto_finsetSum s (fun i hi => (h i hi t).1), ?_⟩
    choose! l hl using fun i (hi : i ∈ s) => (h i hi t).2
    exact ⟨∑ i ∈ s, l i, tendsto_finsetSum s (fun i hi => hl i hi)⟩
  have hstep : ∀ {c y : ℝ}, IsCadlag (fun t : ℝ => if c ≤ t then y else 0) := by
    intro c y t
    constructor
    · rcases lt_or_ge t c with ht | ht
      · have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Ici t] t] fun _ => (0 : ℝ) := by
          filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs
          simp only [if_neg (not_le.mpr (Set.mem_Iio.mp hs))]
        refine continuousWithinAt_const.congr_of_eventuallyEq heq ?_
        simp only [if_neg (not_le.mpr ht)]
      · have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Ici t] t] fun _ => y := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          simp only [if_pos (le_trans ht hs)]
        refine continuousWithinAt_const.congr_of_eventuallyEq heq ?_
        simp only [if_pos ht]
    · rcases le_or_gt t c with ht | ht
      · refine ⟨0, ?_⟩
        have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Iio t] t] fun _ => (0 : ℝ) := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          simp only [if_neg (not_le.mpr (lt_of_lt_of_le hs ht))]
        exact tendsto_const_nhds.congr' heq.symm
      · refine ⟨y, ?_⟩
        have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Iio t] t] fun _ => y := by
          filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with s hs
          simp only [if_pos (le_of_lt (Set.mem_Ioi.mp hs))]
        exact tendsto_const_nhds.congr' heq.symm
  have hcongr : ∀ {f g : ℝ → ℝ} {t : ℝ},
      IsCadlagAt f t → f =ᶠ[𝓝 t] g → IsCadlagAt g t := by
    intro f g t hf h
    obtain ⟨hc, l, hl⟩ := hf
    refine ⟨?_, l, ?_⟩
    · exact hc.congr_of_eventuallyEq (h.filter_mono nhdsWithin_le_nhds).symm h.eq_of_nhds.symm
    · exact hl.congr' (h.filter_mono nhdsWithin_le_nhds)
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
  have hwin : ∀ T : ℕ, ∀ᵐ ω ∂μ,
      {k | ∃ n ∈ Finset.range (K k ω),
        X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ A}.Finite := fun T =>
    hfinite (measurableSet_Ioc.prod hA)
      (volume_prod_Ioc_prod_lt_top (m := ν) (s := 0) (t := (T : ℝ)) hAfin)
  filter_upwards [ae_all_iff.mpr hwin] with ω hω
  intro t
  obtain ⟨T, hT⟩ := exists_nat_gt t
  let S : Finset ℕ := (hω T).toFinset
  let F : ℝ → ℝ := fun u =>
    ∑ k ∈ S, ∑ n ∈ Finset.range (K k ω),
      (if (X k n ω).1 ≤ u then
        ({p : ℝ × ℝ | 0 < p.1 ∧ p.2 ∈ A}).indicator
          (fun p : ℝ × ℝ => p.2) (X k n ω) else 0)
  have hcadF : IsCadlag F := by
    dsimp only [F]
    exact hfinset _ fun k _ =>
      hfinset _ fun n _ => hstep
  have hEq : Set.EqOn (fun u : ℝ => bandJumpSum K X A u ω) F (Set.Iio (T : ℝ)) := by
    intro u hu
    simp only [Set.mem_Iio] at hu
    have huT : u ≤ (T : ℝ) := le_of_lt hu
    have hvanish : ∀ k ∉ S,
        pieceSum K X ((Set.Ioc 0 u ×ˢ A).indicator fun p : ℝ × ℝ => p.2) k ω = 0 := by
      intro k hk
      simp only [pieceSum]
      refine Finset.sum_eq_zero fun n hn => ?_
      refine Set.indicator_of_notMem ?_ _
      intro hmem
      exact hk ((hω T).mem_toFinset.mpr ⟨n, hn, Set.mem_prod.mpr
        ⟨Set.Ioc_subset_Ioc le_rfl huT (Set.mem_prod.mp hmem).1,
          (Set.mem_prod.mp hmem).2⟩⟩)
    simp only [bandJumpSum, F]
    rw [tsum_eq_sum hvanish]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [pieceSum]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hut : (X k n ω).1 ≤ u
    · rw [if_pos hut]
      rcases em (X k n ω ∈ Set.Ioc 0 u ×ˢ A) with hm | hm
      · rw [Set.indicator_of_mem hm,
          Set.indicator_of_mem
            (show X k n ω ∈ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 ∈ A} from
              ⟨(Set.mem_Ioc.mp (Set.mem_prod.mp hm).1).1,
                (Set.mem_prod.mp hm).2⟩)]
      · rw [Set.indicator_of_notMem hm,
          Set.indicator_of_notMem
            (show X k n ω ∉ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 ∈ A} from
              fun hc => hm (Set.mem_prod.mpr
                ⟨Set.mem_Ioc.mpr ⟨hc.1, hut⟩, hc.2⟩))]
    · rw [if_neg hut,
        Set.indicator_of_notMem
          (fun hmem => hut (Set.mem_Ioc.mp (Set.mem_prod.mp hmem).1).2)]
  refine hcongr (hcadF t) ?_
  filter_upwards [Iio_mem_nhds hT] with u hu
  exact (hEq hu).symm