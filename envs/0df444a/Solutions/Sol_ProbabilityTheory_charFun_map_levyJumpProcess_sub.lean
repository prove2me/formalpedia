-- Prove2me | solution 1 for ProbabilityTheory.charFun_map_levyJumpProcess_sub
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T04:03:13.36507+00:00
-- url     : https://prove2.me/submissions/53fdeff2-a9b2-41ab-b0db-29b86f3dbf73

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Theorems.Thm_ProbabilityTheory_iIndep_prmEvalSigma
import Theorems.Thm_ProbabilityTheory_increment_apply
import Theorems.Thm_ProbabilityTheory_levyCompensatedSmallJump_sub
import Theorems.Thm_ProbabilityTheory_measurable_lintegral_poissonRandomMeasure_prmEvalSigma
import Theorems.Thm_ProbabilityTheory_lintegral_poissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_charFun_map_bandJumpSum
import Theorems.Thm_ProbabilityTheory_charFun_map_smallJumpBandIntegral
import Theorems.Thm_ProbabilityTheory_integral_levyCompensatedIntegrand_eq_small_add_large
import Theorems.Thm_ProbabilityTheory_indep_prmEvalSigma
import Theorems.Thm_ProbabilityTheory_measurable_levyLargeJumpSum
open MeasureTheory ProbabilityTheory Filter Complex
open scoped ENNReal NNReal Topology
variable {Ω : Type} [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}
namespace ProbabilityTheory
private lemma local_ae_finite_pieces_mem [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    {R : Set (ℝ × ℝ)} (hR : MeasurableSet R)
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
private lemma local_ae_finite_support_pieceSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    {R : Set (ℝ × ℝ)} (hR : MeasurableSet R)
    (hRfin : ((volume : Measure ℝ).prod ν) R < ⊤)
    {g : ℝ × ℝ → ℝ} (hg : ∀ p ∉ R, g p = 0) :
    ∀ᵐ ω ∂μ, {k | pieceSum K X g k ω ≠ 0}.Finite := by
  filter_upwards [local_ae_finite_pieces_mem hd hR hRfin] with ω hω
  refine hω.subset fun k hk => ?_
  simp only [Set.mem_setOf_eq] at hk ⊢
  have hk' : (∑ n ∈ Finset.range (K k ω), g (X k n ω)) ≠ 0 := hk
  obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk'
  refine ⟨n, hn, ?_⟩
  by_contra hnm
  exact hterm (hg _ hnm)
private lemma local_bandSumAeEq {Ω : Type} [MeasurableSpace Ω] {ν : Measure ℝ} [SigmaFinite ν]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hν : IsLevyMeasure ν) {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) :
    (fun ω => levyLargeJumpSum K X t ω - levyLargeJumpSum K X s ω) =ᵐ[μ] fun ω =>
      ∑' k, pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω := by
  have hfin (u v : ℝ) :
      ∀ᵐ ω ∂μ, {k | pieceSum K X
          ((Set.Ioc u v ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω ≠ 0}.Finite := by
    have hbandfin : (volume.prod ν) (Set.Ioc u v ×ˢ {x : ℝ | 1 ≤ |x|}) < ⊤ :=
      volume_prod_Ioc_prod_lt_top (m := ν) (s := u) (t := v)
        (hν.measure_setOf_abs_ge_lt_top one_pos)
    exact local_ae_finite_support_pieceSum hd
      (measurableSet_Ioc.prod (measurableSet_le measurable_const continuous_abs.measurable))
      hbandfin (fun p hp => Set.indicator_of_notMem hp _)
  filter_upwards [hfin 0 s, hfin s t] with ω hω_s hω_st
  have hsplit : ∀ k,
      pieceSum K X ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω
        = pieceSum K X ((Set.Ioc 0 s ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω
          + pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω := by
    intro k
    have hdisj : Disjoint (Set.Ioc 0 s ×ˢ {x : ℝ | 1 ≤ |x|})
        (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) :=
      Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le (le_refl s)) _ _
    have hfun : ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2)
        = (Set.Ioc 0 s ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun p : ℝ × ℝ => p.2)
          + (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun p : ℝ × ℝ => p.2) := by
      rw [← Set.Ioc_union_Ioc_eq_Ioc h0 hst, Set.union_prod,
        Set.indicator_union_of_disjoint hdisj]
      rfl
    simp only [pieceSum, hfun, Pi.add_apply, Finset.sum_add_distrib]
  have hsum_s : Summable (fun k =>
      pieceSum K X ((Set.Ioc 0 s ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω) :=
    summable_of_ne_finset_zero (s := hω_s.toFinset) fun k hk => by
      by_contra hne; exact hk (hω_s.mem_toFinset.mpr hne)
  have hsum_st : Summable (fun k =>
      pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω) :=
    summable_of_ne_finset_zero (s := hω_st.toFinset) fun k hk => by
      by_contra hne; exact hk (hω_st.mem_toFinset.mpr hne)
  simp only [levyLargeJumpSum]
  rw [tsum_congr hsplit, hsum_s.tsum_add hsum_st]
  ring
private lemma ae_finite_band_pieces [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) {s t : ℝ} :
    ∀ᵐ ω ∂μ, {k | ∃ n ∈ Finset.range (K k ω),
        X k n ω ∈ Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}}.Finite := by
  have hRmeas : MeasurableSet (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) :=
    measurableSet_Ioc.prod (measurableSet_le measurable_const continuous_abs.measurable)
  have hRfin : (volume.prod ν) (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (hν.measure_setOf_abs_ge_lt_top one_pos)
  have hg1 : Measurable ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hRmeas
  filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hRmeas hRfin] with ω hω
  have hcount : ∑' k, ∑ n ∈ Finset.range (K k ω),
        (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)
      = poissonRandomMeasure K X ω (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) := by
    rw [← lintegral_poissonRandomMeasure hg1 ω, lintegral_indicator hRmeas, setLIntegral_one]
  have hCfin : {k | (1 : ℝ≥0∞) ≤ ∑ n ∈ Finset.range (K k ω),
        (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top (by rw [hcount]; exact hω.ne) one_ne_zero
  refine hCfin.subset fun k hk => ?_
  simp only [Set.mem_setOf_eq] at hk ⊢
  obtain ⟨n, hn, hmem⟩ := hk
  calc (1 : ℝ≥0∞)
      = (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω) := by
        rw [Set.indicator_of_mem hmem]
    _ ≤ _ := Finset.single_le_sum
        (f := fun n => (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
          (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)) (fun _ _ => zero_le) hn
private lemma local_bandToReal [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) :
    (fun ω => levyLargeJumpSum K X t ω - levyLargeJumpSum K X s ω) =ᵐ[μ] fun ω =>
      (∫⁻ p, (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun q => ENNReal.ofReal q.2) p ∂(poissonRandomMeasure K X ω)).toReal
      - (∫⁻ p, (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun q => ENNReal.ofReal (-q.2)) p ∂(poissonRandomMeasure K X ω)).toReal := by
  -- the per-point real/ENNReal split of the band jump size
  have hpt : ∀ p : ℝ × ℝ,
      (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun q : ℝ × ℝ => q.2) p
        = ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
            (fun q : ℝ × ℝ => ENNReal.ofReal q.2) p).toReal
          - ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
            (fun q : ℝ × ℝ => ENNReal.ofReal (-q.2)) p).toReal := by
    intro p
    by_cases hp : p ∈ Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}
    · simp only [Set.indicator_of_mem hp]
      rcases le_total 0 p.2 with h | h
      · rw [ENNReal.toReal_ofReal h, ENNReal.ofReal_of_nonpos (by linarith), ENNReal.toReal_zero,
          sub_zero]
      · rw [ENNReal.ofReal_of_nonpos h, ENNReal.toReal_zero, ENNReal.toReal_ofReal (by linarith),
          zero_sub, neg_neg]
    · simp only [Set.indicator_of_notMem hp, ENNReal.toReal_zero, sub_zero]
  have hposFin : ∀ p : ℝ × ℝ, (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
      (fun q : ℝ × ℝ => ENNReal.ofReal q.2) p ≠ ⊤ := by
    intro p
    by_cases hp : p ∈ Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}
    · rw [Set.indicator_of_mem hp]; exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem hp]; exact ENNReal.zero_ne_top
  have hnegFin : ∀ p : ℝ × ℝ, (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
      (fun q : ℝ × ℝ => ENNReal.ofReal (-q.2)) p ≠ ⊤ := by
    intro p
    by_cases hp : p ∈ Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}
    · rw [Set.indicator_of_mem hp]; exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem hp]; exact ENNReal.zero_ne_top
  have hposMeas : Measurable ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
      fun q : ℝ × ℝ => ENNReal.ofReal q.2) :=
    measurable_snd.ennreal_ofReal.indicator
      (measurableSet_Ioc.prod (measurableSet_le measurable_const continuous_abs.measurable))
  have hnegMeas : Measurable ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
      fun q : ℝ × ℝ => ENNReal.ofReal (-q.2)) :=
    measurable_snd.neg.ennreal_ofReal.indicator
      (measurableSet_Ioc.prod (measurableSet_le measurable_const continuous_abs.measurable))
  filter_upwards [local_bandSumAeEq hd hν h0 hst, ae_finite_band_pieces hd hν (s := s) (t := t)]
    with ω hg hfin
  rw [hg]
  -- convert the three quantities to finite sums over the realized band pieces
  rw [lintegral_poissonRandomMeasure hposMeas ω, lintegral_poissonRandomMeasure hnegMeas ω]
  -- localize to the finite set of contributing pieces
  set S := hfin.toFinset with hSdef
  have hzero_off : ∀ {β : Type} [AddCommMonoid β] (F : ℝ × ℝ → β), ∀ k ∉ S,
      ∑ n ∈ Finset.range (K k ω),
        (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator F (X k n ω) = 0 := by
    intro β _ F k hk
    refine Finset.sum_eq_zero fun n hn => ?_
    apply Set.indicator_of_notMem
    intro hmem
    exact hk (hfin.mem_toFinset.mpr ⟨n, hn, hmem⟩)
  have hposTsum : ∑' k, ∑ n ∈ Finset.range (K k ω),
        (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.2)
          (X k n ω)
      = ∑ k ∈ S, ∑ n ∈ Finset.range (K k ω),
        (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.2)
          (X k n ω) :=
    tsum_eq_sum (hzero_off _)
  have hnegTsum : ∑' k, ∑ n ∈ Finset.range (K k ω),
        (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun q : ℝ × ℝ => ENNReal.ofReal (-q.2))
          (X k n ω)
      = ∑ k ∈ S, ∑ n ∈ Finset.range (K k ω),
        (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun q : ℝ × ℝ => ENNReal.ofReal (-q.2))
          (X k n ω) :=
    tsum_eq_sum (hzero_off _)
  rw [hposTsum, hnegTsum,
    ENNReal.toReal_sum (fun k _ => (ENNReal.sum_lt_top.mpr fun n _ => (hposFin _).lt_top).ne),
    ENNReal.toReal_sum (fun k _ => (ENNReal.sum_lt_top.mpr fun n _ => (hnegFin _).lt_top).ne),
    ← Finset.sum_sub_distrib]
  -- the large-jump sum, as a tsum of piece sums, localizes to the same finite set
  simp only [pieceSum]
  rw [tsum_eq_sum (s := S) (hzero_off _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.toReal_sum (fun n _ => hposFin _),
    ENNReal.toReal_sum (fun n _ => hnegFin _), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => hpt (X k n ω)
private lemma local_strongLarge [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) :
    AEStronglyMeasurable[prmEvalSigma K X ((volume : Measure ℝ).prod ν)
        (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|})]
      (fun ω => levyLargeJumpSum K X t ω - levyLargeJumpSum K X s ω) μ := by
  have hRmeas : MeasurableSet (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) :=
    measurableSet_Ioc.prod (measurableSet_le measurable_const continuous_abs.measurable)
  have hRfin : (volume.prod ν) (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (hν.measure_setOf_abs_ge_lt_top one_pos)
  have hmeas_pos : Measurable[prmEvalSigma K X (volume.prod ν)
      (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|})]
      fun ω => (∫⁻ p, (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun q : ℝ × ℝ => ENNReal.ofReal q.2) p ∂(poissonRandomMeasure K X ω)).toReal :=
    (measurable_lintegral_poissonRandomMeasure_prmEvalSigma hRmeas hRfin
      (measurable_snd.ennreal_ofReal.indicator hRmeas)
      (fun _ hx => Set.indicator_of_notMem hx _)).ennreal_toReal
  have hmeas_neg : Measurable[prmEvalSigma K X (volume.prod ν)
      (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|})]
      fun ω => (∫⁻ p, (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun q : ℝ × ℝ => ENNReal.ofReal (-q.2)) p ∂(poissonRandomMeasure K X ω)).toReal :=
    (measurable_lintegral_poissonRandomMeasure_prmEvalSigma hRmeas hRfin
      (measurable_snd.neg.ennreal_ofReal.indicator hRmeas)
      (fun _ hx => Set.indicator_of_notMem hx _)).ennreal_toReal
  exact ⟨_, (hmeas_pos.sub hmeas_neg).stronglyMeasurable,
    local_bandToReal hd hν h0 hst⟩
private lemma local_smallJumpBandFun_toLp_ae_zero_off (hν : IsLevyMeasure ν) {s t : ℝ} {A : Set ℝ}
    (hA : Set.Ioc s t ⊆ A) :
    ∀ᵐ p ∂((volume : Measure ℝ).prod ν), p ∉ A ×ˢ (Set.univ : Set ℝ) →
      (memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1) 1).indicator fun q : ℝ × ℝ => q.2) p = 0 := by
  filter_upwards [MemLp.coeFn_toLp (memLp_two_smallJumpBandFun hν s t)] with p hp hpA
  rw [hp]
  apply Set.indicator_of_notMem
  intro hmem
  exact hpA ⟨hA hmem.1, Set.mem_univ _⟩

private lemma local_smallStrong [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (s t : ℝ) :
    AEStronglyMeasurable[prmEvalSigma K X (volume.prod ν) (Set.Ioc s t ×ˢ Set.univ)]
      (compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp _)) μ :=
  aestronglyMeasurable_compensatedPoissonIntegral_prmEvalSigma hd
    (measurableSet_Ioc.prod MeasurableSet.univ)
    (local_smallJumpBandFun_toLp_ae_zero_off hν (subset_refl _))


private lemma local_charFunLargeSub [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => levyLargeJumpSum K X t ω - levyLargeJumpSum K X s ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) *
          ∫ x in {x : ℝ | 1 ≤ |x|}, (Complex.exp (x * ξ * Complex.I) - 1) ∂ν) := by
  rw [Measure.map_congr (local_bandSumAeEq hd hν h0 hst)]
  exact charFun_map_bandJumpSum hd hν hst ξ

private lemma local_charFunSmallSub [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => levyCompensatedSmallJump hd hν t ω
        - levyCompensatedSmallJump hd hν s ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) * ∫ x in Set.Ioo (-1) 1,
          (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν) := by
  have hmap : (fun ω => levyCompensatedSmallJump hd hν t ω - levyCompensatedSmallJump hd hν s ω)
      =ᵐ[μ] fun ω => (compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
        ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))) ω := by
    have hsub : levyCompensatedSmallJump hd hν t - levyCompensatedSmallJump hd hν s
        = compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
            ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2)) :=
      levyCompensatedSmallJump_sub hd hν h0 hst
    filter_upwards [Lp.coeFn_sub (levyCompensatedSmallJump hd hν t)
      (levyCompensatedSmallJump hd hν s)] with ω hω
    rw [Pi.sub_apply] at hω
    rw [← hω, hsub]
  rw [Measure.map_congr hmap]
  exact charFun_map_smallJumpBandIntegral hd hν hst ξ

end ProbabilityTheory
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) {s t : ℝ≥0} (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => levyJumpProcess hd hν b t ω - levyJumpProcess hd hν b s ω)) ξ
      = Complex.exp ((((t : ℝ) - (s : ℝ) : ℝ) : ℂ)
          * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by
  set sR := (s : ℝ) with hsRdef
  set tR := (t : ℝ) with htRdef
  have h0 : (0 : ℝ) ≤ sR := s.coe_nonneg
  have hstR : sR ≤ tR := by exact_mod_cast hst
  -- the two banded increments
  set L := fun ω => levyLargeJumpSum K X tR ω - levyLargeJumpSum K X sR ω with hLdef
  set S := fun ω => levyCompensatedSmallJump hd hν tR ω - levyCompensatedSmallJump hd hν sR ω
    with hSdef
  have hLmeas : Measurable L :=
    (measurable_levyLargeJumpSum hd.measurable_count hd.measurable_point).sub
      (measurable_levyLargeJumpSum hd.measurable_count hd.measurable_point)
  have hSmeas : AEMeasurable S μ :=
    ((Lp.aestronglyMeasurable _).aemeasurable).sub ((Lp.aestronglyMeasurable _).aemeasurable)
  have hcont : Continuous fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I) := by fun_prop
  -- The small increment agrees a.e. with the compensated band integral over `(s, t] × (-1, 1)`.
  have hSmap : S =ᵐ[μ] ⇑(compensatedPoissonIntegral hd
      ((memLp_two_smallJumpBandFun hν sR tR).toLp
        ((Set.Ioc sR tR ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))) := by
    have hsub := levyCompensatedSmallJump_sub hd hν h0 hstR
    filter_upwards [Lp.coeFn_sub (levyCompensatedSmallJump hd hν tR)
      (levyCompensatedSmallJump hd hν sR)] with ω hω
    rw [Pi.sub_apply] at hω
    show levyCompensatedSmallJump hd hν tR ω - levyCompensatedSmallJump hd hν sR ω = _
    rw [← hω, hsub]
  -- Independence factorizes the characteristic function of the sum of the two increments.
  have hLS : charFun (μ.map (fun ω => L ω + S ω)) ξ
      = charFun (μ.map L) ξ * charFun (μ.map S) ξ := by
    -- disjoint mark bands over the `(s, t]` time band
    have hmark : Disjoint {x : ℝ | 1 ≤ |x|} (Set.Ioo (-1 : ℝ) 1) := by
      rw [Set.disjoint_left]
      intro x hx hx2
      rw [Set.mem_Ioo] at hx2
      exact absurd (abs_lt.mpr hx2) (not_lt.mpr hx)
    have hdisj : Disjoint (Set.Ioc sR tR ×ˢ {x : ℝ | 1 ≤ |x|})
        (Set.Ioc sR tR ×ˢ Set.Ioo (-1 : ℝ) 1) :=
      Set.Disjoint.set_prod_right hmark _ _
    have hindepSig := indep_prmEvalSigma hd hdisj
    -- honest region-adapted representatives of the two banded increments
    obtain ⟨Wlarge, hWlarge_sm, hWlarge_ae⟩ :=
      local_strongLarge hd hν h0 hstR
    have hf : ∀ᵐ p ∂((volume : Measure ℝ).prod ν),
        p ∉ Set.Ioc sR tR ×ˢ Set.Ioo (-1 : ℝ) 1 →
        (memLp_two_smallJumpBandFun hν sR tR).toLp
            ((Set.Ioc sR tR ×ˢ Set.Ioo (-1) 1).indicator fun q : ℝ × ℝ => q.2) p = 0 := by
      filter_upwards [MemLp.coeFn_toLp (memLp_two_smallJumpBandFun hν sR tR)] with p hp hpR
      rw [hp]
      exact Set.indicator_of_notMem hpR _
    obtain ⟨Wsmall, hWsmall_sm, hWsmall_ae⟩ :
        AEStronglyMeasurable[prmEvalSigma K X (volume.prod ν)
          (Set.Ioc sR tR ×ˢ Set.Ioo (-1 : ℝ) 1)] S μ :=
      (aestronglyMeasurable_compensatedPoissonIntegral_prmEvalSigma hd
        (measurableSet_Ioc.prod measurableSet_Ioo) hf).congr hSmap.symm
    have hindepW : IndepFun Wlarge Wsmall μ := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le hindepSig hWlarge_sm.measurable.comap_le
        hWsmall_sm.measurable.comap_le
    have hindep : IndepFun L S μ := hindepW.congr hWlarge_ae.symm hWsmall_ae.symm
    have h := hindep.charFun_map_fun_add_eq_mul hLmeas.aemeasurable hSmeas
    simpa [Pi.mul_apply] using congrFun h ξ
  -- Rewrite the increment as drift plus the sum of the two banded jump increments.
  have hmap_eq : (fun ω => levyJumpProcess hd hν b t ω - levyJumpProcess hd hν b s ω)
      = fun ω => b * (tR - sR) + (L ω + S ω) := by
    funext ω; simp only [levyJumpProcess, hLdef, hSdef, htRdef, hsRdef]; ring
  rw [hmap_eq]
  have hgae : AEMeasurable (fun ω => b * (tR - sR) + (L ω + S ω)) μ :=
    aemeasurable_const.add (hLmeas.aemeasurable.add hSmeas)
  rw [charFun_apply_real, integral_map hgae hcont.aestronglyMeasurable]
  -- Peel the drift exponential off the integrand.
  have hpeel : ∀ ω, Complex.exp (↑ξ * ↑(b * (tR - sR) + (L ω + S ω)) * Complex.I)
      = Complex.exp (↑ξ * ↑(b * (tR - sR)) * Complex.I)
        * Complex.exp (↑ξ * ↑(L ω + S ω) * Complex.I) := by
    intro ω; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [hpeel]
  rw [integral_const_mul]
  rw [show (∫ ω, Complex.exp (↑ξ * ↑(L ω + S ω) * Complex.I) ∂μ)
        = charFun (μ.map (fun ω => L ω + S ω)) ξ from by
      rw [charFun_apply_real, integral_map
        (show AEMeasurable (fun ω => L ω + S ω) μ from hLmeas.aemeasurable.add hSmeas)
        hcont.aestronglyMeasurable]]
  rw [hLS]
  rw [show charFun (μ.map L) ξ
        = Complex.exp (((tR - sR : ℝ) : ℂ) *
            ∫ x in {x : ℝ | 1 ≤ |x|}, (Complex.exp (x * ξ * Complex.I) - 1) ∂ν) from
      local_charFunLargeSub hd hν h0 hstR ξ]
  rw [show charFun (μ.map S) ξ
        = Complex.exp (((tR - sR : ℝ) : ℂ) * ∫ x in Set.Ioo (-1) 1,
            (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν) from
      local_charFunSmallSub hd hν h0 hstR ξ]
  -- Combine the three exponentials and match the exponent via the radius-1 split.
  rw [← Complex.exp_add, ← Complex.exp_add, LevyKhintchineTriple.exponent,
    integral_levyCompensatedIntegrand_eq_small_add_large hν ξ]
  congr 1
  push_cast
  ring
