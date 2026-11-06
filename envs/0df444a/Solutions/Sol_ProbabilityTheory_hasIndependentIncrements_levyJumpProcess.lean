-- Prove2me | solution 1 for ProbabilityTheory.hasIndependentIncrements_levyJumpProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T03:59:08.698168+00:00
-- url     : https://prove2.me/submissions/0352cc6c-8807-4fd4-84ee-b04e95f0cfa8

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Theorems.Thm_ProbabilityTheory_iIndep_prmEvalSigma
import Theorems.Thm_ProbabilityTheory_increment_apply
import Theorems.Thm_ProbabilityTheory_levyCompensatedSmallJump_sub
import Theorems.Thm_ProbabilityTheory_measurable_lintegral_poissonRandomMeasure_prmEvalSigma
import Theorems.Thm_ProbabilityTheory_lintegral_poissonRandomMeasure
open MeasureTheory ProbabilityTheory Filter
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

end ProbabilityTheory
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) :
    HasIndependentIncrements (levyJumpProcess hd hν b) μ := by
  intro n τ hτmono
  -- the consecutive time bands over the grid, extended over all marks
  set R : Fin n → Set (ℝ × ℝ) :=
    fun k => Set.Ioc ((τ k.castSucc : ℝ)) ((τ k.succ : ℝ)) ×ˢ (Set.univ : Set ℝ) with hRdef
  -- coercion facts: the grid is monotone and nonnegative in ℝ≥0
  have hcoe_le : ∀ k : Fin n, (τ k.castSucc : ℝ) ≤ (τ k.succ : ℝ) := fun k => by
    exact_mod_cast hτmono (Fin.castSucc_le_succ k)
  have hcoe_nonneg : ∀ k : Fin n, (0 : ℝ) ≤ (τ k.castSucc : ℝ) := fun _ => NNReal.coe_nonneg _
  -- the bands are pairwise disjoint
  have hRdisj : Pairwise (Function.onFun Disjoint R) := by
    have hcore : ∀ i j : Fin n, i < j → Disjoint (R i) (R j) := by
      intro i j hij
      refine Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le ?_) _ _
      have hle : i.succ ≤ j.castSucc := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        have : (i : ℕ) < (j : ℕ) := hij
        omega
      exact_mod_cast hτmono hle
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hcore i j h
    · exact (hcore j i h).symm
  -- an honest per-band representative of each increment, measurable in that band's σ-algebra
  have hdata : ∀ k : Fin n, ∃ W : Ω → ℝ,
      Measurable[prmEvalSigma K X (volume.prod ν) (R k)] W ∧
      increment (levyJumpProcess hd hν b) (τ k.castSucc) (τ k.succ) =ᵐ[μ] W := by
    intro k
    obtain ⟨WL, hWL_sm, hWL_ae⟩ :=
      local_strongLarge hd hν (hcoe_nonneg k) (hcoe_le k)
    obtain ⟨WS, hWS_sm, hWS_ae⟩ :=
      local_smallStrong hd hν (τ k.castSucc : ℝ) (τ k.succ : ℝ)
    -- lift the large-jump representative from its `{|x| ≥ 1}` band to the full band `R k`
    have hsub : Set.Ioc ((τ k.castSucc : ℝ)) ((τ k.succ : ℝ)) ×ˢ {x : ℝ | 1 ≤ |x|} ⊆ R k :=
      Set.prod_mono le_rfl (Set.subset_univ _)
    have hWL_sm_R : StronglyMeasurable[prmEvalSigma K X (volume.prod ν) (R k)] WL :=
      hWL_sm.mono (prmEvalSigma_mono hsub)
    refine ⟨fun ω => b * ((τ k.succ : ℝ) - (τ k.castSucc : ℝ)) + WL ω + WS ω,
      ((stronglyMeasurable_const.add hWL_sm_R).add hWS_sm).measurable, ?_⟩
    -- the small increment is the coeFn of the band compensated integral, a.e.
    have hcoeFnSub := Lp.coeFn_sub (levyCompensatedSmallJump hd hν (τ k.succ : ℝ))
      (levyCompensatedSmallJump hd hν (τ k.castSucc : ℝ))
    rw [levyCompensatedSmallJump_sub hd hν (hcoe_nonneg k) (hcoe_le k)] at hcoeFnSub
    filter_upwards [hWL_ae, hWS_ae, hcoeFnSub] with ω hWLω hWSω hsubω
    simp only [Pi.sub_apply] at hsubω
    have hWSeq : WS ω = levyCompensatedSmallJump hd hν (τ k.succ : ℝ) ω
        - levyCompensatedSmallJump hd hν (τ k.castSucc : ℝ) ω := hWSω.symm.trans hsubω
    rw [increment_apply]
    simp only [levyJumpProcess]
    rw [← hWLω, hWSeq]
    ring
  choose W hW_meas hW_ae using hdata
  -- disjoint bands give independent evaluation σ-algebras, hence independent representatives
  have hiIndepW : iIndep (fun k => MeasurableSpace.comap (W k) inferInstance) μ :=
    iIndep_of_iIndep_of_le (iIndep_prmEvalSigma hd hRdisj) (fun k => (hW_meas k).comap_le)
  -- transfer independence from the representatives back to the increments
  exact (iIndepFun_congr fun k => hW_ae k).mpr ((iIndepFun_iff_iIndep _ W μ).mpr hiIndepW)
