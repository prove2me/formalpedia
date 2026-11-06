-- Prove2me | solution 1 for WhittEfficiency.IS.proposition_2_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:32:53.769062+00:00
-- url     : https://prove2.me/submissions/7a28ee1d-656d-4bf0-94c0-160087233b56

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model
import Theorems.Thm_WhittEfficiency_IS_proposition_2_3
import Theorems.Thm_WhittEfficiency_IS_prop_2_4_increment_law
import Theorems.Thm_QueueingFundamentals_Foundations_poisson_count_cdf

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace WhittProp24Aux

/-- Pathwise: nonnegative interarrival times, infinitely many of which exceed `1`, give only
finitely many arrival epochs in `(-∞, t]`. -/
theorem finite_of_infinite_big {Ω : Type*} (T : ℕ → Ω → ℝ) (ω : Ω) (t : ℝ)
    (hnn : ∀ i, 0 ≤ T i ω) (hinf : {i : ℕ | 1 < T i ω}.Infinite) :
    {k : ℕ | arrivalTime T (k + 1) ω ≤ t}.Finite := by
  obtain ⟨F, hFsub, hFcard⟩ := hinf.exists_subset_card_eq (⌈t⌉₊ + 1)
  have hbound : ∀ n, (∀ i ∈ F, i < n) → t < arrivalTime T n ω := by
    intro n hn
    have hsub : F ⊆ Finset.range n := fun i hi => Finset.mem_range.mpr (hn i hi)
    have h1 : ∑ i ∈ F, T i ω ≤ arrivalTime T n ω := by
      unfold arrivalTime
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnn i)
    have h2 : (F.card : ℝ) ≤ ∑ i ∈ F, T i ω := by
      have : ∑ i ∈ F, (1 : ℝ) ≤ ∑ i ∈ F, T i ω :=
        Finset.sum_le_sum fun i hi => le_of_lt (hFsub hi)
      simpa using this
    have h3 : t < (F.card : ℝ) := by
      rw [hFcard]
      push_cast
      have := Nat.le_ceil t
      linarith
    linarith
  obtain ⟨N, hN⟩ : ∃ N, ∀ i ∈ F, i < N := ⟨F.sup id + 1, fun i hi => by
    have := Finset.le_sup (f := id) hi
    simp at this
    omega⟩
  apply (Set.finite_lt_nat N).subset
  intro k hk
  simp only [Set.mem_ofPred_eq] at hk ⊢
  by_contra hkN
  push_neg at hkN
  have := hbound (k + 1) (fun i hi => by have := hN i hi; omega)
  linarith

/-- Under i.i.d. exponential interarrival times, almost surely only finitely many arrivals occur
by time `t`. -/
theorem ae_finite_arrivals {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    (hT : IsExpInterarrivals μ lam T) (t : ℝ) :
    ∀ᵐ ω ∂μ, {k : ℕ | arrivalTime T (k + 1) ω ≤ t}.Finite := by
  haveI : IsProbabilityMeasure (expMeasure lam) := isProbabilityMeasure_expMeasure hlam
  have hIic : ∀ i x, μ (T i ⁻¹' Set.Iic x) = expMeasure lam (Set.Iic x) := by
    intro i x
    rw [← hT.law i, Measure.map_apply (hT.measurable i) measurableSet_Iic]
  -- nonnegativity
  have hnn : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ T i ω := by
    rw [ae_all_iff]
    intro i
    have h0 : μ (T i ⁻¹' Set.Iic 0) = 0 := by
      rw [hIic]
      have hc := cdf_expMeasure_eq hlam 0
      rw [cdf_eq_real] at hc
      simp at hc
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hc
      rcases hc with hc | hc
      · exact hc
      · exact absurd hc (measure_ne_top _ _)
    rw [ae_iff]
    refine measure_mono_null ?_ h0
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_le] at hω
    simp only [Set.mem_preimage, Set.mem_Iic]
    exact hω.le
  -- infinitely many big interarrival times
  set s : ℕ → Set Ω := fun i => T i ⁻¹' Set.Ioi 1 with hs
  have hsm : ∀ i, MeasurableSet (s i) := fun i => hT.measurable i measurableSet_Ioi
  have hsind : iIndepSet s μ := by
    rw [iIndepSet_iff_meas_biInter hsm]
    intro S
    exact hT.indep.measure_inter_preimage_eq_mul S (fun _ _ => measurableSet_Ioi)
  have hpos : μ (s 0) ≠ 0 := by
    intro h
    have hc := cdf_expMeasure_eq hlam 1
    rw [cdf_eq_real] at hc
    have e1 : (expMeasure lam).real (Set.Iic 1) = 1 := by
      have hcompl : μ (s 0)ᶜ = 1 := by
        rw [prob_compl_eq_one_sub (hsm 0), h, tsub_zero]
      have : (s 0)ᶜ = T 0 ⁻¹' Set.Iic 1 := by
        ext ω; simp [hs]
      rw [this, hIic] at hcompl
      rw [measureReal_def, hcompl]
      simp
    rw [e1] at hc
    simp only [zero_le_one, if_true, mul_one] at hc
    have : Real.exp (-lam) = 0 := by linarith
    exact (Real.exp_pos _).ne' this
  have hsame : ∀ i, μ (s i) = μ (s 0) := by
    intro i
    have h := fun j => (show μ (s j) = expMeasure lam (Set.Ioi 1) by
      rw [← hT.law j, Measure.map_apply (hT.measurable j) measurableSet_Ioi])
    rw [h i, h 0]
  have hsum : (∑' i, μ (s i)) = ⊤ := by
    simp_rw [hsame]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hpos
  have hls := measure_limsup_eq_one hsm hsind hsum
  have hae_ls : ∀ᵐ ω ∂μ, ω ∈ Filter.limsup s Filter.atTop := by
    rw [ae_iff]
    have hmeas : MeasurableSet (Filter.limsup s Filter.atTop) := MeasurableSet.measurableSet_limsup hsm
    exact prob_compl_eq_zero_iff hmeas |>.mpr hls
  filter_upwards [hnn, hae_ls] with ω hω1 hω2
  apply finite_of_infinite_big T ω t hω1
  rw [Filter.mem_limsup_iff_frequently_mem] at hω2
  exact Nat.frequently_atTop_iff_infinite.mp hω2


/-- Under i.i.d. exponential interarrival times, almost surely every interarrival time is
positive. -/
theorem ae_pos {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    (hT : IsExpInterarrivals μ lam T) :
    ∀ᵐ ω ∂μ, ∀ i, 0 < T i ω := by
  haveI : IsProbabilityMeasure (expMeasure lam) := isProbabilityMeasure_expMeasure hlam
  rw [ae_all_iff]
  intro i
  have h0 : μ (T i ⁻¹' Set.Iic 0) = 0 := by
    rw [show μ (T i ⁻¹' Set.Iic 0) = expMeasure lam (Set.Iic 0) by
      rw [← hT.law i, Measure.map_apply (hT.measurable i) measurableSet_Iic]]
    have hc := cdf_expMeasure_eq hlam 0
    rw [cdf_eq_real] at hc
    simp at hc
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hc
    rcases hc with hc | hc
    · exact hc
    · exact absurd hc (measure_ne_top _ _)
  rw [ae_iff]
  refine measure_mono_null ?_ h0
  intro ω hω
  simp only [Set.mem_ofPred_eq, not_lt] at hω
  simp only [Set.mem_preimage, Set.mem_Iic]
  exact hω

end WhittProp24Aux

open WhittProp24Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    (hT : IsExpInterarrivals μ lam T) (t : ℝ) (ht : 1 < t) :
    ∀ k : ℕ, μ.real {ω | WhittEfficiency.IS.busyCount T (fun _ _ => 1) t ω = k} =
      Real.exp (-lam) * lam ^ k / k.factorial := by
  intro k
  have hcongr : μ.real {ω | WhittEfficiency.IS.busyCount T (fun _ _ => 1) t ω = k} =
      μ.real {ω | countingProcess T t ω = countingProcess T (t - 1) ω + k} := by
    apply measureReal_congr
    filter_upwards [ae_pos μ lam hlam T hT, ae_finite_arrivals μ lam hlam T hT t] with ω hpos hfin
    have hfin' : {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t}.Finite := by
      apply (hfin.image (fun k => k + 1)).subset
      rintro n ⟨hn1, hn2⟩
      refine ⟨n - 1, ?_, by simp only; omega⟩
      simp only [Set.mem_ofPred_eq]
      rwa [Nat.sub_add_cancel hn1]
    have h23 := WhittEfficiency.IS.proposition_2_3 T ω t hpos hfin'
    change (WhittEfficiency.IS.busyCount T (fun _ _ => 1) t ω = k) =
      (countingProcess T t ω = countingProcess T (t - 1) ω + k)
    apply propext
    constructor
    · intro h; rw [h] at h23; omega
    · intro h; rw [h] at h23; push_cast at h23; omega
  rw [hcongr, WhittEfficiency.IS.prop_2_4_increment_law μ lam hlam T hT t ht.le k]
  have h := (poisson_count_cdf μ lam hlam T hT k 1 zero_le_one).2.2
  rw [measureReal_def, h]
  simp only [mul_one]
  ring
