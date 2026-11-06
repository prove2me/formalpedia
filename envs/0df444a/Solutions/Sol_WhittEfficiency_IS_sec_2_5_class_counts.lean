-- Prove2me | solution 1 for WhittEfficiency.IS.sec_2_5_class_counts
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:28:53.499191+00:00
-- url     : https://prove2.me/submissions/e7206398-555c-4667-a6de-11536986d953

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model
import Theorems.Thm_WhittEfficiency_IS_sec_2_5_split

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace WhittClassCountsAux

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

end WhittClassCountsAux

open WhittClassCountsAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    {m : ℕ} (p d : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i) (J : ℕ → Ω → Fin m)
    (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J)
    (t : ℝ) (ht : ∀ i, d i < t) :
    iIndepFun (fun i ω => WhittEfficiency.IS.classBusyCount T J d i t ω) μ ∧
    (∀ (i : Fin m) (k : ℕ), μ.real {ω | WhittEfficiency.IS.classBusyCount T J d i t ω = k} =
      Real.exp (-(lam * p i * d i)) * (lam * p i * d i) ^ k / k.factorial) ∧
    ∀ᵐ ω ∂μ, WhittEfficiency.IS.busyCount T (fun j ω => d (J j ω)) t ω =
      ∑ i, WhittEfficiency.IS.classBusyCount T J d i t ω := by
  have hab : ∀ i, 0 ≤ t - d i ∧ t - d i ≤ t := fun i =>
    ⟨by linarith [ht i], by linarith [hd i]⟩
  obtain ⟨hind, hlaw⟩ :=
    WhittEfficiency.IS.sec_2_5_split μ lam hlam T p J hM (fun i => t - d i) (fun _ => t) hab
  have hEq : (fun i ω => WhittEfficiency.IS.classBusyCount T J d i t ω) =
      (fun i ω => WhittEfficiency.IS.classWindowCount T J i (t - d i) t ω) := by
    funext i ω
    unfold WhittEfficiency.IS.classBusyCount WhittEfficiency.IS.classWindowCount
    congr 1
    ext k
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, h2⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hEq]; exact hind
  · intro i k
    have h := hlaw i k
    have e : WhittEfficiency.IS.classBusyCount T J d i t =
        fun ω => WhittEfficiency.IS.classWindowCount T J i (t - d i) t ω := congrFun hEq i
    simp only [e]
    rw [h]
    ring_nf
  · filter_upwards [ae_finite_arrivals μ lam hlam T hM.arrivals t] with ω hfin
    set S0 := hfin.toFinset with hS0
    have key : ∀ (P : ℕ → Prop) [DecidablePred P],
        (∀ k, P k → arrivalTime T (k + 1) ω ≤ t) →
        {k : ℕ | P k}.ncard = (S0.filter P).card := by
      intro P _ hP
      have : {k : ℕ | P k} = ((S0.filter P : Finset ℕ) : Set ℕ) := by
        ext k
        simp only [Set.mem_ofPred_eq, Finset.coe_filter, hS0, Set.Finite.mem_toFinset]
        exact ⟨fun h => ⟨hP k h, h⟩, fun h => h.2⟩
      rw [this, Set.ncard_coe_finset]
    classical
    unfold WhittEfficiency.IS.busyCount WhittEfficiency.IS.classBusyCount
    rw [key _ (fun k hk => hk.1)]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun k => J k ω) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key (fun k => J k ω = i ∧ arrivalTime T (k + 1) ω ≤ t ∧
      t < arrivalTime T (k + 1) ω + d i) (fun k hk => hk.2.1)]
    congr 1
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hk, h1, h2⟩, h3⟩
      subst h3
      exact ⟨hk, rfl, h1, h2⟩
    · rintro ⟨hk, h3, h1, h2⟩
      subst h3
      exact ⟨⟨hk, h1, h2⟩, rfl⟩
