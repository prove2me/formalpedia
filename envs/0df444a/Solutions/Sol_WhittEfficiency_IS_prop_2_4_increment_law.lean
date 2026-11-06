-- Prove2me | solution 1 for WhittEfficiency.IS.prop_2_4_increment_law
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:34:04.074206+00:00
-- url     : https://prove2.me/submissions/60d56677-c472-406d-a43e-7a5581dd4344

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model
import Theorems.Thm_WhittEfficiency_IS_sec_2_5_split
import Theorems.Thm_QueueingFundamentals_Foundations_poisson_count_cdf

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace WhittIncLawAux

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


theorem iIndepFun_const_family {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    iIndepFun (fun (_ : ℕ) (_ : Ω) => (0 : Fin 1)) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases h : ∀ i ∈ S, (0 : Fin 1) ∈ sets i
  · have e1 : (⋂ i ∈ S, (fun (_ : Ω) => (0 : Fin 1)) ⁻¹' sets i) = Set.univ := by
      ext ω; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]; exact h
    rw [e1, measure_univ]
    symm
    apply Finset.prod_eq_one
    intro i hi
    have : (fun (_ : Ω) => (0 : Fin 1)) ⁻¹' sets i = Set.univ := by
      ext ω; simp [h i hi]
    rw [this, measure_univ]
  · push_neg at h
    obtain ⟨i, hi, hni⟩ := h
    have e0 : (fun (_ : Ω) => (0 : Fin 1)) ⁻¹' sets i = ∅ := by
      ext ω; simp [hni]
    have e1 : (⋂ j ∈ S, (fun (_ : Ω) => (0 : Fin 1)) ⁻¹' sets j) = ∅ := by
      apply Set.subset_empty_iff.mp
      intro ω hω
      simp only [Set.mem_iInter] at hω
      have := hω i hi
      rw [e0] at this
      exact this
    rw [e1, measure_empty]
    symm
    exact Finset.prod_eq_zero hi (by rw [e0, measure_empty])

end WhittIncLawAux

open WhittIncLawAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    (hT : IsExpInterarrivals μ lam T) (t : ℝ) (ht : 1 ≤ t) :
    ∀ k : ℕ, μ.real {ω | countingProcess T t ω = countingProcess T (t - 1) ω + k} =
      μ.real {ω | countingProcess T 1 ω = k} := by
  intro k
  set J : ℕ → Ω → Fin 1 := fun _ _ => 0 with hJ
  have hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T (fun _ => (1 : ℝ)) J :=
    { arrivals := hT
      label_measurable := fun _ => measurable_const
      label_indep := iIndepFun_const_family μ
      label_law := fun k i => by
        have : {ω : Ω | J k ω = i} = Set.univ := by
          ext ω; simp [hJ, Fin.fin_one_eq_zero i]
        rw [this, probReal_univ]
      indep := indepFun_const_right (fun ω k => T k ω) (fun (_ : ℕ) => (0 : Fin 1)) }
  have hsplit := (WhittEfficiency.IS.sec_2_5_split μ lam hlam T (fun _ => (1 : ℝ)) J hM
    (fun _ => t - 1) (fun _ => t) (fun _ => ⟨by linarith, by linarith⟩)).2 0 k
  have hcongr : μ.real {ω | countingProcess T t ω = countingProcess T (t - 1) ω + k} =
      μ.real {ω | WhittEfficiency.IS.classWindowCount T J 0 (t - 1) t ω = k} := by
    apply measureReal_congr
    filter_upwards [ae_finite_arrivals μ lam hlam T hT t] with ω hfin
    change (countingProcess T t ω = countingProcess T (t - 1) ω + k) =
      (WhittEfficiency.IS.classWindowCount T J 0 (t - 1) t ω = k)
    have hfinN : {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t}.Finite := by
      apply (hfin.image (fun k => k + 1)).subset
      rintro n ⟨hn1, hn2⟩
      refine ⟨n - 1, ?_, by simp only; omega⟩
      simp only [Set.mem_ofPred_eq]
      rwa [Nat.sub_add_cancel hn1]
    have hsplitset : {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t} =
        {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t - 1} ∪
          {n : ℕ | 1 ≤ n ∧ t - 1 < arrivalTime T n ω ∧ arrivalTime T n ω ≤ t} := by
      ext n
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h3 : arrivalTime T n ω ≤ t - 1
        · exact Or.inl ⟨h1, h3⟩
        · exact Or.inr ⟨h1, by linarith, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
        · exact ⟨h1, by linarith⟩
        · exact ⟨h1, h3⟩
    have hdisj : Disjoint {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t - 1}
        {n : ℕ | 1 ≤ n ∧ t - 1 < arrivalTime T n ω ∧ arrivalTime T n ω ≤ t} := by
      rw [Set.disjoint_left]
      rintro n ⟨_, h2⟩ ⟨_, h3, _⟩
      linarith
    have hwin : WhittEfficiency.IS.classWindowCount T J 0 (t - 1) t ω =
        {n : ℕ | 1 ≤ n ∧ t - 1 < arrivalTime T n ω ∧ arrivalTime T n ω ≤ t}.ncard := by
      unfold WhittEfficiency.IS.classWindowCount
      have : {n : ℕ | 1 ≤ n ∧ t - 1 < arrivalTime T n ω ∧ arrivalTime T n ω ≤ t} =
          (fun k => k + 1) '' {k : ℕ | J k ω = 0 ∧ t - 1 < arrivalTime T (k + 1) ω ∧
            arrivalTime T (k + 1) ω ≤ t} := by
        ext n
        simp only [Set.mem_ofPred_eq, Set.mem_image, hJ, true_and]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨n - 1, ?_, by omega⟩
          rw [Nat.sub_add_cancel h1]
          exact ⟨h2, h3⟩
        · rintro ⟨k, ⟨h2, h3⟩, rfl⟩
          exact ⟨by omega, h2, h3⟩
      rw [this, Set.ncard_image_of_injective _ (fun a b h => by simpa using h)]
    have hcount : countingProcess T t ω = countingProcess T (t - 1) ω +
        WhittEfficiency.IS.classWindowCount T J 0 (t - 1) t ω := by
      rw [hwin]
      unfold countingProcess
      rw [hsplitset]
      exact Set.ncard_union_eq hdisj (hfinN.subset (by
          rw [hsplitset]; exact Set.subset_union_left))
        (hfinN.subset (by rw [hsplitset]; exact Set.subset_union_right))
    apply propext
    rw [hcount]
    omega
  rw [hcongr, hsplit]
  have h := (poisson_count_cdf μ lam hlam T hT k 1 zero_le_one).2.2
  rw [measureReal_def, h]
  simp only [mul_one]
  ring_nf
