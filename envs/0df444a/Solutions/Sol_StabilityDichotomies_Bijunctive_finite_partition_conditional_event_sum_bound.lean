-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.finite_partition_conditional_event_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:10:34.684692+00:00
-- url     : https://prove2.me/submissions/e8e300a6-3bcd-4922-9d6a-e5d362f5d303

import Mathlib
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem solution
    {Ω ι τ : Type} [MeasurableSpace Ω] [Fintype ι] [Fintype τ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ι → Set Ω) (E : τ → Set Ω) (B : ℝ)
    (hP : ∀ i, MeasurableSet (P i)) (hE : ∀ j, MeasurableSet (E j))
    (hdis : Pairwise (Disjoint on P)) (hcover : (⋃ i, P i) = Set.univ)
    (hB : 0 ≤ B)
    (hcond : ∀ i, μ (P i) ≠ 0 → ∑ j, (ProbabilityTheory.cond μ (P i)).real (E j) ≤ B) :
    (∑ j, μ.real (E j)) ≤ B := by
  classical
  have hpiece (i : ι) (j : τ) : μ.real (E j ∩ P i) =
      μ.real (P i) * (ProbabilityTheory.cond μ (P i)).real (E j) := by
    by_cases hzero : μ (P i) = 0
    · have he : μ (E j ∩ P i) = 0 := by
        apply le_antisymm _ bot_le
        exact (measure_mono Set.inter_subset_right).trans_eq hzero
      simp [Measure.real,he,hzero]
    · have hreal : μ.real (P i) ≠ 0 := by
        exact (measureReal_ne_zero_iff (measure_ne_top μ _)).mpr hzero
      have hh : (ProbabilityTheory.cond μ (P i)).real (E j) =
          (μ.real (P i))⁻¹ * μ.real (E j ∩ P i) := by
        unfold Measure.real
        rw [ProbabilityTheory.cond_apply (hP i), ENNReal.toReal_mul, ENNReal.toReal_inv]
        congr 1
        rw [Set.inter_comm]
      rw [hh]
      field_simp
  have hmass : (∑ i, μ.real (P i)) = 1 := by
    have h := measureReal_iUnion_fintype (μ := μ) hdis hP
    rw [hcover] at h
    simpa [Measure.real] using h.symm
  have hdecomp (j : τ) : μ.real (E j) = ∑ i, μ.real (E j ∩ P i) := by
    have heq : E j = ⋃ i, E j ∩ P i := by
      ext x
      simp only [mem_iUnion,mem_inter_iff]
      constructor
      · intro hx
        have : x ∈ ⋃ i, P i := by rw [hcover]; trivial
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp this
        exact ⟨i,hx,hi⟩
      · rintro ⟨i,hx,_⟩
        exact hx
    nth_rewrite 1 [heq]
    apply measureReal_iUnion_fintype
    · intro a b hab
      exact (hdis hab).mono Set.inter_subset_right Set.inter_subset_right
    · intro i
      exact (hE j).inter (hP i)
    · intro i
      exact measure_ne_top μ _
  calc
    (∑ j, μ.real (E j)) = ∑ j, ∑ i, μ.real (P i) * (ProbabilityTheory.cond μ (P i)).real (E j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hdecomp j]
      apply Finset.sum_congr rfl
      intro i hi
      exact hpiece i j
    _ = ∑ i, μ.real (P i) * ∑ j, (ProbabilityTheory.cond μ (P i)).real (E j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ ≤ ∑ i, μ.real (P i) * B := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hzero : μ (P i) = 0
      · simp [Measure.real,hzero]
      · exact mul_le_mul_of_nonneg_left (hcond i hzero) measureReal_nonneg
    _ = B := by rw [← Finset.sum_mul, hmass, one_mul]
