-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P22.cdNorm_formula
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T21:19:24.467844+00:00
-- url     : https://prove2.me/submissions/1c642077-73c5-4ce9-a8f6-23f10f8b7376

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P22
set_option autoImplicit false
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Intakethird100.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel correlationMixture prBox)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Gap48.P25 (classicalMI)

private lemma le_finiteMax' {I : Type} [Fintype I] [Nonempty I] (f : I → ℝ) (i : I) :
    f i ≤ finiteMax f :=
  le_csSup (Set.finite_range f).bddAbove ⟨i, rfl⟩

private lemma finiteMax_eq' {I : Type} [Fintype I] [Nonempty I] (f : I → ℝ) :
    ∃ i, finiteMax f = f i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨i, le_antisymm ?_ (le_finiteMax' f i)⟩
  apply csSup_le (Set.range_nonempty f)
  rintro _ ⟨j, rfl⟩
  exact hi j (Finset.mem_univ j)

private lemma apply_sub' {C E Z : Type} [Fintype C] [Fintype E] [Fintype Z]
    (g : CDObservation C E Z) (p q : CDArray C E Z) (j : Fin g.size) :
    g.apply p j - g.apply q j =
      ∑ c, ∑ z, ∑ e, g.input c z * (p z c e - q z c e) * g.output c z e j := by
  simp only [CDObservation.apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun z _ =>
    Finset.sum_congr rfl fun e _ => by ring

private lemma upper' {C E Z : Type} [Fintype C] [Fintype E] [Fintype Z] [Nonempty Z]
    (g : CDObservation C E Z) (p q : CDArray C E Z) :
    ∑ j, |g.apply p j - g.apply q j| ≤
      ∑ c, finiteMax (fun z => ∑ e, |p z c e - q z c e|) := by
  calc ∑ j, |g.apply p j - g.apply q j|
      ≤ ∑ j, ∑ c, ∑ z, ∑ e, g.input c z * |p z c e - q z c e| * g.output c z e j := by
        apply Finset.sum_le_sum; intro j _
        rw [apply_sub']
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg ((g.input_law c).1 z),
          abs_of_nonneg ((g.output_law c z e).1 j)]
    _ = ∑ c, ∑ z, g.input c z * ∑ e, |p z c e - q z c e| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← Finset.mul_sum, (g.output_law c z e).2, mul_one]
    _ ≤ ∑ c, ∑ z, g.input c z * finiteMax (fun z => ∑ e, |p z c e - q z c e|) := by
        refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun z _ => ?_
        exact mul_le_mul_of_nonneg_left
          (le_finiteMax' (fun z => ∑ e, |p z c e - q z c e|) z) ((g.input_law c).1 z)
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_mul, (g.input_law c).2, one_mul]

theorem solution {C E Z : Type}
    [Fintype C] [Fintype E] [Fintype Z] [Nonempty C] [Nonempty E] [Nonempty Z]
    (p q : CDArray C E Z) (hp : IsCD p) (hq : IsCD q) :
    cdDistance p q = (1 / 2 : ℝ) * ∑ c, finiteMax (fun z => ∑ e, |p z c e - q z c e|) := by
  have hzs : ∀ c, ∃ z, finiteMax (fun z => ∑ e, |p z c e - q z c e|) =
      ∑ e, |p z c e - q z c e| := fun c => finiteMax_eq' _
  choose zs hzs using hzs
  let g : CDObservation C E Z :=
    { size := 2
      positive := by norm_num
      input := fun c z => if z = zs c then 1 else 0
      input_law := fun c => ⟨fun z => by
        show 0 ≤ (if z = zs c then (1 : ℝ) else 0)
        split_ifs <;> norm_num, by simp⟩
      output := fun c z e => if 0 < p z c e - q z c e then ![1, 0] else ![0, 1]
      output_law := fun c z e => ⟨fun j => by split_ifs <;> fin_cases j <;> simp,
        by split_ifs <;> simp [Fin.sum_univ_two]⟩ }
  have hA : g.apply p 0 - g.apply q 0 = ∑ c, ∑ e,
      (p (zs c) c e - q (zs c) c e) * (if 0 < p (zs c) c e - q (zs c) c e then 1 else 0) := by
    rw [apply_sub']
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [g, ite_mul, Finset.sum_ite_eq', apply_ite]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  have hB : g.apply p 1 - g.apply q 1 = ∑ c, ∑ e,
      (p (zs c) c e - q (zs c) c e) * (if 0 < p (zs c) c e - q (zs c) c e then 0 else 1) := by
    rw [apply_sub']
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [g, ite_mul, Finset.sum_ite_eq', apply_ite]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  have hval : ∑ j, |g.apply p j - g.apply q j| =
      ∑ c, finiteMax (fun z => ∑ e, |p z c e - q z c e|) := by
    change ∑ j : Fin 2, |g.apply p j - g.apply q j| = _
    rw [Fin.sum_univ_two, hA, hB]
    rw [abs_of_nonneg, abs_of_nonpos, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [hzs, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs with h
      · rw [abs_of_pos h]; ring
      · rw [abs_of_nonpos (not_lt.mp h)]; ring
    · refine Finset.sum_nonpos fun c _ => Finset.sum_nonpos fun e _ => ?_
      split_ifs with h
      · simp
      · simpa using not_lt.mp h
    · refine Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun e _ => ?_
      split_ifs with h
      · simpa using h.le
      · simp
  unfold cdDistance
  apply le_antisymm
  · refine csSup_le ⟨_, g, rfl⟩ ?_
    rintro _ ⟨g', rfl⟩
    exact mul_le_mul_of_nonneg_left (upper' g' p q) (by norm_num)
  · apply le_csSup
    · refine ⟨(1 / 2 : ℝ) * ∑ c, finiteMax (fun z => ∑ e, |p z c e - q z c e|), ?_⟩
      rintro _ ⟨g', rfl⟩
      exact mul_le_mul_of_nonneg_left (upper' g' p q) (by norm_num)
    · exact ⟨g, by rw [hval]⟩

end
